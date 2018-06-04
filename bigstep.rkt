; A partial implementation of the big-step semantics in the faceted
; execution paper.
#lang racket

(require rackunit)
(require rackunit/text-ui)

; 
; Terms
; 
(define label? symbol?)
(define var? symbol?)
(define (lit? l) (or (number? l) (boolean? l)))

(define (exp? e) (exp-env? (hash)))

; Check if an expression is well-formed within a specific
; environment. In particular, this checks to ensure that variables are
; not used outside of their lexical scopes.
; 
; @Zhanpeng: if you are confused about what this code is doing, first
; read about "quasipatterns" here:
; https://docs.racket-lang.org/reference/match.html
; 
; @Zhanpeng: Also note that this function has a weird style you
; probably haven't seen before, it's using a curried style. Please
; read about it here:
; https://docs.racket-lang.org/guide/define.html#%28part._.Curried_.Function_.Shorthand%29
; 
; Then feel free to ask me and Tom questions.
(define ((exp-env? env) e)
  (match e
    [(? var? x) (set-member? env x)]
    [(? lit?) #t]
    [`(λ (,(? var? x)) ,e)
     ((exp-env? (set-add env x)) e)]
    [`(ref ,(? (exp-env? env))) #t]
    [`(deref ,(? (exp-env? env))) #t]
    [`(set! ,(? (exp-env? env) e0) ,(? (exp-env? env) e1)) #t]
    [`(,(? (exp-env? env)) ,(? (exp-env? env))) #t]
    [`(let ([,(? var? x) ,(? (exp-env? env) e1)]) ,e2)
     ((exp-env? (set-add env x)) e2)]
    [`(if ,(? (exp-env? env)) ,(? (exp-env? env)) ,(? (exp-env? env))) #t]
    [else (pretty-print `(bad-exp ,e ,env)) #f]))

; 
; Values
; 

; Closures
(struct clo (lam env) #:transparent)

; Addresses
(struct addr (loc))

; Void
(struct void ())

; A contract for values
(define (value? v)
  (match v 
    [number? #t]
    [addr? #t]
    [clo? #t]
    [void? #t]
    [else #f]))

; 
; Environment handling: delegate to Racket's underlying hashes.
;

; Add a new binding to the environment:
; Θ[x ↦ v]
(define (env-set env x v) (hash-set env x v))
; ^^Note: this could also have been written as 
; (define env-set hash-set)

; Lookup a variable from an environment
(define (env-ref env x) (hash-ref env x))

;
; Store handling: also use hashes..
; 
(define heap-set hash-set)
(define heap-ref hash-ref)

; A hash that maps symbols of builtins into the functions that
; implement them.
(define builtins (hash '+ + '- - '* * '/ /))

; 
; The evaluation function
; 
; Note that this function is written using define/contract, which
; allows me to specify certain "contracts" about its input and output
; values. Here I'm saying that it's arguments must be a hash, another
; hash, and an exp?, and that it must return a pair (cons cell) of a
; hash? and value? Note that hash? just comes from the Racket
; standrard library, and value? is defined up above using match. If
; you try to call this function with something that violates the
; contract, it will yell at you. Similarly, if the function returns
; something other than a cons of a hash and a value, Racket will
; complain about that (via a runtime error), too. I encourage you to
; try it with a bunch of examples.
; 
(define/contract (eval sigma env e)
  (hash? hash? exp? . -> . (cons/c hash? value?))
  (match e
    ; What to do when you see a number? Return it (without modifying
    ; heap)
    [(? number? n) (cons sigma n)]

    ; What to do when you see a variable..
    [(? var? x) (cons sigma (env-ref env x))]

    ; What to do when you see a term that looks like a lambda?
    [`(lambda (,x) ,body)
     ; Turn it into a closure..
     (cons sigma (clo e env))]

    ; Handle builtins
    [`(,(? (lambda (op) (hash-has-key? builtins op)) op) . ,args)
     (match-let* ([(cons sigma-last vs)
                   ; acc will be a pair of a state and a list of values
                   (foldl (lambda (enext acc)
                            (match-let* ([(cons sigma-next v-next)
                                          (eval (car acc) env enext)])
                              (cons sigma-next (cons v-next (cdr acc)))))
                          ; Initial value is sigma + empty list
                          (cons sigma '())
                          ; Fold over each of the arguments
                          args)])

       ; Now vs is a list of values. Assume it's a list of numbers
       ; Apply the operator to the list of values. Use `op-to-builtin`
       ; as a helper that turns the symbol for the operator into a
       ; function that we can apply.
       (cons sigma-last (apply (hash-ref builtins op) vs)))]
    
    ; What to do when you see an application?
    [`(,e1 ,e2)
     (match-let* ([(cons sigma1 (clo `(lambda (,x) ,e) env1)) (eval sigma env e1)]
                  [(cons sigma2 arg) (eval sigma1 env e2)]
                  ; ...
                  )
       (error "not implemented yet"))]))

(define empty-heap (hash))
(define empty-env (hash))

(define (inject-eval e)
  (eval empty-heap empty-env e))

(run-tests
 (test-suite
  "eval"
  (test-case "eval-num"
    ; Note that I use `cdr` here to throw away the ending heap
    (check-equal? (cdr (inject-eval 42)) 42))
  (test-case "eval-lam"
    (check-equal? (cdr (inject-eval `(lambda (x) x))) (clo '(lambda (x) x) (hash))))
  (test-case "eval-apply"
    (check-equal? (cdr (inject-eval `((lambda (x) x) 2))) 2))
  (test-case "eval-builtin-simple"
    (check-equal? (cdr (inject-eval `(+ 1 2 3))) 6))
  (test-case "eval-builtin-multi"
    (check-equal? (cdr (inject-eval `(+ (* 3 4) 2 3))) 17))))
