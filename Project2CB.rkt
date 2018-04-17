#lang plai-typed

(print-only-errors #t)

;; Chris Betsill

;; Got a lot of help during office hours

;; type for surface representations
(define-type ExprS
  [numS (n : number)]
  [varS (s : symbol)]
  [appS (fun : ExprS) (args : (listof ExprS))]
  [plusS (l : ExprS) (r : ExprS)]
  [bminusS (l : ExprS) (r : ExprS)]
  [multS (l : ExprS) (r : ExprS)]
  [uminusS (e : ExprS)]
  [lamS (params : (listof symbol)) (body : ExprS)]
  [withS (ids : (listof symbol)) (binding-exprs : (listof ExprS)) (bound-body : ExprS)] ;; symbols correspond to binding expressions
  [ifS (test : ExprS) (do : ExprS) (else : ExprS)] ;; will break down into cond
  [condS (tests : (listof  ExprS)) (do : (listof ExprS))] ;; tests evaluate to boolean (or an else). The corresponding item on the "do" list will be evaluated for true tests
  [boolS (value : (listof 'symbol))] ;; booleans are represented by lists of symbols. Empty lists evaluate to false, non-empty to true
  [boxS (arg : ExprS)]
  [unboxS (arg : ExprS)]
  [setboxS (b : ExprS) (v : ExprS)]
  [setS (v : symbol) (a : ExprS)]
  [seqS (es : (listof ExprS))] ;; only displays last item in list
  [orS (e1 : ExprS) (e2 : ExprS)] 
  [notS (e : ExprS)]
  [andS  (e1 : ExprS) (e2 : ExprS)]
  [=S (e1 : ExprS) (e2 : ExprS)]
  [<S (e1 : ExprS) (e2 : ExprS)]
  [>S (e1 : ExprS) (e2 : ExprS)]
  [<=S (e1 : ExprS) (e2 : ExprS)]
  [>=S (e1 : ExprS) (e2 : ExprS)]
  [eqS (e1 : ExprS) (e2 : ExprS)]
  [equalS (e1 : ExprS) (e2 : ExprS)]
  [recS (name : symbol) (value : ExprS) (body : ExprS)]
  )

;; type for core representations
(define-type ExprC
  [numC (n : number)]
  [varC (s : symbol)]
  [appC (fun : ExprC) (args : (listof ExprC))]
  [plusC (l : ExprC) (r : ExprC)]
  [multC (l : ExprC) (r : ExprC)]
  [lamC (params : (listof symbol)) (body : ExprC)]
  [boxC (arg : ExprC)]
  [unboxC (arg : ExprC)]
  [setboxC (b : ExprC) (v : ExprC)]
  [setC (v : symbol) (a : ExprC)]
  [seqC (es : (listof ExprC))]
  [condC (tests : (listof  ExprC)) (do : (listof ExprC))]  
  [boolC (value : (listof symbol))]
  [orC (e1 : ExprC) (e2 : ExprC)]
  [notC (e : ExprC)]
  [=C (e1 : ExprC) (e2 : ExprC)]
  [<C (e1 : ExprC) (e2 : ExprC)]
  [eqC (e1 : ExprC) (e2 : ExprC)]
  [equalC (e1 : ExprC) (e2 : ExprC)]
  )

;; types for values
(define-type Value
  [numV (n : number)]
  [closV (params : (listof symbol)) (body : ExprC) (env : Env)]
  [boxV (l : Location)]
  [boolV (v : (listof symbol))]) 

;; "allocate" unique "memory" locations for boxes, variables, and parameter values
(define new-loc
  (let ([n (box 0)])
    (lambda () (begin (set-box! n (add1 (unbox n)))
                      (unbox n)))))

;; types and defs for Environments and Stores
(define-type-alias Location number)

(define-type Binding [bind (name : symbol) (loc : Location)])
(define-type-alias Env (listof Binding))
(define mt-Env empty)
(define extend-env cons)
(define-type Storage [cell (loc : Location) (val : Value)])
(define-type-alias Store (listof Storage))
(define mt-Sto empty)
(define override-store cons)

;; type for returning both Value and Store from interp
(define-type Result
  [v*s (v : Value) (s : Store)])

(define (check-pairs [list : (listof s-expression)]) :  (listof s-expression)
  (map (lambda (x)
         (cond
           [(not (s-exp-list? x)) (error 'check-pairs "Invalid arguments - check parens")]
           [(= 2 (length (s-exp->list x)))x]
           [else (error 'check-pairs "Invalid arguments - arguments should contain two expressions")])) list))
                       

(define (parse [s : s-expression]) : ExprS
  ;; parse S-expressions into a surface representation that can be programmatically manipulated
  (cond [(s-exp-number? s) (numS (s-exp->number s))]
        [(s-exp-symbol? s)
         (cond
           [(equal? (s-exp->symbol s) 'true) (boolS (list 'true))] ;; any non-empty list is true
           [(equal? (s-exp->symbol s) 'false) (boolS empty)] ;; empty list is false
           [(equal? (s-exp->symbol s) 'else) (boolS (list 'else))] ;; it actually worked out really well that I chose a list representation for booleans
           [else (varS (s-exp->symbol s))])]
        [(s-exp-list? s)
         (let ([sl (s-exp->list s)])
           (cond
             [(not (s-exp-symbol? (first sl)))
              (appS (parse (first sl)) (map (lambda (x) (parse x)) (rest sl)))]
             [else
              (case (s-exp->symbol (first sl))
                [(+)(cond
                      [(not (= (length sl) 3)) (error 'parse "Invalid arguments for addition - input two arguments")]
                      [else (plusS (parse (second sl)) (parse (third sl)))])]
                [(-) (cond
                       [(<= (length sl) 3)
                        (if (= (length sl) 3)
                            (bminusS (parse (second sl)) (parse (third sl)))
                            (uminusS (parse (second sl))))]
                       [else  (error 'parse "Invalid arguments for subtraction")])]
                [(*) (cond
                       [(not (= (length sl) 3)) (error 'parse "Invalid arguments for multiplication - input two arguments")]
                       [else (multS (parse (second sl)) (parse (third sl)))])]
                [(lambda) (cond
                            [(not (= (length sl) 3)) (error 'parse "Invalid arguments for lambda - requires two arguments for paramaters (of which there can be multiple) and the body expression respectivly")]
                            [else 
                             (lamS (foldr cons empty (map (lambda (x) (if (s-exp-symbol? x) (s-exp->symbol x) (error 'parse "Invalid arguments for lambda - paramaters must be symbols")))  (s-exp->list (second sl)))) ;; builds list of params
                                   (parse (third sl)))])]
                [(with) (cond
                          [(not (= (length sl) 3)) (error 'parse "Invalid arguments for with - input two arguments for the binding expressions (of which there can be multiple) and the body expression respectivly")]
                          [else
                           (let ([binding-pairs (s-exp->list (second sl))]) ;; this extracts the pairs that bind symbols and expressions
                             (withS (map (lambda (x) (if (s-exp-symbol? (first (s-exp->list x))) (s-exp->symbol (first (s-exp->list x)))  (error 'parse "Invalid arguments for with - expressions must bind to symbols"))) (check-pairs binding-pairs)) ;; this makes a list of the symbols
                                    (map (lambda (x) (parse (second (s-exp->list x)))) binding-pairs) ;; this makes a list of the expresions which corresppmd with symbols
                                    (parse (third sl))))])] ;; this extracts the body
                [(true) (cond
                          [(not (= (length sl) 1))
                           (error 'parse "Booleans do not accept arguments")]
                          [else (boolS (list 'true))])]
                [(false) (cond
                           [(not (= (length sl) 1))
                            (error 'parse "Booleans do not accept arguments")]
                           [else (boolS empty)])]
                [(cond) (cond
                          [(< (length sl) 2) (error 'parse "Invalid arguments for cond - input at least one argument")]
                          [else
                           (condS
                            (map (lambda (x) (parse (first (s-exp->list x)))) (check-pairs (rest sl)))
                            (map (lambda (x) (parse (second (s-exp->list x)))) (rest sl)))])]
                [(if) (cond
                        [(not (equal? (length sl) 4)) (error 'parse "Invalid arguments for if : input three arguments for if")]
                        [else (condS (list (parse (second sl)) (boolS (list 'true))) (list (parse (third sl)) (parse (fourth sl))))])]
                [(or) (cond
                        [(not (= (length sl) 3)) (error 'parse "Invalid arguments for or - input two arguments")]
                        [else (orS (parse (second sl)) (parse (third sl)))])]
                [(not) (cond
                         [(not (= (length sl) 2)) (error 'parse "Invalid arguments for not - input one argument")]
                         [else (notS (parse (second sl)))])]
                [(and) (cond
                         [(not (= (length sl) 3)) (error 'parse "Invalid arguments for and - input two arguments")]
                         [else (andS (parse (second sl)) (parse (third sl)))])]
                [(eq) (cond
                        [(not (= (length sl) 3)) (error 'parse "Invalid arguments for eq - input two arguments")]
                        [else (eqS (parse (second sl)) (parse (third sl)))])]
                [(equal) (cond
                           [(not (= (length sl) 3)) (error 'parse "Invalid arguments for equal - input two arguments")]
                           [else (equalS (parse (second sl)) (parse (third sl)))])]
                [(box) (cond
                         [(not (= (length sl) 2)) (error 'parse "Invalid arguments for box- input one argument")]
                         [else (boxS (parse (second sl)))])]
                [(unbox) (cond
                           [(not (= (length sl) 2)) (error 'parse "Invalid arguments for unbox - input one argument")]
                           [else (unboxS (parse (second sl)))])]
                [(set-box!) (cond
                              [(not (= (length sl) 3)) (error 'parse "Invalid arguments for set-box! - input two arguments")]
                              [else (setboxS (parse (second sl)) (parse (third sl)))])]
                [(begin) (cond
                           [(< (length sl) 3) (error 'parse "Invalid arguments for begin - input at least two arguments")]
                           [else (seqS (map (lambda (x) (parse x)) (rest sl)))])]
                [(set!) (cond
                          [(not (= (length sl) 3)) (error 'parse "Invalid arguments for set!- input two arguments")]
                          [else (setS (if (s-exp-symbol? (second sl))
                                          (s-exp->symbol (second sl))
                                          (error 'parse "Invalid arguments for set! - first argument must be a symbol"))
                                      (parse (third sl)))])]
                [(=) (cond
                       [(not (= (length sl) 3)) (error 'parse "Invalid arguments for = - input two arguments")]
                       [else (=S (parse (second sl)) (parse (third sl)))])]
                [(<) (cond
                       [(not (= (length sl) 3)) (error 'parse "Invalid arguments for < - input two arguments")]
                       [else(<S (parse (second sl)) (parse (third sl)))])]
                [(>) (cond
                       [(not (= (length sl) 3)) (error 'parse "Invalid arguments for > - input two arguments")]
                       [else (>S (parse (second sl)) (parse (third sl)))])]
                [(<=) (cond
                        [(not (= (length sl) 3)) (error 'parse "Invalid arguments for <= - input two arguments")]
                        [else (<=S (parse (second sl)) (parse (third sl)))])]
                [(>=) (cond
                        [(not (= (length sl) 3)) (error 'parse "Invalid arguments for >= - input two arguments")]
                        [else (>=S (parse (second sl)) (parse (third sl)))])]
                [(rec) (cond
                         [(not (equal? (length sl) 4)) (error 'parse "Invalid arguments for rec - input three arguments for the function name, the function body, and the expression to be evaluated")]
                         [else (recS (if (s-exp-symbol? (second sl))
                                         (s-exp->symbol (second sl))
                                         (error 'parse "Invalid arguments for rec - first argument must be a symbol"))
                                     (parse (third sl))
                                     (parse (fourth sl)))])]
                [else (appS (parse (first sl))
                            (map (lambda (x) (parse  x)) (rest sl)))])]
             ))]
        [else (error 'parse (string-append (to-string s) " is an invalid input"))]))
        
(test (parse '4) (numS 4))
(test (parse '(* (+ 3 4) (* 2 (+ 1 2))))
      (multS (plusS (numS 3) (numS 4))
             (multS (numS 2) (plusS (numS 1) (numS 2)))))
(test (parse '(- 8)) (uminusS (numS 8)))
(test (parse '(- (+ 3 4))) (uminusS (plusS (numS 3) (numS 4))))
(test (parse '(lambda (x) (+ x x))) (lamS (list 'x) (plusS (varS 'x) (varS 'x))))
(test (parse '(with ((x 3)) (+ x x))) (withS (list 'x) (list (numS 3)) (plusS (varS 'x) (varS 'x))))
(test (parse '(with ((b (box 0))) (set! b (begin (set-box! b 10)
                                                 (unbox b)))))
      (withS (list 'b)  (list (boxS (numS 0))) (setS 'b (seqS (list (setboxS (varS 'b) (numS 10))
                                                                    (unboxS (varS 'b)))))))
(test  (parse '(<= 4 5)) (<=S (numS 4) (numS 5)))
(test  (parse '(>= 4 5)) (>=S (numS 4) (numS 5)))
(test (parse '(or true false)) (orS (boolS (list 'true)) (boolS empty)))
(test (parse '(and true false)) (andS (boolS (list 'true)) (boolS empty)))
(test (parse '(not (eq 7 8))) (notS (eqS (numS 7) (numS 8))))
(test (parse '(cond (false 4) (false 6) (else 5))) (condS (list (boolS empty) (boolS empty) (boolS (list 'else))) (list (numS 4) (numS 6) (numS 5))))
(test (parse '(rec fact (lambda (n) (if (= n 0) 1 (* n (fact (- n 1))))) (fact 5)))(recS
                                                                                    'fact
                                                                                    (lamS (list 'n) (condS (list (=S (varS 'n) (numS 0)) (boolS (list 'true))) (list (numS 1) (multS (varS 'n) (appS (varS 'fact) (list (bminusS (varS 'n) (numS 1))))))))
                                                                                    (appS (varS 'fact) (list (numS 5)))))
(test/exn (parse '(+ 1)) "Invalid arguments for addition - input two arguments")
(test/exn (parse '(+ 1 2 3)) "Invalid arguments for addition - input two arguments")
(test/exn (parse '(* 1)) "Invalid arguments for multiplication - input two arguments")
(test/exn (parse '(* 1 2 3)) "Invalid arguments for multiplication - input two arguments")
(test/exn (parse '(- 1 2 3)) "Invalid arguments for subtraction")
(test/exn (parse '(begin (+ 5 6))) "Invalid arguments for begin - input at least two arguments")
(test/exn (parse '(lambda (+ 5 6))) "Invalid arguments for lambda - requires two arguments for paramaters (of which there can be multiple) and the body expression respectivly")
(test/exn (parse '(lambda (x) (y)  (+ x y))) "Invalid arguments for lambda - requires two arguments for paramaters (of which there can be multiple) and the body expression respectivly")
(test/exn (parse '(lambda (y 9) (+ 9 y))) "Invalid arguments for lambda - paramaters must be symbols")
(test/exn (parse '(with (x 5) (x))) "Invalid arguments - check parens")
(test/exn (parse '(with ((7 8)) 7)) " Invalid arguments for with - expressions must bind to symbols")
(test/exn (parse '(with (y 8) (x 5) (x))) "Invalid arguments for with - input two arguments for the binding expressions (of which there can be multiple) and the body expression respectivly")
(test/exn (parse '(rec 8 (lambda (n) (if (= n 0) 1 (* n (fact (- n 1))))) (fact 5))) "Invalid arguments for rec - first argument must be a symbol")
(test/exn (parse '(rec fact 8 (lambda (n) (if (= n 0) 1 (* n (fact (- n 1))))) (fact 5))) "Invalid arguments for rec - input three arguments for the function name, the function body, and the expression to be evaluated")

;; the way parse does error catching on the length of the s-exp-list is pretty standard accross multiple cases so I only felt the need to test the interesting ones. 


(define (desugar [as : ExprS]) : ExprC
  ;; transform programs in surface syntax representation into core representation
  (type-case ExprS as
    [numS (n) (numC n)]
    [varS (s) (varC s)]
    [appS (f a) (appC (desugar f) (map (lambda (x) (desugar x)) a))]
    [plusS (l r) (plusC (desugar l) (desugar r))]
    [bminusS (l r) (plusC (desugar l)
                          (multC (numC -1) (desugar r)))]
    [multS (l r) (multC (desugar l) (desugar r))]
    [uminusS (e) (multC (numC -1) (desugar e))]
    [lamS (p b) (lamC p (desugar b))]
    [withS (id be bb) (appC (lamC id (desugar bb)) ;; with can be desugared into a lambda with multiple args
                            (map desugar be))]
    [ifS (t d e) (condC ;; if is the basic case of a cond. 
                  (list (desugar t) (boolC (list 'true))) ;; the first item in the list is the test, then add a true so the else will always be evaluated if the first expression does not evaluate to true
                  (list (desugar d) (desugar e)))] ;; add the "do" case and "else" case in order
    [condS (t d) (condC (map (lambda (x) (desugar x)) t) (map (lambda (x) (desugar x)) d))]
    [boolS (v) (boolC v)]
    [boxS (a) (boxC (desugar a))]
    [unboxS (a) (unboxC (desugar a))]
    [setboxS (b v) (setboxC (desugar b) (desugar v))]
    [setS (v a) (setC v (desugar a))]
    [seqS (es) (seqC (map (lambda (x) (desugar x)) es))]
    [orS (e1 e2) (orC (desugar e1) (desugar e2))]
    [notS (e) (notC (desugar e))]
    [andS  (e1 e2) (notC (orC (notC (desugar e1))  (notC (desugar e2))))] ;; negate both, then take the or - will evaluate to false if both are true, then negate
    [=S (e1 e2) (=C (desugar e1) (desugar e2))]
    [<S (e1 e2) (<C (desugar e1) (desugar e2))]
    [>S (e1 e2) (<C (desugar e2) (desugar e1))]
    [>=S (e1 e2) (orC (=C (desugar e1) (desugar e2)) (<C (desugar e2) (desugar e1)))] ;; greater than or equal to is or of > and = (common sense) 
    [<=S (e1 e2) (orC (=C (desugar e1) (desugar e2)) (<C (desugar e1) (desugar e2)))] ;; less than than or equal is or of < and = (common sense)
    [eqS (e1 e2) (eqC (desugar e1) (desugar e2))]
    [equalS (e1 e2) (equalC (desugar e1) (desugar e2))]
    [recS (name value body) (desugar (withS (list name) ;; follows the desugaring pattern given in the book
                                            (list (boxS (numS 0)))
                                            (seqS (list
                                                   (setS name value)
                                                   body))))]
    ))
(test (desugar (numS 3)) (numC 3))
(test (desugar (multS (numS 2) (numS 3)))
      (multC (numC 2) (numC 3)))
(test (desugar (uminusS (numS 8))) (multC (numC -1) (numC 8)))
(test (desugar (uminusS (plusS (numS 3) (numS 4))))
      (multC (numC -1) (plusC (numC 3) (numC 4))))
(test (desugar (parse '(with ((b (box 0))) (set! b (begin (set-box! b 10)
                                                          (unbox b))))))
      (appC (lamC (list 'b) (setC 'b (seqC (list (setboxC (varC 'b) (numC 10))
                                                 (unboxC (varC 'b))))))
            (list (boxC (numC 0)))))
(test (desugar (parse '(<= 4 5))) (orC (=C (numC 4) (numC 5)) (<C (numC 4) (numC 5))))
(test (desugar  (parse '(>= 4 5))) (orC (=C (numC 4) (numC 5)) (<C (numC 5) (numC 4))))
(test (desugar (parse '(not (eq 7 8)))) (notC (eqC (numC 7) (numC 8))))
(test (desugar (parse '(or true false))) (orC (boolC (list 'true)) (boolC empty)))
(test (desugar (parse '(and true false))) (notC (orC (notC (boolC (list 'true))) (notC (boolC empty)))))
(test (desugar (parse '(cond (false 4) (false 6) (else 5)))) (condC (list (boolC empty) (boolC empty) (boolC (list 'else))) (list (numC 4) (numC 6) (numC 5))))
(test (desugar  (parse  '(rec fact (lambda (n) (if (= n 0) 1 (* n (fact (- n 1))))) (fact 5))))
      (appC
       (lamC
        (list 'fact)
        (seqC
         (list
          (setC 'fact (lamC (list 'n) (condC (list (=C (varC 'n) (numC 0)) (boolC (list 'true))) (list (numC 1) (multC (varC 'n) (appC (varC 'fact) (list (plusC (varC 'n) (multC (numC -1) (numC 1))))))))))
          (appC (varC 'fact) (list (numC 5))))))
       (list (boxC (numC 0)))))


(define (lookup-binding [id : symbol] [env : Env]) : Location
  ;; retrieve the location to which this identifier is bound
  (cond [(empty? env) (error 'lookup-binding (string-append (string-append (to-string id) " is an unbound ID in Enviornment ") (to-string env)))]
        [(symbol=? id (bind-name (first env))) (bind-loc (first env))]
        [else (lookup-binding id (rest env))]))
(test (lookup-binding 'y (list (bind 'x 2) (bind 'y 3))) 3)

(define (fetch [loc : Location] [sto : Store]) : Value
  ;; retrieve the value stored in the given location
  (cond [(empty? sto) (error 'fetch "no value stored at that location")]
        [(= loc (cell-loc (first sto))) (cell-val (first sto))]
        [else (fetch loc (rest sto))]))

;; Type used for storing an Enviornment and a Store (needed for applying functions of multiple arguments to accumulate sto)
(define-type Sto-Env
  [sto*env (s : Store) (e : Env)])


(define (app-helper [args : (listof ExprC)] [params : (listof symbol)] [accum : Sto-Env]) : Sto-Env
  ;; returns an enviornment and store that contains each of the associations between parameters and argument values
  (cond
    [(empty? args) accum]
    [else 
     (type-case Result (interp (first args) (sto*env-e accum) (sto*env-s accum)) ;; evaluate arg
       [v*s (v-a s-a) ;; arg val and store
            (let ([where (new-loc)])
              (app-helper (rest args) (rest params) (sto*env (override-store (cell where v-a) s-a)
                                                             (extend-env (bind (first params) where) (sto*env-e accum)))))])]))
(define (seq-help [exps : (listof ExprC)] [accum : Sto-Env]) : Result
  ;; evaluates each expression to accumulate store, and displays last expression result
  (cond
    [(not (= 1 (length exps))) ;; if its not the last expression
     (type-case Result (interp (first exps) (sto*env-e accum) (sto*env-s accum)) ;; evaluate expression
       [v*s (v-e1 s-e1)
            (seq-help (rest exps) (sto*env s-e1 (sto*env-e accum)))])] ;; call function with next expression and updated env and sto
    [else (interp (first exps) (sto*env-e accum) (sto*env-s accum))])) ;; evaluate and display last expression


(define (interp [a : ExprC] [env : Env] [sto : Store]) : Result
  (type-case ExprC a
    [numC (n) (v*s (numV n) sto)]
    [varC (s) (v*s (fetch (lookup-binding s env) sto) sto)]
    [appC (f a) (type-case Result (interp f env sto) ;; evaluate function
                  [v*s (v-f s-f) ;; function val and store
                       (type-case Sto-Env (app-helper a (closV-params v-f) (sto*env s-f env)) ;; enviornment and store will contain each association between parameters and argument values
                         (sto*env (s e)
                                  (interp (closV-body v-f) e s)))])] ;; evaluate with accumulated env and sto
               
    [plusC (l r) (type-case Result (interp l env sto)
                   [v*s (v-l s-l)
                        (type-case Result (interp r env s-l)
                          [v*s (v-r s-r)
                               (v*s (num+ v-l v-r) s-r)])])]
    [multC (l r) (type-case Result (interp l env sto)
                   [v*s (v-l s-l)
                        (type-case Result (interp r env s-l)
                          [v*s (v-r s-r)
                               (v*s (num* v-l v-r) s-r)])])]
    [lamC (p b) (v*s (closV p b env) sto)]

    [boolC (v) (v*s (boolV v) sto)]

    [condC (t d) (cond-help t d env sto)]                       
    
    [boxC (a) (type-case Result (interp a env sto)
                [v*s (v-a s-a)
                     (let ([where (new-loc)])
                       (v*s (boxV where)
                            (override-store (cell where v-a) s-a)))])]
    [unboxC (a) (type-case Result (interp a env sto)
                  [v*s (v-a s-a)
                       (if (boxV? v-a) 
                           (v*s (fetch (boxV-l v-a) s-a) s-a)
                           (error 'interp "Invalid arguments for unbox- argument must evaluate to a box"))])]
    [setboxC (b a) (type-case Result (interp b env sto)
                     [v*s (v-b s-b)
                          (if (boxV? v-b)
                              (type-case Result (interp a env s-b)
                                [v*s (v-a s-a)
                                     (v*s v-a
                                          (override-store (cell (boxV-l v-b) v-a) s-a))])
                              (error 'interp "Invalid Arguments - first argument must evaluate to a box"))])]
    [setC (v a) (type-case Result (interp a env sto)
                  [v*s (v-a s-a)
                       (let ([where (lookup-binding v env)])
                         (v*s v-a
                              (override-store (cell where v-a) s-a)))])]
    [seqC (exps) (seq-help exps (sto*env sto env))]
                        
    [orC (e1 e2) (type-case Result (interp e1 env sto)
                   [v*s (v-e1 s-e1)
                        (type-case Result (interp e2 env s-e1)
                          [v*s (v-e2 s-e2)
                               (cond
                                 [(and (boolV? v-e1) (boolV? v-e2))
                                  (cond
                                    [(not (empty? (boolV-v v-e1))) (v*s (boolV (list 'true)) s-e1)]
                                    [else
                                     (cond
                                       [(not (empty? (boolV-v v-e2))) (v*s (boolV (list 'true)) s-e2)]
                                       [else (v*s (boolV empty) s-e2)])])]
                                 [else (error 'interp "Invalid Arguments - both expressions must evaluate to booleans")])])])]
                   
    [notC (e) (type-case Result (interp e env sto)
                [v*s (v-e s-e)
                     (cond
                       [(boolV? v-e)
                        (cond
                          [(empty? (boolV-v v-e)) (v*s (boolV (list 'true)) s-e)]
                          [else (v*s (boolV empty) s-e)])]
                       [else (error 'interp "Invalid Arguments - expression must evaluate to boolean")])])]
    [=C (e1 e2) (cond
                  [(and (numV? (v*s-v (interp e1 env sto))) (numV? (v*s-v (interp e2 env sto))))
                   (if (= (numV-n (v*s-v (interp e1 env sto))) (numV-n (v*s-v (interp e2 env sto))))
                       (v*s (boolV (list 'true)) sto) (v*s (boolV empty) sto))]
                  [else (error 'interp "= only accepts numbers as arguments")])]
    [<C (e1 e2) (cond
                  [(and (numV? (v*s-v (interp e1 env sto))) (numV? (v*s-v (interp e2 env sto))))
                   (if (< (numV-n (v*s-v (interp e1 env sto))) (numV-n (v*s-v (interp e2 env sto))))
                       (v*s (boolV (list 'true)) sto) (v*s (boolV empty) sto))]
                  [else (error 'interp "< only accepts numbers as arguments")])]
    [eqC (e1 e2) (type-case Result (interp e1 env sto)
                   [v*s (v-e1 s-e1)
                        (type-case Result (interp e2 env s-e1)
                          [v*s (v-e2 s-e2)
                               (type-case Value v-e1
                                 [numV (n)
                                       (cond
                                         [(numV? v-e2)
                                          (cond
                                            [(= n (numV-n v-e2)) (v*s (boolV (list 'true)) s-e2)]
                                            [else (v*s (boolV empty) s-e2)])]
                                         [else (v*s (boolV empty) s-e2)])]
                                 [closV (p b e) (cond
                                                  [(closV? v-e2)
                                                   (cond
                                                     [(eq? b (closV-body v-e2))(v*s (boolV (list 'true)) s-e2)]
                                                     [else (v*s (boolV empty) s-e2)])]
                                                  [else (v*s (boolV empty) s-e2)])]
                                 [boxV (l) (cond
                                             [(boxV? v-e2)
                                              (cond
                                                [(= l (boxV-l v-e2)) (v*s (boolV (list 'true)) s-e2)]
                                                [else (v*s (boolV empty) s-e2)])]
                                             [else (v*s (boolV empty) s-e2)])]
                                 [boolV (v) (cond
                                              [(boolV? v-e2)
                                               (cond
                                                 [(and (empty? (boolV-v v-e1)) (empty? (boolV-v v-e2)))(v*s (boolV (list 'true)) s-e2)]
                                                 [(and (not (empty? (boolV-v v-e1))) (not (empty? (boolV-v v-e2)))) (v*s (boolV (list 'true)) s-e2)]
                                                 [else (v*s (boolV empty) s-e2)])]
                                              [else (v*s (boolV empty) s-e2)])])])])]
    

                                  
    [equalC (e1 e2) (type-case Result (interp e1 env sto)
                      [v*s (v-e1 s-e1)
                           (type-case Result (interp e2 env s-e1)
                             [v*s (v-e2 s-e2)
                                  (type-case Value v-e1
                                    [numV (n)
                                          (cond
                                            [(numV? v-e2)
                                             (cond
                                               [(= n (numV-n v-e2)) (v*s (boolV (list 'true)) s-e2)]
                                               [else (v*s (boolV empty) s-e2)])]
                                            [else (v*s (boolV empty) s-e2)])]
                                    [closV (p b e) (cond
                                                     [(closV? v-e2)
                                                      (cond
                                                        [(eq? v-e1 v-e2)(v*s (boolV (list 'true)) s-e2)]
                                                        [else (v*s (boolV empty) s-e2)])]
                                                     [else (v*s (boolV empty) s-e2)])]
                                    [boxV (l) (cond  ;; a lot of these cases could be abstracted to helper functions, however I realized this after it was pretty much done 
                                                [(boxV? v-e2)
                                                 (let ([val1 (fetch (boxV-l v-e1) s-e1)] [val2 (fetch (boxV-l v-e2) s-e2)])
                                                   (type-case Value val1
                                                     [numV (n)
                                                           (cond
                                                             [(numV? val2)
                                                              (cond
                                                                [(= n (numV-n val2)) (v*s (boolV (list 'true)) s-e2)]
                                                                [else (v*s (boolV empty) s-e2)])]
                                                             [else (v*s (boolV empty) s-e2)])]
                                                     [closV (p b e)
                                                            (cond
                                                              [(closV? val2)
                                                               (cond
                                                                 [(eq? b (closV-body val2))(v*s (boolV (list 'true)) s-e2)]
                                                                 [else (v*s (boolV empty) s-e2)])]
                                                              [else (v*s (boolV empty) s-e2)])]
                                                     [boxV (l) (cond
                                                                 [(boxV? val2)
                                                                  (equal-box-nested l (boxV-l val2) s-e1 s-e2)]
                                                                 [else (v*s (boolV empty) s-e2)])]
                                                     [boolV (v) (cond
                                                                  [(boolV? val2)
                                                                   (cond
                                                                     [(and (empty?  v) (empty? (boolV-v val2)))(v*s (boolV (list 'true)) s-e2)]
                                                                     [(and (not (empty? v)) (not (empty? (boolV-v val2)))) (v*s (boolV (list 'true)) s-e2)]
                                                                     [else (v*s (boolV empty) s-e2)])]
                                                                  [else (v*s (boolV empty) s-e2)])]
                                                     ))])]
                                                   
                                    [boolV (v) (cond
                                                 [(boolV? v-e2)
                                                  (cond
                                                    [(and (empty? (boolV-v v-e1)) (empty? (boolV-v v-e2)))(v*s (boolV (list 'true)) s-e2)]
                                                    [(and (not (empty? (boolV-v v-e1))) (not (empty? (boolV-v v-e2)))) (v*s (boolV (list 'true)) s-e2)]
                                                    [else (v*s (boolV empty) s-e2)])]
                                                 [else (v*s (boolV empty) s-e2)])])])])]
    
    ))

(define (equal-box-nested [l1 : Location] [l2 : Location] [sto1 : Store]  [sto2 : Store]) : Result
  ;; used to hadle checking eqality of nested boxes
  (let ([val1 (fetch l1 sto1)] [val2 (fetch l2 sto2)])
    (type-case Value val1
      [numV (n)
            (cond
              [(numV? val2)
               (cond
                 [(= n (numV-n val2)) (v*s (boolV (list 'true)) sto2)]
                 [else (v*s (boolV empty) sto2)])]
              [else (v*s (boolV empty) sto2)])]
      [closV (p b e)
             (cond
               [(closV? val2)
                (cond
                  [(eq? b (closV-body val2))(v*s (boolV (list 'true)) sto2)]
                  [else (v*s (boolV empty) sto2)])]
               [else (v*s (boolV empty) sto2)])]
      [boxV (l) (cond
                  [(boxV? val2)
                   (equal-box-nested l (boxV-l val2) sto1 sto2)]
                  [else (v*s (boolV empty) sto2)])]

      [boolV (v) (cond
                   [(boolV? val2)
                    (cond
                      [(and (empty?  v) (empty? (boolV-v val2)))(v*s (boolV (list 'true)) sto2)]
                      [(and (not (empty? v)) (not (empty? (boolV-v val2)))) (v*s (boolV (list 'true)) sto2)]
                      [else (v*s (boolV empty) sto2)])]
                   [else (v*s (boolV empty) sto2)])]
      )))


(define (cond-help [tests : (listof ExprC)] [exps : (listof ExprC)] [env : Env] [sto : Store]) : Result
  ;; used to evaluate conditional statements
  (cond
    [(empty? tests) (error 'interp "Error : no test expressions evaluated to true, and no ELSE expression found")] ;; if no tests remain, there were no "trues" so throw error
    [else
     (type-case Result (interp (first tests) env sto) ;; evaluate the first test exoression
       [v*s (v-e1 s-e1)
            (cond
              [(boolV? v-e1) (cond  ;; if it is a boolV
                               [(not (empty? (boolV-v v-e1))) ;; if it is true
                                (cond
                                  [(and (equal? 'else (first (boolV-v v-e1))) (not (= 0 (length (rest tests)))))  (error 'interp "Error : else expression must be the final expression")] ;; check if it is an else, and if it make sure it is the last expression (otherwise throw an error) 
                                  [else (interp (first exps) env s-e1)])] ;; evaluate
                               [else (cond-help (rest tests) (rest exps) env s-e1)])] ;; move on to the next expression
              [else (error 'interp "Error : test expressions must evaluate to boolean")])])])) ;; throw error if test does not evaluate to boolV
        
        
(define (num+ [l : Value] [r : Value]) : Value
  (cond [(and (numV? l) (numV? r))
         (numV (+ (numV-n l) (numV-n r)))]
        [else (error 'num+ "bad arg")]))
(define (num* [l : Value] [r : Value]) : Value
  (cond [(and (numV? l) (numV? r))
         (numV (* (numV-n l) (numV-n r)))]
        [else (error 'num* "bad arg")]))


(define (asw [s : s-expression]) : Value
  ;; A Swell Wrapper function to interp expressions
  ;;  w/out typing interp, desugar and parse and our-functions
  (v*s-v (interp (desugar (parse s)) mt-Env mt-Sto)))

(test (asw '(* (+ 3 4) (* 2 3))) (numV 42))
(test (asw '(- 7 2)) (numV 5))
(test (asw '(+ 3 (- 1))) (numV 2))
(test (v*s-v (interp (plusC (numC 2) (appC (lamC (list 'x) (plusC (varC 'x) (numC 1))) (list (numC 4))))
                     mt-Env mt-Sto))
      (numV 7))
(test (v*s-v (interp (appC (varC 'sqr) (list (numC 3)))
                     (list (bind 'sqr 0))
                     (list (cell 0 (closV (list 'x) (multC (varC 'x) (varC 'x)) mt-Env)))))
      (numV 9))
(test (asw '(with ((double (lambda (x) (+ x x))) (quad (lambda (x) (double (double x)))))
                  (quad 5)))
      (numV 20))

(test (asw '(with ((addThings (lambda (x y) (+ x y)))) (addThings 2 3))) (numV 5))
     
 
(test (asw '(with ((b (box 7)))
                  (with ((add1 (lambda (x) (+ x 1))))
                        (begin (set-box! b (add1 10))
                               (unbox b)))))
      (numV 11))
(test (asw '(with ((b (box 7)))
                  (with ((add1 (lambda (x) (+ x 1))))
                        (+ (begin (set-box! b (add1 (unbox b)))
                                  (unbox b))
                           (begin (set-box! b (add1 (unbox b)))
                                  (unbox b))))))
      (numV 17))
(test (asw '(with ((x 7))
                  (begin (set! x 0)
                         (+ x 1))))
      (numV 1))
(test/exn (asw '(with ((x 7))
                      (begin (set! 9 0)
                             (+ x 1))))
          "Invalid arguments for set! - first argument must be a symbol")         
(test (asw '(if (true) (+ 1 2) (+ 4 6))) (numV 3))
(test (asw '(if (false) (+ 1 2) (+ 4 6))) (numV 10))
(test (asw '(not false)) (boolV (list 'true)))
(test/exn (asw '(not false true)) "Invalid arguments for not - input one argument")
(test (asw '(<= 4 5)) (boolV (list 'true)))
(test (asw '(>= 4 5)) (boolV empty))
(test/exn (asw '(= 8 true)) "= only accepts numbers as arguments")
(test/exn (asw '(< 8 true)) "< only accepts numbers as arguments")
(test/exn (asw '(unbox true)) "Invalid arguments for unbox- argument must evaluate to a box")
(test/exn (asw '(set-box! 8 true)) "Invalid Arguments - first argument must evaluate to a box")
(test (asw '(not (eq 7 8))) (boolV (list 'true)))
(test (asw '(or true false))  (boolV (list 'true)))
(test/exn (asw '(or 11 true)) "Invalid Arguments - both expressions must evaluate to boolean")
(test (asw '(and true false)) (boolV empty))
(test (asw '(cond (false 4) (false 6) (else 5))) (numV 5))
(test (asw '(rec fact (lambda (n) (if (= n 0) 1 (* n (fact (- n 1))))) (fact 5))) (numV 120))
(test/exn (asw '(cond (false 4) (false 6) (else 5) (true 8))) "Error : else expression must be the final expression")
(test/exn (asw '(cond (false 4) (false 6))) "Error : no test expressions evaluated to true, and no ELSE expression found")
(test/exn (asw '(cond (11 true))) "Error : test expressions must evaluate to boolean")
(test (asw '(equal (box (box (box 6))) (box (box (box 6))))) (boolV (list 'true)))
(test (asw '(eq (box (box (box 6))) (box (box (box 6))))) (boolV empty))
(test (asw '(with ((a (box (box (box 6))))) (eq a a))) (boolV (list 'true)))
(test (asw '(equal (box (box (box true))) (box (box (box true))))) (boolV (list 'true)))
(test (asw '(eq (box (box (box true))) (box (box (box true))))) (boolV empty))
(test (asw '(with ((a (box (box (box true))))) (eq a a))) (boolV (list 'true)))
(test (asw '(with ((x (lambda (b) (+ b 5)))) (eq x x))) (boolV (list 'true)))
(test (asw '(with ((x (lambda (b) (+ b 5)))
                   (y (lambda (b) (+ b 5)))) (eq x y))) (boolV empty))
(test (asw '((lambda () (+ 5 6)))) (numV 11))
(test (asw '((lambda (x y z) (+ x (* y z))) 1 2 3)) (numV 7))
(test (asw '(begin (+ 5 6) (+ 7 8) (< 8 7))) (boolV empty))
