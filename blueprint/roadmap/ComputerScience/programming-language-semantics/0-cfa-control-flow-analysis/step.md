# Transitions of the CEK machine

Call-by-value evaluation in five rules, where
`ev e env k` evaluates `e` in the environment `env` and `ret v k` returns the closure `v` to `k`:

* `var`: `ev (var x l) env k` steps to `ret c k` when `Env.lookup env x = some c`, the newest
  binding of `x` in the current environment `env`;
* `lam`: `ev (lam x body l) env k` steps to `ret (mk x body l env) k`, the closure of the
  abstraction in the current environment `env`;
* `app`: `ev (app fn arg l) env k` steps to `ev fn env (ar l arg env k)`, which evaluates the
  function `fn` in `env` and saves the argument `arg` and `env` in an argument frame;
* `arg`: `ret c (ar l arg env k)` steps to `ev arg env (fn l c k)`, which evaluates the argument
  in the environment `env` saved in the frame and saves the function closure `c` in a function
  frame;
* `call`: `ret v (fn l (mk x body l' env) k)` steps to `ev body ((x, v) :: env) k`, which runs
  the body of the function closure in the environment `env` of that closure, not the caller's,
  extended by binding its parameter `x` to the argument `v`.

A variable whose name has no binding in the current environment, and a closure returned to the
empty continuation, have no transition.
