# Upper Unipotent same Pair add

Same-pair addition: for `i ≠ j`, `x i j a * x i j b` equals
`x i j (a + b)` in this exact left-to-right factor order, with additive
coefficient update `a + b`. Holds over `[Ring R]` with no import change,
proved directly from accepted `x_add`. Purpose: atomic same-pair merge step
needed by the right-insertion driver. Nonclaims: no collection termination,
evaluator multiplication/inversion closure, ordered normal-form existence,
coefficient/evaluator uniqueness, `toStableE` injectivity, TWT, kernel
generation, or Matsumoto theorem.
