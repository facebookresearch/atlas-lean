# Forward uniqueness

Two solutions with the same initial state agree at every `t ≥ 0`
(any real parameters).

Proof: on `[0, t]` both packed curves lie in a common closed ball, on which the polynomial field
is Lipschitz; apply Mathlib's `ODE_solution_unique_of_mem_Icc_right`.
