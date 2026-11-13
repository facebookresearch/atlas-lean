# Forward uniqueness

Two solutions of the Michaelis–Menten system (any real rate
constants) with the same initial values agree at every time `t ≥ 0`.

Proof: on `[0, t]` both packed curves lie in a common closed ball, on which the polynomial field
is Lipschitz; apply Mathlib's `ODE_solution_unique_of_mem_Icc_right`.
