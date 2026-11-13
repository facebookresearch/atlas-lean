# Forward uniqueness

Two solutions of the SIR system (any real parameters) with the same
initial values agree at every time `t ≥ 0`.

Proof: on `[0, t]` both packed curves are continuous, hence lie in a common closed ball, on
which the `C¹` field is Lipschitz; apply Mathlib's `ODE_solution_unique_of_mem_Icc_right`
(one-sided derivatives at the initial time suffice).
