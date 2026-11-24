# CSTR IVP uniqueness

Any solution of the linear CSTR equation on
`[a, b]` with the same value as the explicit solution at the initial time
`a` equals the explicit solution on the whole interval. One application
of Mathlib's `ODE_solution_unique_of_mem_Icc_right` with Lipschitz
constant `Q / V + k`; the explicit side is supplied by
`solution_hasDerivAt`.
