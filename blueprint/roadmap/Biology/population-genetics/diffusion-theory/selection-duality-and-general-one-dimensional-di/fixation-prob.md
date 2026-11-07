# Dirichlet ratio $S(p)/S(1)$ of the scale function

The analytic Dirichlet ratio `S(p) / S(1)` for drift `b` and variance `a` (Kimura 1962;
Ewens 2004, Chapter 4). This is the solution of the backward boundary-value problem
`L u = 0`, `u(0) = 0`, `u(1) = 1` (see `eq_fixationProb_of_diffusionGenerator_eq_zero`).
It is the hitting probability `P_p(hit 1 before 0)` only when both boundaries are
Feller-accessible; that is not implied by `IsRegularDiffusion` (see the module docstring for
the `a x = x² (1 - x)²` counterexample).
