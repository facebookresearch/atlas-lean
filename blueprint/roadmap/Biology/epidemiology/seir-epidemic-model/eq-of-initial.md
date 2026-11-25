# Forward uniqueness of SEIR solutions

Let `β`, `σ`, `γ` and `N` be any real numbers. If `(S₁, E₁, I₁, R₁)` and `(S₂, E₂, I₂, R₂)` are two
[solutions of the SEIR system](is-solution.md) with these parameters and the same values at time
`0`, then `S₁(t) = S₂(t)`, `E₁(t) = E₂(t)`, `I₁(t) = I₂(t)` and `R₁(t) = R₂(t)` for every `t ≥ 0`.

Proof: on `[0, t]` the curves `s ↦ (Sₖ(s), Eₖ(s), Iₖ(s), Rₖ(s))`, `k = 1, 2`, are continuous, hence
lie in a common closed ball, on which the continuously differentiable SEIR vector field is
Lipschitz; the uniqueness theorem for Lipschitz equations, which uses only right derivatives on
`[0, t)`, then applies.
