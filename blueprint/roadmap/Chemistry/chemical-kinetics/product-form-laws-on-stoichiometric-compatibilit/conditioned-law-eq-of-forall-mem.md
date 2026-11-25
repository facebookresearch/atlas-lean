# Weights proportional on a set with a nonzero factor give the same law

Let `S` be a finite set, `c, d ∈ ℝ^S`, `Γ ⊆ ℕ^S` and `a` a nonzero real number. If the
[Poisson weight](../../../Biology/systems-biology/stochastic-mass-action-metabolic-control-and-flu/poisson-weight.md)s
satisfy `π_d(x) = a π_c(x)` for every `x ∈ Γ`, then the two [conditioned laws](conditioned-law.md)
agree at every state: `π_d(x | Γ) = π_c(x | Γ)` for all `x ∈ ℕ^S`. The masses satisfy
`π_d(Γ) = a π_c(Γ)`, so the factor cancels, also when `π_c(Γ) = 0`, where both laws are `0` by the
convention `y / 0 = 0`. The factor must be nonzero: for `a = 0` the law of `d` is `0`, while that of
`c` need not be.
