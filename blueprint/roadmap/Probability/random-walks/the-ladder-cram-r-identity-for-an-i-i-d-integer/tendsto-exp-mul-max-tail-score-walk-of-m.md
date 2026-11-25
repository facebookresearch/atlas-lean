# Ladder-height limit from the Cramér root

Assume `∀ i, Measurable (X i)` and `¬ ∀ᵐ ω ∂P, X 0 ω = 0`.

**Ladder-height limit from the Cramér root** (Cramér–Lundberg / Karlin–Dembo). For i.i.d.
integer scores `X` that are not almost surely `0`, if `θ > 0` solves `𝔼 e^{θ X} = 1`, the
ladder support is aperiodic and the tilted ladder mean `μ = ∑ j g j e^{θ j}` is finite, then
`e^{θ k} P(M > k) → (1 - P(M > 0)) / ((e^θ - 1) μ)`. This is
`tendsto_exp_mul_maxTail_scoreWalk` with its Cramér hypothesis discharged by
`hasSum_ladderLaw_mul_exp`.
