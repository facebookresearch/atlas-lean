# Ladder Cramér identity

Assume `∀ i, Measurable (X i)` and `¬ ∀ᵐ ω ∂P, X 0 ω = 0`.

Let `X` be i.i.d. integer scores with walk `S`, first strict
ascending ladder epoch `τ₊` and defective ladder-height law
`g j = P(τ₊ < ∞, S_{τ₊} = j)` (`ladderLaw`). If `θ > 0` solves `𝔼 e^{θ X} = 1` and `X` is not almost surely `0`, then `∑ j, g j e^{θ j} = 1`.

Proof: optional stopping of the martingale `e^{θ S_n}` at `τ₊ ∧ n` (`stopped_identity`, by
fixed-time independence), with the remainder `𝔼[e^{θ S_n}; τ₊ > n] ≤ (𝔼 e^{θ X / 2})^n → 0`.
