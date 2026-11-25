# Ergm Prob injective iff

Assume that equality on `V` is decidable; that `V` is finite; and that `ι` is finite.

Identifiability iff no affine dependence.

In symbols: `Function.Injective (ergmProb t) ↔ ∀ (v : ι → ℝ) (c : ℝ), (∀ G, v ⬝ᵥ t G = c) → v = 0`.
