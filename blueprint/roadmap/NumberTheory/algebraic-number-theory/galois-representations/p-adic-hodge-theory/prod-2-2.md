# Prod

The direct sum of a filtered `(φ, N)`-module `M₁` on `D₁` and a filtered `(φ, N)`-module `M₂`
on `D₂`: the direct sum `D₁ × D₂` of the underlying `(φ, N)`-modules (`PhiNModule.prod`), with the
filtration of `(D₁ × D₂)_K = K ⊗_{K₀} (D₁ × D₂)` whose `i`-th step is the preimage of
`Fil^i D₁_K × Fil^i D₂_K` under the isomorphism `(D₁ × D₂)_K ≅ D₁_K × D₂_K`
(`TensorProduct.prodRight`).
