# Uniform local rank glues over a cover

Let `C : Type u₁` have morphism universe `v₁`, `J` be a topology, and `R : Sheaf J
RingCat.{u}`. Assume strong and weak additive sheafification with the locally-bijective
comparison on first slices, and additive sheafification with the comparison on second slices.
For `M`, `n : ℕ`, a cover `X : I → C` with `I : Type u₁`, and data `D_i :
LocalGeneratorsData.{max u₁ v₁}(M.over(X i))` each locally free of rank `n`, the global sheaf
`M` is locally free of rank `n`.
