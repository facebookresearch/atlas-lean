# Pullback of a finite free sheaf preserves its local rank

Let `(C,J,R)` and `(C',K,S)` be ringed sites with ring/module universe `u`, object universes
`u₁,u₂`, and morphism universes `v₁,v₂`. Assume weak additive sheafification and the
locally-bijective comparison on both base sites, binary products in `C`, and strong and weak
additive sheafification with the comparison on all `J`-slices. Let `F : C' ⥤ C` be continuous
and final, and `φ : S → F_*R` have right-adjoint module pushforward. For a finite `I : Type u`
with `Fintype I`, `pullback φ (free_S I)` is locally free of rank `Fintype.card I`.
