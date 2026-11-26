# Fixed local rank under pullback between ringed sites

Let `(C,J)` and `(C',K)` be sites, with `C : Type u₁`, `C' : Type u`, morphism universe `v₁`,
and pullbacks in `C`. Let `R,S` be ring sheaves of carrier universe `u`, with additive
sheafification and the locally-bijective comparison on all slices of both sites. Let `F : C' ⥤
C` and each `Over.post F` be continuous and final. For `φ : S → F_*R`, assume the module
pushforward along `φ` and each `overRingHom φ X` is a right adjoint. If `M` is locally free of
rank `n` over `S` and each `X∈C'` has an isomorphism `pullback(overRingHom φ X)(M.over X) ≅
(pullback φ M).over(F.obj X)`, then `pullback φ M` is locally free of rank `n` over `R`.
