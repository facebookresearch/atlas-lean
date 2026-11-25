# Boundary Torus sup ker inf finite Stage sup ker refined factorization

Refined factorization for the joined boundary-torus / finite-stage intersection.

Given `g` in `(boundaryTorusSubgroup n ⊔ ker toStableE) ⊓
(finiteStage n ⊔ ker toStableE)`, there exist `u : Fin n → Fˣ` with
`∏ u = 1` and `k ∈ ker toStableE` such that
`toStableE g = piHom n u = toStableE (boundaryTorusProd n u)` and
`g = k * boundaryTorusProd n u`.

This is a refined factorization and not exact subgroup equality; it only
factors the `ker`-joined intersection via a product-one torus and a kernel
correction.
