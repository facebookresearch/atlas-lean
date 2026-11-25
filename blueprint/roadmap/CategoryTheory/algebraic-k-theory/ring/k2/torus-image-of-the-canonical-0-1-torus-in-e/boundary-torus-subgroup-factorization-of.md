# Boundary Torus Subgroup factorization of mem range

Factorization of a boundary torus element whose stable elementary
image lies in the range of `StableE.fromFinite F n`.

If `g ∈ boundaryTorusSubgroup n` and `toStableE g` is in the range of
`fromFinite n`, then `g` factors as `k * f` with `k ∈ ker toStableE`
and `f ∈ finiteStage n`. Uses `boundaryTorusSubgroup_le_finiteStage_succ`
to place `g` in `finiteStage (n+1)`, then
`finiteStage_succ_mem_finiteStage_sup_ker_of_toStableE_mem_range` to get
`g ∈ finiteStage n ⊔ ker`, `sup_comm` to flip to `ker ⊔ finiteStage n`,
and `Subgroup.mem_sup_of_normal_left` with the monoid-hom kernel
normality instance. Uniform for `n = 0, 1`; no extra hypothesis, no
commutative-only `mem_sup`, no direct intersection equality, and no
reproved range criterion.
