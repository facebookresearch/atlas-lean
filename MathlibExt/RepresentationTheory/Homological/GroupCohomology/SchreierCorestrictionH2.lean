/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferDegreeTwoIndependence
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferCupProjection
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierCorestrictionH1

/-!
# Degree-two corestriction for finite-index subgroups

Let `G` be a group, `k` a commutative ring, `H ≤ G` a finite-index subgroup, and `A` a `k`-representation of `G`. A right transversal `T` gives decompositions `t g = h_T(t,g) r_T(t,g)`, with `h_T(t,g) ∈ H` and `r_T(t,g) ∈ T`. The cochain transfer is
`Tr_T z(g₁,g₂) = ∑ t∈T, ρ(t⁻¹) z(h_T(t,g₁), h_T(r_T(t,g₁),g₂))`.
Its map `H²(H,Res A) → H²(G,A)` is independent of `T`.

For representations `A,B`, classes `x ∈ H¹(G,A)` and `y ∈ H¹(H,Res B)` satisfy `cor(θ_*(res x
∪ y)) = x ∪ cor(y)`, where `θ : Res A ⊗ Res B → Res(A ⊗ B)` is the restriction/tensor
comparison.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` a finite-index subgroup, and `A : Rep k
G`. The linear map `corestrictionH2 A : H²(H,Res A) →ₗ[k] H²(G,A)` is induced by
right-transversal Schreier transfer. For a transversal `T`, this transfer sends `z(g₁,g₂)` to
`∑ t∈T, ρ(t⁻¹) z(h_T(t,g₁),h_T(r_T(t,g₁),g₂))`, using `t g = h_T(t,g) r_T(t,g)`; the
cohomology map is independent of `T`. -/
noncomputable def corestrictionH2 (A : Rep k G) [H.FiniteIndex] :
    groupCohomology.H2 (Rep.res (Subgroup.subtype H) A) →ₗ[k]
      groupCohomology.H2 A :=
  corestrictionH2OfRightTransversal A (default : H.RightTransversal)

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` a finite-index subgroup, `A : Rep k G`,
and `T` any right transversal for `H`. Then `corestrictionH2 A =
corestrictionH2OfRightTransversal A T` as linear maps `H²(H,Res A) → H²(G,A)`. The right-hand
map is induced by the finite Schreier cochain sum for `T`. -/
theorem corestrictionH2_eq_of_rightTransversal (A : Rep k G)
    [H.FiniteIndex] (T : H.RightTransversal) :
    corestrictionH2 A = corestrictionH2OfRightTransversal A T := by
  unfold corestrictionH2
  exact corestrictionH2OfRightTransversal_independent A _ T

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `A : Rep k G`, and `T` a
right transversal. For `z ∈ Z²(H,Res A)`, `corestrictionH2 A (H2π (Res A) z) = H2π A
(corestrictionCocyclesTwo A T z)`. The transferred cocycle has value `∑ t∈T, ρ(t⁻¹)
z(h_T(t,g₁),h_T(r_T(t,g₁),g₂))`, where `t g = h_T(t,g) r_T(t,g)`. -/
theorem corestrictionH2_H2π (A : Rep k G)
    [H.FiniteIndex] (T : H.RightTransversal)
    (z : groupCohomology.cocycles₂
      (Rep.res (Subgroup.subtype H) A)) :
    corestrictionH2 A
        (groupCohomology.H2π (Rep.res (Subgroup.subtype H) A) z) =
      groupCohomology.H2π A (corestrictionCocyclesTwo A T z) := by
  rw [corestrictionH2_eq_of_rightTransversal,
    corestrictionH2OfRightTransversal_H2π]

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` a finite-index subgroup, and `A,B : Rep k
G`. For `x ∈ H¹(G,A)` and `y ∈ H¹(H,Res B)`, `cor²_{A⊗B}(θ_*(res¹_A x ∪ y)) = x ∪ cor¹_B(y)`
in `H²(G,A ⊗ B)`. Here `θ = (Rep.resTensorIso (Subgroup.subtype H) A B).hom : Res A ⊗ Res B →
Res(A ⊗ B)`, and the degree-one and degree-two cups are `cupOneOne`. -/
theorem corestrictionH2_cupOneOne
    (A B : Rep k G) (H : Subgroup G) [H.FiniteIndex]
    (x : groupCohomology.H1 A)
    (y : groupCohomology.H1 (Rep.res (Subgroup.subtype H) B)) :
    corestrictionH2 (A ⊗ B)
        (groupCohomology.map (MonoidHom.id H)
          (Rep.resTensorIso (Subgroup.subtype H) A B).hom 2
          (groupCohomology.cupOneOne
            (Rep.res (Subgroup.subtype H) A)
            (Rep.res (Subgroup.subtype H) B)
            (groupCohomology.map (Subgroup.subtype H) (𝟙 _) 1 x) y)) =
      groupCohomology.cupOneOne A B x (corestrictionH1 B y) := by
  unfold corestrictionH2 corestrictionH1
  exact corestrictionH2OfRightTransversal_cupOneOne
    A B (default : H.RightTransversal) x y

end groupCohomology
