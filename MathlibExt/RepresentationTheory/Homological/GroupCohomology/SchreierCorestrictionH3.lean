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

public import
MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferDegreeThreeIndependence

/-!
# Degree-three corestriction for finite-index subgroups

Let `G` be a group, `k` a commutative ring, `H ≤ G` a finite-index subgroup, and `A` a
representation. For a right transversal `T`, start at `r₀ = t ∈ T` and decompose `r_{i-1} g_i
= h_i r_i` with `h_i ∈ H` and `r_i ∈ T`. The transfer of a three-cochain is `Tr_T z(g₁,g₂,g₃)
= ∑ t∈T, ρ(t⁻¹) z(h₁,h₂,h₃)`.

The induced map `H³(H,Res A) → H³(G,A)` is independent of the right transversal. Its value on
any three-cocycle representative is the class of this finite sum.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` a finite-index subgroup, and `A : Rep k
G`. The linear map `corestrictionH3 A : H³(H,Res A) →ₗ[k] H³(G,A)` is induced by
right-transversal Schreier transfer. Its three-cochain formula is `∑ t∈T, ρ(t⁻¹) z(h₁,h₂,h₃)`,
where `r₀=t` and `r_{i-1}g_i=h_i r_i` with `h_i∈H`, `r_i∈T`; the cohomology map is independent
of `T`. -/
noncomputable def corestrictionH3 (A : Rep k G) [H.FiniteIndex] :
    H3 (Rep.res (Subgroup.subtype H) A) →ₗ[k] H3 A :=
  corestrictionH3OfRightTransversal A
    (default : H.RightTransversal)

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` a finite-index subgroup, `A : Rep k G`,
and `T` any right transversal for `H`. Then `corestrictionH3 A =
corestrictionH3OfRightTransversal A T` as linear maps `H³(H,Res A) → H³(G,A)`, where the
right-hand map is induced by the finite Schreier three-cochain sum. -/
theorem corestrictionH3_eq_of_rightTransversal (A : Rep k G)
    [H.FiniteIndex] (T : H.RightTransversal) :
    corestrictionH3 A = corestrictionH3OfRightTransversal A T :=
  corestrictionH3OfRightTransversal_independent A
    (default : H.RightTransversal) T

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `A : Rep k G`, and `T` a
right transversal. For `z ∈ Z³(H,Res A)`, `corestrictionH3 A (H3π (Res A) z) = H3π A
(corestrictionCocyclesThree A T z)`. The transferred cocycle has value `∑ t∈T, ρ(t⁻¹)
z(h₁,h₂,h₃)`, with `r₀=t` and successive decompositions `r_{i-1}g_i=h_i r_i`, `h_i∈H`,
`r_i∈T`. -/
@[simp]
theorem corestrictionH3_H3π (A : Rep k G)
    [H.FiniteIndex] (T : H.RightTransversal)
    (z : cocycles₃ (Rep.res (Subgroup.subtype H) A)) :
    corestrictionH3 A
        (H3π (Rep.res (Subgroup.subtype H) A) z) =
      H3π A (corestrictionCocyclesThree A T z) := by
  rw [corestrictionH3_eq_of_rightTransversal A T,
    corestrictionH3OfRightTransversal_H3π]

end groupCohomology
