/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupProductCochainLowDegree
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneOne
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneTwo
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.LowDegreeThreeFunctoriality
public import MathlibExt.Algebra.Homology.CochainGradedPairingHomologyLaws

/-!
# Low-degree comparisons for the Alexander–Whitney cup

The arbitrary-degree cup agrees with the existing explicit `(1,1)` and
`(1,2)` cups. The comparison uses their common inhomogeneous cochain
formula, the actual cocycle isomorphisms, and the cohomology quotient maps.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace groupCohomology

variable (G : Type u) [Group G] (k : Type u) [CommRing k]
variable (A B : Rep k G)

private theorem pairCycles_one_one (x : cocycles₁ A) (y : cocycles₁ B) :
    ((inhomogeneousCupPairing G k A B).pairCycles 1 1).hom
        ((isoCocycles₁ A).inv x ⊗ₜ[k] (isoCocycles₁ B).inv y) =
      (isoCocycles₂ (A ⊗ B)).inv (cupCocycleOneOne A B x y) := by
  apply (ModuleCat.mono_iff_injective (iCocycles (A ⊗ B) 2)).1 inferInstance
  change ((inhomogeneousCochains (A ⊗ B)).iCycles 2).hom
      (((inhomogeneousCupPairing G k A B).pairCycles 1 1).hom
        ((isoCocycles₁ A).inv.hom x ⊗ₜ[k] (isoCocycles₁ B).inv.hom y)) =
    ((inhomogeneousCochains (A ⊗ B)).iCycles 2).hom
      ((isoCocycles₂ (A ⊗ B)).inv.hom (cupCocycleOneOne A B x y))
  rw [HomologicalComplex.CochainGradedPairing.pairCycles_i_apply k
    (inhomogeneousCupPairing G k A B) 1 1]
  have hx := isoCocycles₁_inv_comp_iCocycles_apply A x
  have hy := isoCocycles₁_inv_comp_iCocycles_apply B y
  have hz := isoCocycles₂_inv_comp_iCocycles_apply (A ⊗ B)
    (cupCocycleOneOne A B x y)
  change (iCocycles A 1).hom ((isoCocycles₁ A).inv x) = (cochainsIso₁ A).inv x at hx
  change (iCocycles B 1).hom ((isoCocycles₁ B).inv y) = (cochainsIso₁ B).inv y at hy
  change (iCocycles (A ⊗ B) 2).hom
      ((isoCocycles₂ (A ⊗ B)).inv (cupCocycleOneOne A B x y)) =
    (cochainsIso₂ (A ⊗ B)).inv (cupCochainOneOne A B x y) at hz
  rw [hx, hy, hz]
  apply (ModuleCat.mono_iff_injective (cochainsIso₂ (A ⊗ B)).hom).1 inferInstance
  simpa using inhomogeneousCupPairing_one_one G k A B x y

private theorem pairCycles_one_two (x : cocycles₁ A) (y : cocycles₂ B) :
    ((inhomogeneousCupPairing G k A B).pairCycles 1 2).hom
        ((isoCocycles₁ A).inv x ⊗ₜ[k] (isoCocycles₂ B).inv y) =
      (isoCocycles₃ (A ⊗ B)).inv (cupCocycleOneTwo A B x y) := by
  apply (ModuleCat.mono_iff_injective (iCocycles (A ⊗ B) 3)).1 inferInstance
  change ((inhomogeneousCochains (A ⊗ B)).iCycles 3).hom
      (((inhomogeneousCupPairing G k A B).pairCycles 1 2).hom
        ((isoCocycles₁ A).inv.hom x ⊗ₜ[k] (isoCocycles₂ B).inv.hom y)) =
    ((inhomogeneousCochains (A ⊗ B)).iCycles 3).hom
      ((isoCocycles₃ (A ⊗ B)).inv.hom (cupCocycleOneTwo A B x y))
  rw [HomologicalComplex.CochainGradedPairing.pairCycles_i_apply k
    (inhomogeneousCupPairing G k A B) 1 2]
  have hx := isoCocycles₁_inv_comp_iCocycles_apply A x
  have hy := isoCocycles₂_inv_comp_iCocycles_apply B y
  have hz := isoCocycles₃_inv_comp_iCocycles_apply (A ⊗ B)
    (cupCocycleOneTwo A B x y)
  change (iCocycles A 1).hom ((isoCocycles₁ A).inv x) = (cochainsIso₁ A).inv x at hx
  change (iCocycles B 2).hom ((isoCocycles₂ B).inv y) = (cochainsIso₂ B).inv y at hy
  change (iCocycles (A ⊗ B) 3).hom
      ((isoCocycles₃ (A ⊗ B)).inv (cupCocycleOneTwo A B x y)) =
    (cochainsIso₃ (A ⊗ B)).inv (cupCochainOneTwo A B x y) at hz
  rw [hx, hy, hz]
  apply (ModuleCat.mono_iff_injective (cochainsIso₃ (A ⊗ B)).hom).1 inferInstance
  simpa using inhomogeneousCupPairing_one_two G k A B x y

/-- The generalized cup computes as the existing `(1,1)` cup on classes. -/
theorem cup_one_one_apply (x : H1 A) (y : H1 B) :
    (cup G k A B 1 1).hom (x ⊗ₜ[k] y) = cupOneOne A B x y := by
  induction x using H1_induction_on with
  | _ x =>
    induction y using H1_induction_on with
    | _ y =>
      rw [cupOneOne_H1π_H1π]
      change ((inhomogeneousCupPairing G k A B).pairHomology 1 1).hom
          (((inhomogeneousCochains A).homologyπ 1).hom ((isoCocycles₁ A).inv.hom x) ⊗ₜ[k]
            ((inhomogeneousCochains B).homologyπ 1).hom ((isoCocycles₁ B).inv.hom y)) =
        ((inhomogeneousCochains (A ⊗ B)).homologyπ 2).hom
          ((isoCocycles₂ (A ⊗ B)).inv.hom (cupCocycleOneOne A B x y))
      rw [HomologicalComplex.CochainGradedPairing.pairHomology_π_apply k
        (inhomogeneousCupPairing G k A B) 1 1,
        pairCycles_one_one]

/-- The generalized cup computes as the existing `(1,2)` cup on classes. -/
theorem cup_one_two_apply (x : H1 A) (y : H2 B) :
    (cup G k A B 1 2).hom (x ⊗ₜ[k] y) = cupOneTwo A B x y := by
  induction x using H1_induction_on with
  | _ x =>
    induction y using H2_induction_on with
    | _ y =>
      rw [cupOneTwo_H1π_H2π]
      change ((inhomogeneousCupPairing G k A B).pairHomology 1 2).hom
          (((inhomogeneousCochains A).homologyπ 1).hom ((isoCocycles₁ A).inv.hom x) ⊗ₜ[k]
            ((inhomogeneousCochains B).homologyπ 2).hom ((isoCocycles₂ B).inv.hom y)) =
        ((inhomogeneousCochains (A ⊗ B)).homologyπ 3).hom
          ((isoCocycles₃ (A ⊗ B)).inv.hom (cupCocycleOneTwo A B x y))
      rw [HomologicalComplex.CochainGradedPairing.pairHomology_π_apply k
        (inhomogeneousCupPairing G k A B) 1 2,
        pairCycles_one_two]

/-- The `(1,1)` specialization is the tensor lift of the existing bilinear cup. -/
theorem cup_one_one :
    cup G k A B 1 1 = ModuleCat.ofHom (TensorProduct.lift (cupOneOne A B)) := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  rw [cup_one_one_apply]
  rfl

/-- The `(1,2)` specialization is the tensor lift of the existing bilinear cup. -/
theorem cup_one_two :
    cup G k A B 1 2 = ModuleCat.ofHom (TensorProduct.lift (cupOneTwo A B)) := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  rw [cup_one_two_apply]
  rfl

/-- Compatibility name for the class comparison on represented H1 pairs. -/
theorem cup_one_one_H1π_H1π
    {k G : Type u} [CommRing k] [Group G] (A B : Rep k G)
    (x : cocycles₁ A) (y : cocycles₁ B) :
    (cup G k A B 1 1).hom (H1π A x ⊗ₜ[k] H1π B y) =
      cupOneOne A B (H1π A x) (H1π B y) :=
  cup_one_one_apply G k A B (H1π A x) (H1π B y)

/-- Compatibility name for the class comparison in degree (1,1). -/
theorem cup_one_one_eq_cupOneOne
    {k G : Type u} [CommRing k] [Group G] (A B : Rep k G) (x : H1 A) (y : H1 B) :
    (cup G k A B 1 1).hom (x ⊗ₜ[k] y) = cupOneOne A B x y :=
  cup_one_one_apply G k A B x y

/-- Compatibility name for the class comparison on represented H1/H2 pairs. -/
theorem cup_one_two_H1π_H2π
    {k G : Type u} [CommRing k] [Group G] (A B : Rep k G)
    (x : cocycles₁ A) (y : cocycles₂ B) :
    (cup G k A B 1 2).hom (H1π A x ⊗ₜ[k] H2π B y) =
      cupOneTwo A B (H1π A x) (H2π B y) :=
  cup_one_two_apply G k A B (H1π A x) (H2π B y)

/-- Compatibility name for the class comparison in degree (1,2). -/
theorem cup_one_two_eq_cupOneTwo
    {k G : Type u} [CommRing k] [Group G] (A B : Rep k G) (x : H1 A) (y : H2 B) :
    (cup G k A B 1 2).hom (x ⊗ₜ[k] y) = cupOneTwo A B x y :=
  cup_one_two_apply G k A B x y

end groupCohomology
