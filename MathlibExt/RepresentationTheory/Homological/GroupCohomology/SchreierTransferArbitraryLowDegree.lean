/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferArbitrary
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferArbitraryDifferential
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferDegreeThree
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.LowDegreeThreeFunctoriality
public import Mathlib.Tactic.FinCases

/-!
# Low-degree formulas for arbitrary Schreier transfer

The `Fin n` chosen-transversal cochain transfer specializes definitionally
to the existing degree-two and degree-three formulas after the standard
tuple/function identifications.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped BigOperators Matrix
open CategoryTheory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

/-- Degree-two specialization of arbitrary Schreier cochain transfer. -/
theorem corestrictionCochain_two_apply (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (f : H × H → A) (g₁ g₂ : G) :
    corestrictionCochain A T 2
        (fun x ↦ f (x 0, x 1)) ![g₁, g₂] =
      corestrictionCochainTwo A T f (g₁, g₂) := by
  rw [corestrictionCochain_apply, corestrictionCochainTwo_apply]
  apply Finset.sum_congr rfl
  intro t _
  rw [Subgroup.RightTransversal.schreierFactorTuple_zero,
    Subgroup.RightTransversal.schreierFactorTuple_one]
  simp

/-- Degree-three specialization of arbitrary Schreier cochain transfer. -/
theorem corestrictionCochain_three_apply (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (f : H × H × H → A) (g₁ g₂ g₃ : G) :
    corestrictionCochain A T 3
        (fun x ↦ f (x 0, x 1, x 2)) ![g₁, g₂, g₃] =
      corestrictionCochainThree A T f (g₁, g₂, g₃) := by
  rw [corestrictionCochain_apply, corestrictionCochainThree_apply]
  apply Finset.sum_congr rfl
  intro t _
  rw [Subgroup.RightTransversal.schreierFactorTuple_zero,
    Subgroup.RightTransversal.schreierFactorTuple_one,
    Subgroup.RightTransversal.schreierFactorTuple_two]
  simp

/-- Degree-one component square between the arbitrary cochain map and the
existing low-degree function model. -/
theorem corestrictionCochains_f_one_comp_cochainsIso₁_hom
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] :
    (corestrictionCochains A T).f 1 ≫ (cochainsIso₁ A).hom =
      (cochainsIso₁ (Rep.res (Subgroup.subtype H) A)).hom ≫
        ModuleCat.ofHom (corestrictionCochainOne A T) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  funext g
  rw [corestrictionCochains_f]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  simp only [cochainsIso₁, LinearEquiv.funCongrLeft]
  apply Finset.sum_congr rfl
  intro t _
  congr 2
  funext i
  fin_cases i
  simp

/-- Degree-two component square between the arbitrary cochain map and the
existing low-degree pair model. -/
theorem corestrictionCochains_f_two_comp_cochainsIso₂_hom
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] :
    (corestrictionCochains A T).f 2 ≫ (cochainsIso₂ A).hom =
      (cochainsIso₂ (Rep.res (Subgroup.subtype H) A)).hom ≫
        ModuleCat.ofHom (corestrictionCochainTwo A T) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  funext p
  rcases p with ⟨g₁, g₂⟩
  rw [corestrictionCochains_f]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  simp only [cochainsIso₂, LinearEquiv.funCongrLeft, piFinTwoEquiv]
  apply Finset.sum_congr rfl
  intro t _
  congr 2
  funext i
  fin_cases i <;> simp

/-- Degree-three component square between the arbitrary cochain map and the
existing low-degree triple model. -/
theorem corestrictionCochains_f_three_comp_cochainsIso₃_hom
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] :
    (corestrictionCochains A T).f 3 ≫ (cochainsIso₃ A).hom =
      (cochainsIso₃ (Rep.res (Subgroup.subtype H) A)).hom ≫
        ModuleCat.ofHom (corestrictionCochainThree A T) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  funext p
  rcases p with ⟨g₁, ⟨g₂, g₃⟩⟩
  rw [corestrictionCochains_f]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  simp only [cochainsIso₃, LinearEquiv.funCongrLeft]
  apply Finset.sum_congr rfl
  intro t _
  congr 2
  funext i
  fin_cases i <;>
    simp only [Nat.reduceAdd, Equiv.symm_trans, Equiv.prodCongr_symm,
      Equiv.refl_symm, Equiv.symm_symm, Equiv.trans_apply,
      Equiv.prodCongr_apply, Equiv.coe_refl, piFinTwoEquiv_symm_apply,
      Prod.map_apply, id_eq, Fin.reduceFinMk,
      Subgroup.RightTransversal.schreierFactorTuple_zero,
      Subgroup.RightTransversal.schreierFactorTuple_one,
      Subgroup.RightTransversal.schreierFactorTuple_two, Fin.isValue,
      Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_one]
  change T.schreierFactor (T.schreierRep (T.schreierRep t g₁) g₂) g₃ =
    T.schreierFactor (T.schreierRep (T.schreierRep t g₁) g₂) g₃
  rfl

/-- The former chosen-transversal `H¹` transfer is the degree-one
specialization of the arbitrary-degree cohomology transfer. -/
theorem corestrictionOfRightTransversal_one_eq
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] :
    (corestrictionOfRightTransversal A T 1).hom =
      corestrictionH1OfRightTransversal A T := by
  apply LinearMap.ext
  intro x
  induction x using groupCohomology.H1_induction_on with
  | h f =>
      rw [corestrictionH1OfRightTransversal_H1π]
      change corestrictionOfRightTransversal A T 1
          (groupCohomology.π (Rep.res (Subgroup.subtype H) A) 1
            ((isoCocycles₁ (Rep.res (Subgroup.subtype H) A)).inv f)) =
        groupCohomology.π A 1
          ((isoCocycles₁ A).inv (corestrictionCocyclesOne A T f))
      rw [corestrictionOfRightTransversal_π]
      apply congrArg (fun z ↦ groupCohomology.π A 1 z)
      apply (ModuleCat.mono_iff_injective
        (groupCohomology.iCocycles A 1)).mp inferInstance
      rw [iCocycles_corestriction_cyclesMap]
      have hsrc : groupCohomology.iCocycles
          (Rep.res (Subgroup.subtype H) A) 1
            ((isoCocycles₁ (Rep.res (Subgroup.subtype H) A)).inv f) =
          (cochainsIso₁ (Rep.res (Subgroup.subtype H) A)).inv f := by
        have h := isoCocycles₁_inv_comp_iCocycles_apply
          (Rep.res (Subgroup.subtype H) A) f
        exact h
      have htgt : groupCohomology.iCocycles A 1
          ((isoCocycles₁ A).inv (corestrictionCocyclesOne A T f)) =
        (cochainsIso₁ A).inv (corestrictionCocyclesOne A T f) := by
        have h := isoCocycles₁_inv_comp_iCocycles_apply A
          (corestrictionCocyclesOne A T f)
        exact h
      rw [hsrc, htgt]
      apply (ConcreteCategory.bijective_of_isIso
        (cochainsIso₁ A).hom).injective
      have hsquare := ConcreteCategory.congr_hom
        (corestrictionCochains_f_one_comp_cochainsIso₁_hom A T)
        ((cochainsIso₁ (Rep.res (Subgroup.subtype H) A)).inv f)
      simpa only [corestrictionCochains_f, ModuleCat.hom_ofHom,
        ModuleCat.hom_comp, LinearMap.comp_apply,
        Iso.inv_hom_id_apply, coe_corestrictionCocyclesOne] using hsquare

/-- The former chosen-transversal `H²` transfer is the degree-two
specialization of the arbitrary-degree cohomology transfer. -/
theorem corestrictionOfRightTransversal_two_eq
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] :
    (corestrictionOfRightTransversal A T 2).hom =
      corestrictionH2OfRightTransversal A T := by
  apply LinearMap.ext
  intro x
  induction x using groupCohomology.H2_induction_on with
  | h f =>
      rw [corestrictionH2OfRightTransversal_H2π]
      change corestrictionOfRightTransversal A T 2
          (groupCohomology.π (Rep.res (Subgroup.subtype H) A) 2
            ((isoCocycles₂ (Rep.res (Subgroup.subtype H) A)).inv f)) =
        groupCohomology.π A 2
          ((isoCocycles₂ A).inv (corestrictionCocyclesTwo A T f))
      rw [corestrictionOfRightTransversal_π]
      apply congrArg (fun z ↦ groupCohomology.π A 2 z)
      apply (ModuleCat.mono_iff_injective
        (groupCohomology.iCocycles A 2)).mp inferInstance
      rw [iCocycles_corestriction_cyclesMap]
      have hsrc : groupCohomology.iCocycles
          (Rep.res (Subgroup.subtype H) A) 2
            ((isoCocycles₂ (Rep.res (Subgroup.subtype H) A)).inv f) =
          (cochainsIso₂ (Rep.res (Subgroup.subtype H) A)).inv f := by
        exact isoCocycles₂_inv_comp_iCocycles_apply
          (Rep.res (Subgroup.subtype H) A) f
      have htgt : groupCohomology.iCocycles A 2
          ((isoCocycles₂ A).inv (corestrictionCocyclesTwo A T f)) =
        (cochainsIso₂ A).inv (corestrictionCocyclesTwo A T f) := by
        exact isoCocycles₂_inv_comp_iCocycles_apply A
          (corestrictionCocyclesTwo A T f)
      rw [hsrc, htgt]
      apply (ConcreteCategory.bijective_of_isIso
        (cochainsIso₂ A).hom).injective
      have hsquare := ConcreteCategory.congr_hom
        (corestrictionCochains_f_two_comp_cochainsIso₂_hom A T)
        ((cochainsIso₂ (Rep.res (Subgroup.subtype H) A)).inv f)
      simpa only [corestrictionCochains_f, ModuleCat.hom_ofHom,
        ModuleCat.hom_comp, LinearMap.comp_apply,
        Iso.inv_hom_id_apply, coe_corestrictionCocyclesTwo] using hsquare

/-- The former chosen-transversal `H³` transfer is the degree-three
specialization of the arbitrary-degree cohomology transfer. -/
theorem corestrictionOfRightTransversal_three_eq
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] :
    (corestrictionOfRightTransversal A T 3).hom =
      corestrictionH3OfRightTransversal A T := by
  apply LinearMap.ext
  intro x
  induction x using groupCohomology.H3_induction_on with
  | h f =>
      rw [corestrictionH3OfRightTransversal_H3π]
      change corestrictionOfRightTransversal A T 3
          (groupCohomology.π (Rep.res (Subgroup.subtype H) A) 3
            ((isoCocycles₃ (Rep.res (Subgroup.subtype H) A)).inv f)) =
        groupCohomology.π A 3
          ((isoCocycles₃ A).inv (corestrictionCocyclesThree A T f))
      rw [corestrictionOfRightTransversal_π]
      apply congrArg (fun z ↦ groupCohomology.π A 3 z)
      apply (ModuleCat.mono_iff_injective
        (groupCohomology.iCocycles A 3)).mp inferInstance
      rw [iCocycles_corestriction_cyclesMap]
      have hsrc : groupCohomology.iCocycles
          (Rep.res (Subgroup.subtype H) A) 3
            ((isoCocycles₃ (Rep.res (Subgroup.subtype H) A)).inv f) =
          (cochainsIso₃ (Rep.res (Subgroup.subtype H) A)).inv f := by
        have h := ConcreteCategory.congr_hom
          (isoCocycles₃_inv_comp_iCocycles
            (Rep.res (Subgroup.subtype H) A)) f
        exact h
      have htgt : groupCohomology.iCocycles A 3
          ((isoCocycles₃ A).inv (corestrictionCocyclesThree A T f)) =
        (cochainsIso₃ A).inv (corestrictionCocyclesThree A T f) := by
        have h := ConcreteCategory.congr_hom
          (isoCocycles₃_inv_comp_iCocycles A)
          (corestrictionCocyclesThree A T f)
        exact h
      rw [hsrc, htgt]
      apply (ConcreteCategory.bijective_of_isIso
        (cochainsIso₃ A).hom).injective
      have hsquare := ConcreteCategory.congr_hom
        (corestrictionCochains_f_three_comp_cochainsIso₃_hom A T)
        ((cochainsIso₃ (Rep.res (Subgroup.subtype H) A)).inv f)
      simpa only [corestrictionCochains_f, ModuleCat.hom_ofHom,
        ModuleCat.hom_comp, LinearMap.comp_apply,
        Iso.inv_hom_id_apply, coe_corestrictionCocyclesThree] using hsquare

end groupCohomology
