/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OriginalEnrichedDerivedBeckChevalley

/-!
# Pasting two original derived Beck–Chevalley squares

Six original enriched indices retain their actual projective models and
original derived adjunctions. The two full index-square equalities construct
the right cells. Pasting their left mates agrees with pasting those actual
right cells, including the original units, counits and both component maps.
Comparison with the single canonical outer restriction-compositor square
and invertibility from the source homotopy-exact criterion remain required.
-/

set_option autoImplicit false
noncomputable section
universe w uA uB uC uD uE uF uV vV
open CategoryTheory Limits MonoidalCategory
open CategoryTheory.Functor
open scoped CategoryTheory.TwoSquare

namespace HomotopicalAlgebra.OriginalEnrichedDerivedKan

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [ModelCategory V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {E : Type uE} [EnrichedCategory V E]
  {F : Type uF} [EnrichedCategory V F]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} A] [Small.{w} B] [Small.{w} C] [Small.{w} D]
  [Small.{w} E] [Small.{w} F] [LocallySmall.{w} V]
  (g : CofibrantGenerationData V κ)
  (sA : OriginalEnrichedProjective.SourceConditions (A := A) g)
  (sB : OriginalEnrichedProjective.SourceConditions (A := B) g)
  (sC : OriginalEnrichedProjective.SourceConditions (A := C) g)
  (sD : OriginalEnrichedProjective.SourceConditions (A := D) g)
  (sE : OriginalEnrichedProjective.SourceConditions (A := E) g)
  (sF : OriginalEnrichedProjective.SourceConditions (A := F) g)
  (j : EnrichedFunctor V A B) (k : EnrichedFunctor V C D) (l : EnrichedFunctor V E F)
  (p : EnrichedFunctor V A C) (q : EnrichedFunctor V B D)
  (r : EnrichedFunctor V C E) (s : EnrichedFunctor V D F)
  (h₁ : p.comp V k = j.comp V q) (h₂ : r.comp V l = k.comp V s)

/-- The actual left paste uses both original BC maps and their full coefficient whiskerings. -/
def bcVerticalPasting :
    (derivedRestriction g sC sE r ⋙ derivedRestriction g sA sC p) ⋙ derivedKan g sA sB j ⟶
      derivedKan g sE sF l ⋙ (derivedRestriction g sD sF s ⋙ derivedRestriction g sB sD q) :=
  (beckChevalley g sC sD sE sF k l r s h₂) ≫ₕ
    (beckChevalley g sA sB sC sD j k p q h₁)

/-- The right paste retains both original R-composition squares and every intermediate model. -/
def rightVerticalPasting :
    derivedRestriction g sE sF l ⋙ (derivedRestriction g sC sE r ⋙ derivedRestriction g sA sC p) ⟶
      (derivedRestriction g sD sF s ⋙ derivedRestriction g sB sD q) ⋙ derivedRestriction g sA sB j :=
  (rightSquare g sC sD sE sF k l r s h₂).hom ≫ᵥ
    (rightSquare g sA sB sC sD j k p q h₁).hom

/-- Mating the whole pasted left map recovers the two actual original right cells. -/
theorem bcVerticalPasting_mate :
    mateEquiv (derivedAdjunction g sE sF l) (derivedAdjunction g sA sB j)
      (bcVerticalPasting g sA sB sC sD sE sF j k l p q r s h₁ h₂) =
        rightVerticalPasting g sA sB sC sD sE sF j k l p q r s h₁ h₂ := by
  unfold bcVerticalPasting rightVerticalPasting
  rw [mateEquiv_vcomp, beckChevalley_right_readback, beckChevalley_right_readback]

/-- The entire forward component applies the first BC and the original q-restriction of the second. -/
theorem bcVerticalPasting_component (X : projectiveHo g sE) :
    (bcVerticalPasting g sA sB sC sD sE sF j k l p q r s h₁ h₂).app X =
      (beckChevalley g sA sB sC sD j k p q h₁).app ((derivedRestriction g sC sE r).obj X) ≫
        (derivedRestriction g sB sD q).map ((beckChevalley g sC sD sE sF k l r s h₂).app X) := by
  simp only [bcVerticalPasting, TwoSquare.hComp, NatTrans.comp_app, associator_hom_app,
    associator_inv_app, whiskerLeft_app, whiskerRight_app, Category.id_comp, Category.comp_id]

/-- Its mate component applies the original p-restriction and then the first full R-square. -/
theorem rightVerticalPasting_component (Y : projectiveHo g sF) :
    (rightVerticalPasting g sA sB sC sD sE sF j k l p q r s h₁ h₂).app Y =
      (derivedRestriction g sA sC p).map ((rightSquare g sC sD sE sF k l r s h₂).hom.app Y) ≫
        (rightSquare g sA sB sC sD j k p q h₁).hom.app ((derivedRestriction g sD sF s).obj Y) := by
  simp only [rightVerticalPasting, TwoSquare.vComp, NatTrans.comp_app, associator_hom_app,
    associator_inv_app, whiskerLeft_app, whiskerRight_app, Category.id_comp, Category.comp_id]

/-- Both directions of the actual mate bijection recover the same entire pasted left map. -/
theorem bcVerticalPasting_as_mate :
    (mateEquiv (derivedAdjunction g sE sF l) (derivedAdjunction g sA sB j)).symm
        (rightVerticalPasting g sA sB sC sD sE sF j k l p q r s h₁ h₂) =
      bcVerticalPasting g sA sB sC sD sE sF j k l p q r s h₁ h₂ := by
  let m := mateEquiv
    (G := derivedRestriction g sC sE r ⋙ derivedRestriction g sA sC p)
    (H := derivedRestriction g sD sF s ⋙ derivedRestriction g sB sD q)
    (derivedAdjunction g sE sF l) (derivedAdjunction g sA sB j)
  calc
    _ = m.symm (m (bcVerticalPasting g sA sB sC sD sE sF j k l p q r s h₁ h₂)) :=
      congrArg m.symm (bcVerticalPasting_mate g sA sB sC sD sE sF j k l p q r s h₁ h₂).symm
    _ = _ := m.symm_apply_apply _

/-- Both original adjunction units characterize this full two-cell paste. -/
theorem bcVerticalPasting_unit (X : projectiveHo g sE) :
    (derivedRestriction g sC sE r ⋙ derivedRestriction g sA sC p).map
        ((derivedAdjunction g sE sF l).unit.app X) ≫
      (rightVerticalPasting g sA sB sC sD sE sF j k l p q r s h₁ h₂).app
        ((derivedKan g sE sF l).obj X) =
      (derivedAdjunction g sA sB j).unit.app
          ((derivedRestriction g sC sE r ⋙ derivedRestriction g sA sC p).obj X) ≫
        (derivedRestriction g sA sB j).map
          ((bcVerticalPasting g sA sB sC sD sE sF j k l p q r s h₁ h₂).app X) := by
  have h := unit_mateEquiv_symm (derivedAdjunction g sE sF l) (derivedAdjunction g sA sB j)
    (rightVerticalPasting g sA sB sC sD sE sF j k l p q r s h₁ h₂) X
  rw [bcVerticalPasting_as_mate] at h
  exact h

/-- The two actual original counits retain the whole right paste and coefficient maps. -/
theorem bcVerticalPasting_counit (Y : projectiveHo g sF) :
    (derivedKan g sA sB j).map
        ((rightVerticalPasting g sA sB sC sD sE sF j k l p q r s h₁ h₂).app Y) ≫
      (derivedAdjunction g sA sB j).counit.app
        ((derivedRestriction g sD sF s ⋙ derivedRestriction g sB sD q).obj Y) =
      (bcVerticalPasting g sA sB sC sD sE sF j k l p q r s h₁ h₂).app
          ((derivedRestriction g sE sF l).obj Y) ≫
        (derivedRestriction g sD sF s ⋙ derivedRestriction g sB sD q).map
          ((derivedAdjunction g sE sF l).counit.app Y) := by
  have h := mateEquiv_counit_symm (derivedAdjunction g sE sF l) (derivedAdjunction g sA sB j)
    (rightVerticalPasting g sA sB sC sD sE sF j k l p q r s h₁ h₂) Y
  rw [bcVerticalPasting_as_mate] at h
  exact h

end HomotopicalAlgebra.OriginalEnrichedDerivedKan
