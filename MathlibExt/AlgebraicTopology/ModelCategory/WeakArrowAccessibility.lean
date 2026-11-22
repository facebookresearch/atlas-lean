/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.WeakLiftingTest
import MathlibExt.AlgebraicTopology.ModelCategory.AccessibleMorphismProperty
import MathlibExt.CategoryTheory.Presentable.InverseImage
import MathlibExt.CategoryTheory.Presentable.SurjectiveArrow
import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Accessibility of the actual model weak-arrow category

The category contains the original model weak arrows and their original
commuting squares. Its lifting-test comparison changes only membership
proofs. The existing inverse-image theorem produces the actual regular
accessibility rank, separate from the original factorization length.
-/

set_option autoImplicit false
noncomputable section

universe w uC vC

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Presentable

namespace HomotopicalAlgebra

variable (C : Type uC) [Category.{vC} C] [ModelCategory C]

/-- Compatibility name for the canonical object property of the original weak arrows. -/
abbrev modelWeakArrows : ObjectProperty (Arrow C) :=
  (weakEquivalences C).arrowObjectProperty

/-- Compatibility name for the canonical full subcategory of original weak arrows. -/
abbrev ModelWeakArrow := (weakEquivalences C).arrowObjectProperty.FullSubcategory

/-- Original Arrow isomorphisms preserve the canonical model weak property. -/
instance instIsClosedUnderIsomorphismsArrowModelWeakArrows :
    (weakEquivalences C).arrowObjectProperty.IsClosedUnderIsomorphisms where
  of_iso e hp := (weakEquivalences C).arrow_mk_iso_iff e |>.mp hp

namespace CofibrantGenerationData

variable {C} {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

/-- The actual model weak property is the inverse image of original test surjectivity. -/
theorem modelWeakArrows_eq_inverseImage :
    (weakEquivalences C).arrowObjectProperty =
      surjectiveArrows.{w}.inverseImage d.weakLiftingTest :=
  d.weakLiftingTest_weak_predicate

/-- The canonical full-subcategory comparison keeps every original Arrow and square. -/
def weakArrowTestEquivalence :
    (weakEquivalences C).arrowObjectProperty.FullSubcategory ≌
      (surjectiveArrows.{w}.inverseImage d.weakLiftingTest).FullSubcategory :=
  (CategoryTheory.Equivalence.refl : Arrow C ≌ Arrow C).congrFullSubcategory
    (by
      change surjectiveArrows.{w}.inverseImage d.weakLiftingTest =
        (weakEquivalences C).arrowObjectProperty
      exact d.modelWeakArrows_eq_inverseImage.symm)

/-- The entire forward object function retains the same original Arrow. -/
theorem weakArrowTestEquivalence_obj_function :
    (fun A : (weakEquivalences C).arrowObjectProperty.FullSubcategory ↦
      (d.weakArrowTestEquivalence.functor.obj A).obj) =
      (fun A : (weakEquivalences C).arrowObjectProperty.FullSubcategory ↦ A.obj) := rfl

/-- The entire reverse object function retains the same original Arrow. -/
theorem weakArrowTestEquivalence_inverse_obj_function :
    (fun A : (surjectiveArrows.{w}.inverseImage d.weakLiftingTest).FullSubcategory ↦
      (d.weakArrowTestEquivalence.inverse.obj A).obj) =
      (fun A ↦ A.obj) := rfl

/-- Every full forward square map is exactly the original square. -/
theorem weakArrowTestEquivalence_map_function :
    (fun (A B : (weakEquivalences C).arrowObjectProperty.FullSubcategory) (f : A ⟶ B) ↦
      (d.weakArrowTestEquivalence.functor.map f).hom) =
      (fun (A B : (weakEquivalences C).arrowObjectProperty.FullSubcategory)
        (f : A ⟶ B) ↦ f.hom) := rfl

/-- Every full reverse square map is exactly the original square. -/
theorem weakArrowTestEquivalence_inverse_map_function :
    (fun (A B : (surjectiveArrows.{w}.inverseImage d.weakLiftingTest).FullSubcategory)
      (f : A ⟶ B) ↦ (d.weakArrowTestEquivalence.inverse.map f).hom) =
      (fun (A B : (surjectiveArrows.{w}.inverseImage d.weakLiftingTest).FullSubcategory)
        (f : A ⟶ B) ↦ f.hom) := rfl

/-- The full forward comparison followed by the original inclusion is the original inclusion. -/
def weakArrowTestEquivalenceCompInclusion :
    d.weakArrowTestEquivalence.functor ⋙
      (surjectiveArrows.{w}.inverseImage d.weakLiftingTest).ι ≅
        (weakEquivalences C).arrowObjectProperty.ι :=
  Iso.refl _

/-- The inverse comparison followed by the weak inclusion is the original
inverse-image inclusion. -/
def weakArrowTestEquivalenceInverseCompInclusion :
    d.weakArrowTestEquivalence.inverse ⋙ (weakEquivalences C).arrowObjectProperty.ι ≅
      (surjectiveArrows.{w}.inverseImage d.weakLiftingTest).ι :=
  Iso.refl _

/-- The canonical comparison unit has the original identity square on every weak Arrow. -/
theorem weakArrowTestEquivalence_unit_hom
    (A : (weakEquivalences C).arrowObjectProperty.FullSubcategory) :
    (d.weakArrowTestEquivalence.unitIso.hom.app A).hom = 𝟙 A.obj := rfl

/-- The inverse unit has that same original identity square. -/
theorem weakArrowTestEquivalence_unit_inv
    (A : (weakEquivalences C).arrowObjectProperty.FullSubcategory) :
    (d.weakArrowTestEquivalence.unitIso.inv.app A).hom = 𝟙 A.obj := rfl

/-- The canonical comparison counit has the original identity square. -/
theorem weakArrowTestEquivalence_counit_hom
    (A : (surjectiveArrows.{w}.inverseImage d.weakLiftingTest).FullSubcategory) :
    (d.weakArrowTestEquivalence.counitIso.hom.app A).hom = 𝟙 A.obj := rfl

/-- The inverse counit has the same original identity square. -/
theorem weakArrowTestEquivalence_counit_inv
    (A : (surjectiveArrows.{w}.inverseImage d.weakLiftingTest).FullSubcategory) :
    (d.weakArrowTestEquivalence.counitIso.inv.app A).hom = 𝟙 A.obj := rfl

include d in
/-- The actual weak-arrow category and its actual inclusion have a produced regular rank. -/
theorem weakEquivalences_accessible
    (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
    [IsCardinalLocallyPresentable C κLP] :
    ∃ (ν : Cardinal.{w}) (_ : Fact ν.IsRegular),
      (weakEquivalences C).IsCardinalAccessible ν := by
  obtain ⟨χ, hχ, _hω, _hLP, _hκ, _hC, _hI, _hJ,
      _hIZ, _hJZ, _hIL, _hIR, _hJL, _hJR, hTest⟩ :=
    HomotopicalAlgebra.CofibrantGenerationData.exists_common_weak_test_accessibility_cardinal d κLP
  let _ : Fact χ.IsRegular := hχ
  let _ : d.weakLiftingTest.IsCardinalAccessible χ := hTest
  let _ : Functor.IsAccessible.{w} d.weakLiftingTest :=
    Functor.isAccessible_of_isCardinalAccessible _ χ
  let _ : IsAccessibleCategory.{w} C := ⟨κLP, inferInstance, inferInstance⟩
  let _ : IsAccessibleCategory.{w} (Arrow C) :=
    ⟨κLP, inferInstance, inferInstance⟩
  let _ : IsAccessibleCategory.{w} (Arrow (Type w)) :=
    ⟨Cardinal.aleph0, Cardinal.fact_isRegular_aleph0, inferInstance⟩
  obtain ⟨hSurjective, hSurjectiveInclusion⟩ := surjectiveArrow_accessible.{w}
  let _ : IsAccessibleCategory.{w} SurjectiveArrow.{w} := hSurjective
  let _ : Functor.IsAccessible.{w} surjectiveArrows.{w}.ι := hSurjectiveInclusion
  obtain ⟨ν, hν, hCategory, hInclusion⟩ :=
    inverseImage_accessible d.weakLiftingTest surjectiveArrows.{w}
  let _ : Fact ν.IsRegular := hν
  let _ : IsCardinalAccessibleCategory
      (surjectiveArrows.{w}.inverseImage d.weakLiftingTest).FullSubcategory ν := hCategory
  let _ : (surjectiveArrows.{w}.inverseImage d.weakLiftingTest).ι.IsCardinalAccessible ν :=
    hInclusion
  have hOriginal : IsCardinalAccessibleCategory
      (weakEquivalences C).arrowObjectProperty.FullSubcategory ν :=
    d.weakArrowTestEquivalence.symm.isCardinalAccessibleCategory ν
  let _ :
      (d.weakArrowTestEquivalence.functor ⋙
        (surjectiveArrows.{w}.inverseImage d.weakLiftingTest).ι).IsCardinalAccessible ν :=
    inferInstance
  have hOriginalInclusion : (weakEquivalences C).arrowObjectProperty.ι.IsCardinalAccessible ν :=
    Functor.isCardinalAccessible_of_natIso d.weakArrowTestEquivalenceCompInclusion ν
  exact ⟨ν, hν, ⟨hOriginal, hOriginalInclusion⟩⟩

include d in
/-- The original weak-equivalence morphism property is accessible with its produced rank. -/
theorem weakEquivalences_isAccessible
    (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
    [IsCardinalLocallyPresentable C κLP] :
    MorphismProperty.IsAccessible.{w} (weakEquivalences C) := by
  obtain ⟨ν, hν, hW⟩ := d.weakEquivalences_accessible κLP
  exact ⟨ν, hν, hW⟩

include d in
/-- Compatibility projection of the canonical produced rank onto the original two fields. -/
theorem modelWeakArrows_accessible
    (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
    [IsCardinalLocallyPresentable C κLP] :
    ∃ (ν : Cardinal.{w}) (_ : Fact ν.IsRegular),
      IsCardinalAccessibleCategory (ModelWeakArrow C) ν ∧
        (modelWeakArrows C).ι.IsCardinalAccessible ν := by
  obtain ⟨ν, hν, hW⟩ := d.weakEquivalences_accessible κLP
  let _ : Fact ν.IsRegular := hν
  exact ⟨ν, hν, hW.isCardinalAccessibleCategory, hW.isCardinalAccessible_ι⟩

include d in
/-- Compatibility projection for the original full-subcategory and inclusion consumers. -/
theorem modelWeakArrows_isAccessible
    (κLP : Cardinal.{w}) [Fact κLP.IsRegular]
    [IsCardinalLocallyPresentable C κLP] :
    IsAccessibleCategory.{w} (ModelWeakArrow C) ∧
      Functor.IsAccessible.{w} (modelWeakArrows C).ι := by
  obtain ⟨ν, hν, hW⟩ := d.weakEquivalences_isAccessible κLP
  let _ : Fact ν.IsRegular := hν
  let _ : (weakEquivalences C).arrowObjectProperty.ι.IsCardinalAccessible ν :=
    hW.isCardinalAccessible_ι
  exact ⟨⟨ν, hν, hW.isCardinalAccessibleCategory⟩,
    Functor.isAccessible_of_isCardinalAccessible _ ν⟩

end CofibrantGenerationData

end HomotopicalAlgebra
