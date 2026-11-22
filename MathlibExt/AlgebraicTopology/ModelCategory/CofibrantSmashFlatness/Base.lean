/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.OperadicAcyclicCells
public import MathlibExt.AlgebraicTopology.ModelCategory.HCofibration
public import MathlibExt.AlgebraicTopology.ModelCategory.CartesianSM7
public import MathlibExt.CategoryTheory.Monoidal.PushoutProductInitial
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Retract

/-!
# Base flatness and actual tensor comparison arrows

The incoming flatness condition is the source condition on the coefficient
model category: y □ i is weak for a weak coefficient arrow y and a coefficient
cofibration i. It is not a preservation assumption on spectra. All tensor
and retract statements retain the original arrows and both endpoints.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v w

open CategoryTheory Limits MonoidalCategory BraidedCategory HomotopicalAlgebra
open scoped MonoidalCategory

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]

/-- The actual coefficient tensor preserves every weak map when its left
factor is cofibrant, with arbitrary coefficient-arrow endpoints. -/
theorem PushoutProductLe.whiskerLeft_weak
    (h : PushoutProductLe (weakEquivalences C) (cofibrations C) (weakEquivalences C)) (K : C) (hK : IsCofibrant K)
    {Y Z : C} (f : Y ⟶ Z) (hf : weakEquivalences C f) :
    weakEquivalences C (K ◁ f) := by
  let _ : IsCofibrant K := hK
  have hbox : weakEquivalences C (Arrow.mk f □ Arrow.mk (initial.to K)).hom :=
    h f (initial.to K) hf ((cofibration_iff _).mp inferInstance)
  have hb : weakEquivalences C (Arrow.mk (initial.to K) □ Arrow.mk f).hom :=
    ((weakEquivalences C).arrow_mk_iso_iff
      (MonoidalCategory.Arrow.PushoutProduct.braiding (Arrow.mk f) (Arrow.mk (initial.to K)))).mp hbox
  exact ((weakEquivalences C).arrow_mk_iso_iff
    (MonoidalCategory.Arrow.PushoutProduct.isInitialIsoOfPreservesInitial
      (Arrow.mk f) (I := ⊥_ C) initialIsInitial (K := K))).mp hb

/-- The other coefficient-tensor orientation uses the actual original
braiding at both arbitrary weak-arrow endpoints. -/
theorem PushoutProductLe.whiskerRight_weak
    (h : PushoutProductLe (weakEquivalences C) (cofibrations C) (weakEquivalences C)) (K : C) (hK : IsCofibrant K)
    {Y Z : C} (f : Y ⟶ Z) (hf : weakEquivalences C f) :
    weakEquivalences C (f ▷ K) := by
  let e : Arrow.mk (K ◁ f) ≅ Arrow.mk (f ▷ K) :=
    Arrow.isoMk (β_ K Y) (β_ K Z) (braiding_naturality_right K f).symm
  exact ((weakEquivalences C).arrow_mk_iso_iff e).mp (h.whiskerLeft_weak K hK f hf)

end CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.CofibrantSmashFlatnessPrivate

section Base

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]

/-- H-monoidality produces the actual initial h-cofibration of an arbitrary
object tensored with a cofibrant coefficient. No unit-cofibrancy condition is used. -/
theorem HMonoidality.initial_arbitrary_tensor_cofibrant
    (h : HMonoidality C) (K : C) (hK : IsCofibrant K) (Y : C) :
    hCofibrations C (initial.to (Y ⊗ K)) := by
  let _ : IsCofibrant K := hK
  have hi : hCofibrations C (initial.to K ▷ Y) :=
    h.cofibration_tensor (initial.to K) ((cofibration_iff _).mp inferInstance) Y
  have hInitial : IsInitial ((⊥_ C) ⊗ Y) :=
    initialIsInitial.isInitialObj (tensorRight Y)
  let e : Arrow.mk (initial.to K ▷ Y) ≅ Arrow.mk (initial.to (Y ⊗ K)) :=
    Arrow.isoMk (hInitial.uniqueUpToIso initialIsInitial) (β_ K Y)
      (hInitial.hom_ext _ _)
  exact ((hCofibrations C).arrow_mk_iso_iff e).mp hi

end Base

section HCofibrationCoproducts

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- The existing flatness API uses the shared general h-cofibration composition theorem. -/
theorem hCofibration_comp {A B D : C} (f : A ⟶ B) (g : B ⟶ D)
    (hf : hCofibrations C f) (hg : hCofibrations C g) : hCofibrations C (f ≫ g) :=
  HomotopicalAlgebra.hCofibration_comp f g hf hg

/-- The actual binary coproduct of two h-cofibrant objects is h-cofibrant.
Its original initial arrow is the composite of the original first inclusion. -/
theorem initial_hCofibration_coprod (A B : C)
    (hA : hCofibrations C (initial.to A)) (hB : hCofibrations C (initial.to B)) :
    hCofibrations C (initial.to (A ⨿ B)) := by
  have hb : hCofibrations C (coprod.inl : A ⟶ A ⨿ B) :=
    (hCofibrations C).of_isPushout (IsPushout.of_hasBinaryCoproduct' A B) hB
  have h := HomotopicalAlgebra.hCofibration_comp (initial.to A) (coprod.inl : A ⟶ A ⨿ B) hA hb
  have he : initial.to A ≫ (coprod.inl : A ⟶ A ⨿ B) = initial.to (A ⨿ B) :=
    initialIsInitial.hom_ext _ _
  exact he ▸ h

/-- Adding the same original h-cofibrant object on the right preserves an
arbitrary weak map, by the actual binary-coproduct pushout square. -/
theorem coprod_map_id_weak (X : C) (hX : hCofibrations C (initial.to X))
    {A B : C} (f : A ⟶ B) (hf : weakEquivalences C f) :
    weakEquivalences C (coprod.map f (𝟙 X)) := by
  have h : (weakEquivalences C).IsStableUnderCobaseChangeAlong (coprod.inl : A ⟶ A ⨿ X) :=
    hX A (A ⨿ X) (initial.to A) coprod.inl coprod.inr (IsPushout.of_hasBinaryCoproduct' A X)
  exact h.of_isPushout (IsPushout.of_coprod_inl_with_id f X) hf

/-- Adding the same original h-cofibrant object on the left retains the full
coproduct-map braiding square at both arbitrary weak-map endpoints. -/
theorem coprod_id_map_weak (X : C) (hX : hCofibrations C (initial.to X))
    {A B : C} (f : A ⟶ B) (hf : weakEquivalences C f) :
    weakEquivalences C (coprod.map (𝟙 X) f) := by
  let e : Arrow.mk (coprod.map (𝟙 X) f) ≅ Arrow.mk (coprod.map f (𝟙 X)) :=
    Arrow.isoMk (coprod.braiding X A) (coprod.braiding X B) (by
      apply coprod.hom_ext <;> simp)
  exact ((weakEquivalences C).arrow_mk_iso_iff e).mpr (coprod_map_id_weak X hX f hf)

/-- The actual coproduct of two weak arrows is weak when the two original
fixed summands used in its factorization are h-cofibrant. -/
theorem coprod_map_weak {A A' B B' : C} (f : A ⟶ A') (g : B ⟶ B')
    (hB : hCofibrations C (initial.to B)) (hA' : hCofibrations C (initial.to A'))
    (hf : weakEquivalences C f) (hg : weakEquivalences C g) :
    weakEquivalences C (coprod.map f g) := by
  have h₀ := coprod_map_id_weak B hB f hf
  have h₁ := coprod_id_map_weak A' hA' g hg
  have he : coprod.map f (𝟙 B) ≫ coprod.map (𝟙 A') g = coprod.map f g := by
    apply coprod.hom_ext <;> simp
  exact he ▸ (weakEquivalences C).comp_mem _ _ h₀ h₁

end HCofibrationCoproducts

section WholeComparison

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The whole literal tensor comparison, before choosing its left object. -/
abbrev tensorComparison {Y Z : C} (f : Y ⟶ Z) : tensorRight Y ⟶ tensorRight Z :=
  (curriedTensor C).flip.map f

/-- Mapping the original object retract through the whole tensor comparison
retains all four original endpoint maps in the ordinary Arrow category. -/
def tensorComparisonRetract {X X' : C} (r : Retract X X')
    {Y Z : C} (f : Y ⟶ Z) : RetractArrow (X ◁ f) (X' ◁ f) :=
  (tensorComparison f).retractArrowApp r

/-- All four tensor comparison retract maps have their exact original values. -/
theorem tensorComparisonRetract_maps {X X' : C} (r : Retract X X')
    {Y Z : C} (f : Y ⟶ Z) :
    (tensorComparisonRetract r f).i.left = r.i ▷ Y ∧
      (tensorComparisonRetract r f).i.right = r.i ▷ Z ∧
      (tensorComparisonRetract r f).r.left = r.r ▷ Y ∧
      (tensorComparisonRetract r f).r.right = r.r ▷ Z :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Flatness of one original object relative to a specified weak class.
This is a conclusion property, not an input law for all objects. -/
def ObjectFlat (W : MorphismProperty C) (X : C) : Prop :=
  ∀ ⦃Y Z : C⦄ (f : Y ⟶ Z), W f → W (X ◁ f)

/-- Flatness descends through the entire original Arrow retract at every
arbitrary original weak-arrow endpoint. -/
theorem objectFlat_of_retract (W : MorphismProperty C) [W.IsStableUnderRetracts]
    {X X' : C} (r : Retract X X') (h : ObjectFlat W X') : ObjectFlat W X := by
  intro Y Z f hf
  exact W.of_retract (tensorComparisonRetract r f) (h f hf)

variable [HasInitial C] [∀ Y : C, (tensorRight Y).IsLeftAdjoint]

/-- The actual initial tensor object is flat for every weak class containing
isomorphisms; each original output tensor arrow is itself an isomorphism. -/
theorem initial_objectFlat (W : MorphismProperty C) [W.ContainsIdentities] [W.RespectsIso] :
    ObjectFlat W (⊥_ C) := by
  intro Y Z f _
  have hY : IsInitial ((⊥_ C) ⊗ Y) := initialIsInitial.isInitialObj (tensorRight Y)
  have hZ : IsInitial ((⊥_ C) ⊗ Z) := initialIsInitial.isInitialObj (tensorRight Z)
  let _ : IsIso ((⊥_ C) ◁ f) := isIso_of_isInitial hY hZ _
  exact W.of_isIso _

end WholeComparison

end HomotopicalAlgebra.CofibrantSmashFlatnessPrivate
