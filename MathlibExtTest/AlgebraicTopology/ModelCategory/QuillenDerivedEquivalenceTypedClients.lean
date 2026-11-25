/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicTopology.ModelCategory.QuillenDerivedEquivalence
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Typed clients for the derived equivalence of a homotopical Quillen equivalence

* The five statements `homotopicalQuillenDerivedEquivalence_{functor, inverse, unit_hom,
  counit_hom, homEquiv}` are restated with the original binder context and local
  notation and proved by the provider constants.
* For every model category `C`, the equivalence `Cᵒᵖᵒᵖ ≌ C` is a Quillen adjunction
  with invertible unit and counit whose functors preserve weak equivalences, so the
  hypotheses of the five statements are satisfiable by a non-identity adjunction. The
  statements then make the canonical total derived functors an adjoint equivalence.
* A concrete model category: `Type` with isomorphisms as weak equivalences and every
  map a cofibration and a fibration. Its weak equivalences are not all maps.
-/

open CategoryTheory CategoryTheory.Limits MorphismProperty HomotopicalAlgebra

universe u₁ u₂ v₁ v₂

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.QuillenDerivedEquivalenceClients

section OriginalStatements

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  [CategoryTheory.Adjunction.IsQuillenAdjunction adj]

local notation "WC" => weakEquivalences C
local notation "WD" => weakEquivalences D
local notation "data" => quillenDerivedAdjunctionData adj

variable [IsIso adj.unit] [IsIso adj.counit]

section Statements

variable (hL : WC ≤ (WD).inverseImage L) (hR : WD ≤ (WC).inverseImage R)

/-- The original forward-functor statement, from the provider constant. -/
example : (homotopicalQuillenDerivedEquivalence adj hL hR).functor = (data).leftDerived :=
  homotopicalQuillenDerivedEquivalence_functor adj hL hR

/-- The original inverse-functor statement, from the provider constant. -/
example : (homotopicalQuillenDerivedEquivalence adj hL hR).inverse = (data).rightDerived :=
  homotopicalQuillenDerivedEquivalence_inverse adj hL hR

/-- The original unit statement, from the provider constant. -/
example : (homotopicalQuillenDerivedEquivalence adj hL hR).unitIso.hom =
    (data).adjunction.unit :=
  homotopicalQuillenDerivedEquivalence_unit_hom adj hL hR

/-- The original counit statement, from the provider constant. -/
example : (homotopicalQuillenDerivedEquivalence adj hL hR).counitIso.hom =
    (data).adjunction.counit :=
  homotopicalQuillenDerivedEquivalence_counit_hom adj hL hR

/-- The original Hom-equivalence statement, from the provider constant. -/
example (X : (WC).Localization) (Y : (WD).Localization) (f : (data).leftDerived.obj X ⟶ Y) :
    (homotopicalQuillenDerivedEquivalence adj hL hR).toAdjunction.homEquiv X Y f =
      (data).adjunction.homEquiv X Y f :=
  homotopicalQuillenDerivedEquivalence_homEquiv adj hL hR X Y f

end Statements

/-- The canonical total left derived functor is an equivalence. -/
lemma leftDerived_isEquivalence (hL : WC ≤ (WD).inverseImage L)
    (hR : WD ≤ (WC).inverseImage R) : (data).leftDerived.IsEquivalence := by
  rw [← homotopicalQuillenDerivedEquivalence_functor adj hL hR]
  infer_instance

/-- The canonical total right derived functor is an equivalence. -/
lemma rightDerived_isEquivalence (hL : WC ≤ (WD).inverseImage L)
    (hR : WD ≤ (WC).inverseImage R) : (data).rightDerived.IsEquivalence := by
  rw [← homotopicalQuillenDerivedEquivalence_inverse adj hL hR]
  infer_instance

/-- The canonical derived unit and counit are isomorphisms. -/
lemma derived_unit_counit_isIso (hL : WC ≤ (WD).inverseImage L)
    (hR : WD ≤ (WC).inverseImage R) :
    IsIso (data).adjunction.unit ∧ IsIso (data).adjunction.counit := by
  rw [← homotopicalQuillenDerivedEquivalence_unit_hom adj hL hR,
    ← homotopicalQuillenDerivedEquivalence_counit_hom adj hL hR]
  exact ⟨Iso.isIso_hom _, Iso.isIso_hom _⟩

/-- The canonical derived adjunction's Hom maps are bijections. -/
lemma derived_homEquiv_bijective (hL : WC ≤ (WD).inverseImage L)
    (hR : WD ≤ (WC).inverseImage R) (X : (WC).Localization) (Y : (WD).Localization) :
    Function.Bijective ((data).adjunction.homEquiv X Y) := by
  have h : ⇑((data).adjunction.homEquiv X Y) =
      ⇑((homotopicalQuillenDerivedEquivalence adj hL hR).toAdjunction.homEquiv X Y) :=
    funext fun f => (homotopicalQuillenDerivedEquivalence_homEquiv adj hL hR X Y f).symm
  rw [h]
  exact Equiv.bijective _

end OriginalStatements

section OpOp

variable (C : Type u₁) [Category.{v₁} C] [ModelCategory C]

/-- The adjunction of the equivalence `Cᵒᵖᵒᵖ ≌ C`. -/
abbrev opOpAdj : unopUnop C ⊣ opOp C := (opOpEquivalence C).toAdjunction

instance : CategoryTheory.Adjunction.IsQuillenAdjunction (opOpAdj C) where
  preservesCofibrations := fun _ _ _ hf => hf
  preservesTrivialCofibrations := fun _ _ _ hf => hf

instance : IsIso (opOpAdj C).unit := inferInstanceAs (IsIso (opOpEquivalence C).unitIso.hom)

instance : IsIso (opOpAdj C).counit :=
  inferInstanceAs (IsIso (opOpEquivalence C).counitIso.hom)

lemma opOp_hL : weakEquivalences Cᵒᵖᵒᵖ ≤ (weakEquivalences C).inverseImage (unopUnop C) :=
  fun _ _ _ hf => hf

lemma opOp_hR : weakEquivalences C ≤ (weakEquivalences Cᵒᵖᵒᵖ).inverseImage (opOp C) :=
  fun _ _ _ hf => hf

/-- For the non-identity adjunction `Cᵒᵖᵒᵖ ≌ C`, the canonical total left derived functor
is an equivalence and agrees with the forward functor of the derived equivalence. -/
example : (homotopicalQuillenDerivedEquivalence (opOpAdj C) (opOp_hL C) (opOp_hR C)).functor =
      (quillenDerivedAdjunctionData (opOpAdj C)).leftDerived ∧
    (quillenDerivedAdjunctionData (opOpAdj C)).leftDerived.IsEquivalence :=
  ⟨homotopicalQuillenDerivedEquivalence_functor _ _ _,
    leftDerived_isEquivalence _ (opOp_hL C) (opOp_hR C)⟩

/-- For `Cᵒᵖᵒᵖ ≌ C`, the derived unit and counit are invertible. -/
example : IsIso (quillenDerivedAdjunctionData (opOpAdj C)).adjunction.unit ∧
    IsIso (quillenDerivedAdjunctionData (opOpAdj C)).adjunction.counit :=
  derived_unit_counit_isIso _ (opOp_hL C) (opOp_hR C)

end OpOp

section Concrete

/-- Weak equivalences in `Type` are the isomorphisms. -/
instance isoWeakEquivalences : CategoryWithWeakEquivalences (Type) := ⟨isomorphisms _⟩

/-- Every map in `Type` is a cofibration. -/
instance allCofibrations : CategoryWithCofibrations (Type) := ⟨⊤⟩

/-- Every map in `Type` is a fibration. -/
instance allFibrations : CategoryWithFibrations (Type) := ⟨⊤⟩

lemma top_isStableUnderRetracts : (⊤ : MorphismProperty (Type)).IsStableUnderRetracts :=
  ⟨fun _ _ => trivial⟩

lemma isIso_of_weakEquivalence {X Y : Type} (f : X ⟶ Y) [h : WeakEquivalence f] : IsIso f :=
  (weakEquivalence_iff f).1 h

/-- `Type` with isomorphisms as weak equivalences is a model category. -/
instance isoModelCategory : ModelCategory (Type) where
  categoryWithFibrations := allFibrations
  categoryWithCofibrations := allCofibrations
  categoryWithWeakEquivalences := isoWeakEquivalences
  cm2 := inferInstanceAs (isomorphisms (Type)).HasTwoOutOfThreeProperty
  cm3a := inferInstanceAs (isomorphisms (Type)).IsStableUnderRetracts
  cm3b := top_isStableUnderRetracts
  cm3c := top_isStableUnderRetracts
  cm4a i _ _ _ _ := by
    have := isIso_of_weakEquivalence i
    infer_instance
  cm4b _ p _ _ _ := by
    have := isIso_of_weakEquivalence p
    infer_instance
  cm5a := ⟨fun f => ⟨{
    Z := _
    i := 𝟙 _
    p := f
    hi := ⟨trivial, isomorphisms.infer_property _⟩
    hp := trivial }⟩⟩
  cm5b := ⟨fun f => ⟨{
    Z := _
    i := f
    p := 𝟙 _
    hi := trivial
    hp := ⟨trivial, isomorphisms.infer_property _⟩ }⟩⟩

/-- The weak equivalences of this model category are not all maps. -/
example : ¬ weakEquivalences (Type) (TypeCat.ofHom (fun x => nomatch x : Empty → Unit)) := by
  intro h
  have : IsIso (TypeCat.ofHom (fun x => nomatch x : Empty → Unit)) := h
  exact (inv (TypeCat.ofHom (fun x => nomatch x : Empty → Unit)) ()).elim

/-- The hypotheses are satisfiable by a concrete model category and a non-identity
adjunction: the derived equivalence of `Typeᵒᵖᵒᵖ ≌ Type` exists, and its forward functor is
the canonical total left derived functor, which is an equivalence. -/
example : (homotopicalQuillenDerivedEquivalence (opOpAdj (Type)) (opOp_hL _) (opOp_hR _)).functor =
      (quillenDerivedAdjunctionData (opOpAdj (Type))).leftDerived ∧
    (quillenDerivedAdjunctionData (opOpAdj (Type))).rightDerived.IsEquivalence :=
  ⟨homotopicalQuillenDerivedEquivalence_functor _ _ _,
    rightDerived_isEquivalence _ (opOp_hL _) (opOp_hR _)⟩

end Concrete

end MathlibExtTest.AlgebraicTopology.ModelCategory.QuillenDerivedEquivalenceClients
