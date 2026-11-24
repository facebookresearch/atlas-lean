/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import MathlibExt.CategoryTheory.Waldhausen.Basic

/-!
# Exact functors between Waldhausen structures without gluing

A Waldhausen-exact functor preserves zero objects, cofibrations, weak
equivalences, and pushout squares along cofibrations. Neither structural
instance is required to satisfy gluing.

The predicate is explicit rather than a typeclass: the same underlying
category may carry several Waldhausen structures.  It is also distinct from
`CategoryTheory.Functor.IsExact`, which concerns additive functors between
Quillen exact categories.

## Main definitions

* `CategoryTheory.Functor.IsWaldhausenExact`
* `CategoryTheory.Functor.IsWaldhausenExact.id`
* `CategoryTheory.Functor.IsWaldhausenExact.comp`
* `CategoryTheory.Functor.IsWaldhausenExact.map_cofibrationSequence`
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {E : Type u₃} [Category.{v₃} E] [HasZeroObject E] [WaldhausenCategoryWithoutGluing E]

/-- A functor between Waldhausen structures without gluing is Waldhausen exact
if it preserves zero objects, cofibrations, weak equivalences, and pushout
squares whose distinguished source leg is a cofibration.

The pushout orientation agrees with `WaldhausenCategoryWithoutGluing.cofibration_pushout`:
for a cofibration `i : X ⟶ Y` and `f : X ⟶ X'`, the square is
`IsPushout f i inl inr`. -/
structure Functor.IsWaldhausenExact (F : C ⥤ D) : Prop where
  /-- Images of zero objects are zero objects. -/
  map_isZero : ∀ {X : C}, IsZero X → IsZero (F.obj X)
  /-- Images of cofibrations are cofibrations. -/
  map_cofibration : ∀ {X Y : C} (f : X ⟶ Y),
    IsCofibration (C := C) f → IsCofibration (C := D) (F.map f)
  /-- Images of weak equivalences are weak equivalences. -/
  map_weakEquivalence : ∀ {X Y : C} (f : X ⟶ Y),
    IsWeakEquivalence (C := C) f → IsWeakEquivalence (C := D) (F.map f)
  /-- Pushout squares along cofibrations remain pushout squares. -/
  map_pushout : ∀ {X Y X' P : C} (i : X ⟶ Y) (f : X ⟶ X')
    (inl : X' ⟶ P) (inr : Y ⟶ P),
    IsCofibration (C := C) i → IsPushout f i inl inr →
      IsPushout (F.map f) (F.map i) (F.map inl) (F.map inr)

namespace Functor.IsWaldhausenExact

/-- The original constant functor at the chosen target zero is Waldhausen
exact, with independent source and target object and morphism universes. -/
theorem constantZero
    (C : Type u₁) [Category.{v₁} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
    (D : Type u₂) [Category.{v₂} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D] :
    ((Functor.const C).obj (0 : D)).IsWaldhausenExact where
  map_isZero _ := isZero_zero D
  map_cofibration _ _ := WaldhausenCategoryWithoutGluing.cofibrations.of_isIso (𝟙 (0 : D))
  map_weakEquivalence _ _ := WaldhausenCategoryWithoutGluing.weakEquivalences.of_isIso (𝟙 (0 : D))
  map_pushout _ _ _ _ _ _ := IsPushout.of_id_fst (f := 𝟙 (0 : D))

/-- The identity functor is Waldhausen exact. -/
protected theorem id : (Functor.id C).IsWaldhausenExact where
  map_isZero hX := by simpa using hX
  map_cofibration _ hf := by simpa using hf
  map_weakEquivalence _ hf := by simpa using hf
  map_pushout _ _ _ _ _ h := by simpa using h

/-- A composite of Waldhausen-exact functors is Waldhausen exact. -/
theorem comp {F : C ⥤ D} {G : D ⥤ E}
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) :
    (F ⋙ G).IsWaldhausenExact where
  map_isZero hX := hG.map_isZero (hF.map_isZero hX)
  map_cofibration f hf :=
    hG.map_cofibration (F.map f) (hF.map_cofibration f hf)
  map_weakEquivalence f hf :=
    hG.map_weakEquivalence (F.map f) (hF.map_weakEquivalence f hf)
  map_pushout i f inl inr hi h := by
    exact hG.map_pushout (F.map i) (F.map f) (F.map inl) (F.map inr)
      (hF.map_cofibration i hi) (hF.map_pushout i f inl inr hi h)

/-- A Waldhausen-exact functor sends cofibration sequences to cofibration
sequences.

The image of the source zero object need not be definitionally the selected
target zero object.  We transport the mapped pushout square along the
canonical isomorphism between these zero objects. -/
theorem map_cofibrationSequence {F : C ⥤ D} (hF : F.IsWaldhausenExact)
    {X Y Z : C} {i : X ⟶ Y} {p : Y ⟶ Z}
    (hSeq : IsCofibrationSequence (C := C) i p) :
    IsCofibrationSequence (C := D) (F.map i) (F.map p) := by
  obtain ⟨hi, h, q, hPush⟩ := hSeq
  let e : F.obj (0 : C) ≅ (0 : D) :=
    (hF.map_isZero (isZero_zero C)).isoZero
  refine ⟨hF.map_cofibration i hi, F.map h ≫ e.hom,
    e.inv ≫ F.map q, ?_⟩
  have hMapped :
      IsPushout (F.map h) (F.map i) (F.map q) (F.map p) :=
    hF.map_pushout i h q p hi hPush
  apply hMapped.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
  all_goals simp

end Functor.IsWaldhausenExact

end CategoryTheory
