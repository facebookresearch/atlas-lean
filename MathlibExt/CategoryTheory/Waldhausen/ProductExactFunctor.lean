/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.Product
public import MathlibExt.CategoryTheory.Waldhausen.ExactFunctor

/-!
# Exact projections of componentwise Waldhausen products

Both original product projections preserve zero objects, cofibrations,
weak equivalences and the actual componentwise pushout squares. The source
and target object and morphism universes are independent.
-/

public section

noncomputable section
set_option autoImplicit false

open CategoryTheory Limits

namespace CategoryTheory.Functor.IsWaldhausenExact

universe uA vA uB vB

variable (A : Type uA) [Category.{vA} A] [HasZeroObject A] [WaldhausenCategoryWithoutGluing A]
  (B : Type uB) [Category.{vB} B] [HasZeroObject B] [WaldhausenCategoryWithoutGluing B]

/-- The first product projection is exact for the componentwise Waldhausen structure. -/
theorem prodFst :
    letI : WaldhausenCategoryWithoutGluing (A × B) := prodWaldhausen (C := A) (D := B);
    (CategoryTheory.Prod.fst A B).IsWaldhausenExact := by
  let : WaldhausenCategoryWithoutGluing (A × B) := prodWaldhausen (C := A) (D := B)
  refine { map_isZero := ?_, map_cofibration := ?_, map_weakEquivalence := ?_, map_pushout := ?_ }
  · intro X hX
    exact ((isZero_prod_iff (C := A) (D := B)).mp hX).1
  · intro X Y f hf
    exact ((isCofibration_prod_iff (C := A) (D := B) f).mp hf).1
  · intro X Y f hf
    exact ((isWeakEquivalence_prod_iff (C := A) (D := B) f).mp hf).1
  · intro X Y X' P i f inl inr _hi hP
    exact ((isPushout_prod_iff (C := A) (D := B)).mp hP).1

/-- The second product projection is exact for the componentwise Waldhausen structure. -/
theorem prodSnd :
    letI : WaldhausenCategoryWithoutGluing (A × B) := prodWaldhausen (C := A) (D := B);
    (CategoryTheory.Prod.snd A B).IsWaldhausenExact := by
  let : WaldhausenCategoryWithoutGluing (A × B) := prodWaldhausen (C := A) (D := B)
  refine { map_isZero := ?_, map_cofibration := ?_, map_weakEquivalence := ?_, map_pushout := ?_ }
  · intro X hX
    exact ((isZero_prod_iff (C := A) (D := B)).mp hX).2
  · intro X Y f hf
    exact ((isCofibration_prod_iff (C := A) (D := B) f).mp hf).2
  · intro X Y f hf
    exact ((isWeakEquivalence_prod_iff (C := A) (D := B) f).mp hf).2
  · intro X Y X' P i f inl inr _hi hP
    exact ((isPushout_prod_iff (C := A) (D := B)).mp hP).2

universe v₁ u₁ v₂ u₂ v₃ u₃

/-- Pair exact functors with the SAME original common source and
componentwise target product value. All three object and morphism universe
roles remain independent, and all four exactness fields are retained. -/
theorem prod'
    {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
    {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
    {E : Type u₃} [Category.{v₃} E] [HasZeroObject E] [WaldhausenCategoryWithoutGluing E]
    {F : C ⥤ D} {G : C ⥤ E}
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) :
    (letI : WaldhausenCategoryWithoutGluing (D × E) := prodWaldhausen;
      (F.prod' G).IsWaldhausenExact) := by
  let : WaldhausenCategoryWithoutGluing (D × E) := prodWaldhausen
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X hX
    exact (isZero_prod_iff (C := D) (D := E)).2
      ⟨hF.map_isZero hX, hG.map_isZero hX⟩
  · intro X Y f hf
    exact (isCofibration_prod_iff (C := D) (D := E) ((F.prod' G).map f)).2
      ⟨hF.map_cofibration f hf, hG.map_cofibration f hf⟩
  · intro X Y f hf
    exact (isWeakEquivalence_prod_iff (C := D) (D := E) ((F.prod' G).map f)).2
      ⟨hF.map_weakEquivalence f hf, hG.map_weakEquivalence f hf⟩
  · intro X Y X' Q i f inl inr hi hp
    exact (isPushout_prod_iff (C := D) (D := E)).2
      ⟨hF.map_pushout i f inl inr hi hp, hG.map_pushout i f inl inr hi hp⟩

end CategoryTheory.Functor.IsWaldhausenExact

end
