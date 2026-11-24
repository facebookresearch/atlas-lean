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

public import MathlibExt.CategoryTheory.Waldhausen.Basic
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import MathlibExt.CategoryTheory.Products.Limits
public import MathlibExt.CategoryTheory.MorphismProperty.Prod

/-!
# Bounded product Waldhausen foundation

Componentwise product of two Waldhausen categories: cofibrations and weak
equivalences are the `MorphismProperty.prod` conjunctions, with
`IsMultiplicative`/`RespectsIso` proved componentwise. The product zero object
is `((0 : C), (0 : D))`, and pushouts along product cofibrations are paired
from the component witnesses. One componentwise cofibration-sequence
characterization is proved.

This file provides no stage comparison, exact-category bridge, nerve,
realization, additivity, K/G-theory, or spectral claim.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D]

variable [WaldhausenCategoryWithoutGluing C] [WaldhausenCategoryWithoutGluing D]

/-- Componentwise cofibrations on `C × D`. -/
def cofibrationsProd : MorphismProperty (C × D) :=
  MorphismProperty.prod WaldhausenCategoryWithoutGluing.cofibrations
    WaldhausenCategoryWithoutGluing.cofibrations

/-- Componentwise weak equivalences on `C × D`. -/
def weakEquivalencesProd : MorphismProperty (C × D) :=
  MorphismProperty.prod WaldhausenCategoryWithoutGluing.weakEquivalences
    WaldhausenCategoryWithoutGluing.weakEquivalences

/-- Bounded product Waldhausen structure, deliberately not an instance. -/
@[instance_reducible]
def prodWaldhausen : WaldhausenCategoryWithoutGluing (C × D) where
  cofibrations := cofibrationsProd
  weakEquivalences := weakEquivalencesProd
  cofibrations_isMultiplicative := MorphismProperty.Prod.isMultiplicative _ _
  cofibrations_respectsIso := MorphismProperty.Prod.respectsIso _ _
  weakEquivalences_isMultiplicative := MorphismProperty.Prod.isMultiplicative _ _
  weakEquivalences_respectsIso := MorphismProperty.Prod.respectsIso _ _
  zero_isCofibration := fun X f => by
    have hProd :=
      (isZero_prod_iff (C := C) (D := D)).mp (isZero_zero (C × D))
    have hZ1 := hProd.1
    have hZ2 := hProd.2
    refine ⟨?_, ?_⟩
    · let e1 := hZ1.iso (isZero_zero C)
      have hg1 : WaldhausenCategoryWithoutGluing.cofibrations (C := C) (e1.inv ≫ f.1) :=
        WaldhausenCategoryWithoutGluing.zero_isCofibration _ _
      have hEq : e1.hom ≫ (e1.inv ≫ f.1) = f.1 := by simp
      have hMem := MorphismProperty.RespectsIso.precomp _ e1.hom _ hg1
      rwa [hEq] at hMem
    · let e2 := hZ2.iso (isZero_zero D)
      have hg2 : WaldhausenCategoryWithoutGluing.cofibrations (C := D) (e2.inv ≫ f.2) :=
        WaldhausenCategoryWithoutGluing.zero_isCofibration _ _
      have hEq : e2.hom ≫ (e2.inv ≫ f.2) = f.2 := by simp
      have hMem := MorphismProperty.RespectsIso.precomp _ e2.hom _ hg2
      rwa [hEq] at hMem
  cofibration_pushout := fun {X Y} i hi X' f => by
    obtain ⟨P1, inl1, inr1, hpush1, hcof1⟩ :=
      WaldhausenCategoryWithoutGluing.cofibration_pushout (C := C) i.1 hi.1 X'.1 f.1
    obtain ⟨P2, inl2, inr2, hpush2, hcof2⟩ :=
      WaldhausenCategoryWithoutGluing.cofibration_pushout (C := D) i.2 hi.2 X'.2 f.2
    exact ⟨(P1, P2), Prod.mkHom inl1 inl2, Prod.mkHom inr1 inr2,
      (isPushout_prod_iff (C := C) (D := D)).mpr ⟨hpush1, hpush2⟩,
      ⟨hcof1, hcof2⟩⟩

/-- Componentwise cofibration characterization for the product Waldhausen structure. -/
@[simp]
theorem isCofibration_prod_iff {X Y : C × D} (f : X ⟶ Y) :
    @IsCofibration (C × D) _ _ prodWaldhausen X Y f ↔
      IsCofibration (C := C) f.1 ∧ IsCofibration (C := D) f.2 :=
  Iff.rfl

/-- Componentwise weak-equivalence characterization for the product Waldhausen structure. -/
@[simp]
theorem isWeakEquivalence_prod_iff {X Y : C × D} (f : X ⟶ Y) :
    @IsWeakEquivalence (C × D) _ _ prodWaldhausen X Y f ↔
      IsWeakEquivalence (C := C) f.1 ∧ IsWeakEquivalence (C := D) f.2 :=
  Iff.rfl

/-- Cofibration sequences in the product are componentwise. -/
theorem isCofibrationSequence_prod_iff {X Y Z : C × D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    @IsCofibrationSequence (C × D) _ _ prodWaldhausen X Y Z f g ↔
      IsCofibrationSequence (C := C) f.1 g.1 ∧ IsCofibrationSequence (C := D) f.2 g.2 := by
  constructor
  · rintro ⟨hf, h, q, hPush⟩
    have hPush12 := (isPushout_prod_iff (C := C) (D := D)).mp hPush
    have h1 := hPush12.1
    have h2 := hPush12.2
    have hProd :=
      (isZero_prod_iff (C := C) (D := D)).mp (isZero_zero (C × D))
    have hZ1 := hProd.1
    have hZ2 := hProd.2
    refine ⟨⟨hf.1, (isZero_zero C).from_ _,
      (isZero_zero C).to_ _, ?_⟩,
      ⟨hf.2, (isZero_zero D).from_ _,
      (isZero_zero D).to_ _, ?_⟩⟩
    · exact h1.of_iso (Iso.refl _) (hZ1.iso (isZero_zero C)) (Iso.refl _)
        (Iso.refl _) ((isZero_zero C).eq_of_tgt _ _) (by simp)
        (hZ1.eq_of_src _ _) (by simp)
    · exact h2.of_iso (Iso.refl _) (hZ2.iso (isZero_zero D)) (Iso.refl _)
        (Iso.refl _) ((isZero_zero D).eq_of_tgt _ _) (by simp)
        (hZ2.eq_of_src _ _) (by simp)
  · rintro ⟨⟨hf1, hC, qC, hPushC⟩, ⟨hf2, hD, qD, hPushD⟩⟩
    have hProd :=
      (isZero_prod_iff (C := C) (D := D)).mp (isZero_zero (C × D))
    have hZ1 := hProd.1
    have hZ2 := hProd.2
    have hPushC' : IsPushout (hZ1.from_ X.1) f.1 (hZ1.to_ Z.1) g.1 :=
      hPushC.of_iso (Iso.refl _) ((isZero_zero C).iso hZ1) (Iso.refl _)
        (Iso.refl _) (hZ1.eq_of_tgt _ _) (by simp)
        ((isZero_zero C).eq_of_src _ _) (by simp)
    have hPushD' : IsPushout (hZ2.from_ X.2) f.2 (hZ2.to_ Z.2) g.2 :=
      hPushD.of_iso (Iso.refl _) ((isZero_zero D).iso hZ2) (Iso.refl _)
        (Iso.refl _) (hZ2.eq_of_tgt _ _) (by simp)
        ((isZero_zero D).eq_of_src _ _) (by simp)
    refine ⟨⟨hf1, hf2⟩, Prod.mkHom (hZ1.from_ X.1) (hZ2.from_ X.2),
      Prod.mkHom (hZ1.to_ Z.1) (hZ2.to_ Z.2), ?_⟩
    exact (isPushout_prod_iff (C := C) (D := D)).mpr ⟨hPushC', hPushD'⟩

end CategoryTheory
