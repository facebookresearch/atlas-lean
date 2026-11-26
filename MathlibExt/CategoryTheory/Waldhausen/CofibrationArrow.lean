/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import MathlibExt.CategoryTheory.Waldhausen.Basic

/-!
# Cofibration arrows and relative cofibrations

This file packages Waldhausen's arrow category `Ar C` and cofibration-arrow
category `F₁ C` using Mathlib's existing `MorphismProperty.Arrow` carrier.
It defines pointwise morphism properties and the genuine relative/latching
cofibration property on a commutative square.

Only the elementary E0 algebra is provided: identity, composition,
isomorphism closure, pointwise consequences, and named zero-object values.
No zero object or Waldhausen structure is installed globally.  Coproducts,
gluing, cylinders, Cyl-I, Stage constructions, and Approximation results are
outside this file.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory.Waldhausen

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

/-- Waldhausen's category `F₁ C`: cofibrations as objects and arbitrary
commutative squares as morphisms. -/
abbrev CofibrationArrow : Type (max u v) :=
  (WaldhausenCategoryWithoutGluing.cofibrations (C := C)).Arrow
    (⊤ : MorphismProperty C) (⊤ : MorphismProperty C)

/-- Forget a cofibration arrow to its underlying arrow. -/
abbrev cofibrationArrowForget :
    CofibrationArrow C ⥤ Arrow C :=
  MorphismProperty.Arrow.forget
    (WaldhausenCategoryWithoutGluing.cofibrations (C := C))
    (⊤ : MorphismProperty C) (⊤ : MorphismProperty C)

/-- Pointwise cofibrations between arrows. -/
def arrowCofibrations : MorphismProperty (Arrow C) :=
  ((WaldhausenCategoryWithoutGluing.cofibrations (C := C)).inverseImage
      Arrow.leftFunc) ⊓
    ((WaldhausenCategoryWithoutGluing.cofibrations (C := C)).inverseImage
      Arrow.rightFunc)

/-- Pointwise weak equivalences between arrows. -/
def arrowWeakEquivalences : MorphismProperty (Arrow C) :=
  ((WaldhausenCategoryWithoutGluing.weakEquivalences (C := C)).inverseImage
      Arrow.leftFunc) ⊓
    ((WaldhausenCategoryWithoutGluing.weakEquivalences (C := C)).inverseImage
      Arrow.rightFunc)

/-- Pointwise weak equivalences between cofibration arrows. -/
def cofibrationArrowWeakEquivalences :
    MorphismProperty (CofibrationArrow C) :=
  (arrowWeakEquivalences C).inverseImage (cofibrationArrowForget C)

/-- A relative cofibration of cofibration arrows.

For `α : X ⟶ Y`, the left component is a cofibration and the induced map
from `X.right ⊔_[X.left] Y.left` to `Y.right` is a cofibration. -/
def IsRelativeCofibration {X Y : CofibrationArrow C}
    (α : X ⟶ Y) : Prop :=
  IsCofibration α.left ∧
    ∃ (P : C) (inB : X.right ⟶ P) (inA : Y.left ⟶ P)
      (d : P ⟶ Y.right),
      IsPushout X.hom α.left inB inA ∧
        inB ≫ d = α.right ∧
        inA ≫ d = Y.hom ∧
        IsCofibration d

/-- Relative cofibrations as a morphism property on `F₁ C`. -/
def cofibrationArrowCofibrations :
    MorphismProperty (CofibrationArrow C) :=
  fun _ _ α => IsRelativeCofibration C α

instance arrowCofibrations_isMultiplicative :
    (arrowCofibrations C).IsMultiplicative :=
  inferInstanceAs
    ((((WaldhausenCategoryWithoutGluing.cofibrations (C := C)).inverseImage
      Arrow.leftFunc) ⊓
      ((WaldhausenCategoryWithoutGluing.cofibrations (C := C)).inverseImage
        Arrow.rightFunc)).IsMultiplicative)

instance arrowCofibrations_respectsIso :
    (arrowCofibrations C).RespectsIso :=
  inferInstanceAs
    ((((WaldhausenCategoryWithoutGluing.cofibrations (C := C)).inverseImage
      Arrow.leftFunc) ⊓
      ((WaldhausenCategoryWithoutGluing.cofibrations (C := C)).inverseImage
        Arrow.rightFunc)).RespectsIso)

instance arrowWeakEquivalences_isMultiplicative :
    (arrowWeakEquivalences C).IsMultiplicative :=
  inferInstanceAs
    ((((WaldhausenCategoryWithoutGluing.weakEquivalences (C := C)).inverseImage
      Arrow.leftFunc) ⊓
      ((WaldhausenCategoryWithoutGluing.weakEquivalences (C := C)).inverseImage
        Arrow.rightFunc)).IsMultiplicative)

instance arrowWeakEquivalences_respectsIso :
    (arrowWeakEquivalences C).RespectsIso :=
  inferInstanceAs
    ((((WaldhausenCategoryWithoutGluing.weakEquivalences (C := C)).inverseImage
      Arrow.leftFunc) ⊓
      ((WaldhausenCategoryWithoutGluing.weakEquivalences (C := C)).inverseImage
        Arrow.rightFunc)).RespectsIso)

instance cofibrationArrowWeakEquivalences_isMultiplicative :
    (cofibrationArrowWeakEquivalences C).IsMultiplicative :=
  inferInstanceAs
    (((arrowWeakEquivalences C).inverseImage
      (cofibrationArrowForget C)).IsMultiplicative)

instance cofibrationArrowWeakEquivalences_respectsIso :
    (cofibrationArrowWeakEquivalences C).RespectsIso :=
  inferInstanceAs
    (((arrowWeakEquivalences C).inverseImage
      (cofibrationArrowForget C)).RespectsIso)

/-- Identity squares are relative cofibrations. -/
theorem IsRelativeCofibration.id (X : CofibrationArrow C) :
    IsRelativeCofibration C (𝟙 X) := by
  refine ⟨(WaldhausenCategoryWithoutGluing.cofibrations (C := C)).id_mem X.left,
    X.right, 𝟙 X.right, X.hom, 𝟙 X.right, ?_, ?_, ?_, ?_⟩
  · exact IsPushout.of_id_snd
  · simp
  · simp
  · exact (WaldhausenCategoryWithoutGluing.cofibrations (C := C)).id_mem X.right

/-- Relative cofibrations are closed under composition. -/
theorem IsRelativeCofibration.comp
    {X Y Z : CofibrationArrow C} (α : X ⟶ Y) (β : Y ⟶ Z)
    (hα : IsRelativeCofibration C α)
    (hβ : IsRelativeCofibration C β) :
    IsRelativeCofibration C (α ≫ β) := by
  obtain ⟨hαl, P, pB, pA, dα, hpushα, hpB, hpA, hdα⟩ := hα
  obtain ⟨hβl, Q, qB, qA, dβ, hpushβ, hqB, hqA, hdβ⟩ := hβ
  refine ⟨(WaldhausenCategoryWithoutGluing.cofibrations (C := C)).comp_mem
    α.left β.left hαl hβl, ?_⟩
  have hpAcof : IsCofibration pA :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout
      hpushα.flip X.prop
  obtain ⟨R, rZ, rP, hpushR, _⟩ :=
    WaldhausenCategoryWithoutGluing.cofibration_pushout (C := C)
      pA hpAcof Z.left β.left
  have hpush :
      IsPushout X.hom (α.left ≫ β.left) (pB ≫ rP) rZ := by
    exact hpushα.paste_vert hpushR.flip
  have hagree : β.left ≫ qA = pA ≫ (dα ≫ qB) := by
    calc
      β.left ≫ qA = Y.hom ≫ qB := hpushβ.w.symm
      _ = (pA ≫ dα) ≫ qB := by rw [hpA]
      _ = pA ≫ (dα ≫ qB) := Category.assoc _ _ _
  let e : R ⟶ Q := hpushR.desc qA (dα ≫ qB) hagree
  have hrZ : rZ ≫ e = qA := hpushR.inl_desc _ _ _
  have hrP : rP ≫ e = dα ≫ qB := hpushR.inr_desc _ _ _
  have houter : IsPushout β.left (pA ≫ dα) (rZ ≫ e) qB := by
    rw [hpA, hrZ]
    exact hpushβ.flip
  have hlower : IsPushout rP dα e qB :=
    houter.of_top hrP hpushR
  have he : IsCofibration e :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout hlower hdα
  have hedβ : IsCofibration (e ≫ dβ) :=
    (WaldhausenCategoryWithoutGluing.cofibrations (C := C)).comp_mem e dβ he hdβ
  refine ⟨R, pB ≫ rP, rZ, e ≫ dβ, hpush, ?_, ?_, hedβ⟩
  · change (pB ≫ rP) ≫ (e ≫ dβ) = α.right ≫ β.right
    calc
      (pB ≫ rP) ≫ (e ≫ dβ) =
          pB ≫ ((rP ≫ e) ≫ dβ) := by simp only [Category.assoc]
      _ = pB ≫ ((dα ≫ qB) ≫ dβ) := by rw [hrP]
      _ = (pB ≫ dα) ≫ (qB ≫ dβ) := by simp only [Category.assoc]
      _ = α.right ≫ β.right := by rw [hpB, hqB]
  · rw [← Category.assoc, hrZ, hqA]

instance cofibrationArrowCofibrations_isMultiplicative :
    (cofibrationArrowCofibrations C).IsMultiplicative where
  id_mem X := IsRelativeCofibration.id C X
  comp_mem α β := IsRelativeCofibration.comp C α β

/-- Every isomorphism of cofibration arrows is a relative cofibration. -/
theorem IsRelativeCofibration.of_isIso
    {X Y : CofibrationArrow C} (α : X ⟶ Y) [IsIso α] :
    IsRelativeCofibration C α := by
  let L := cofibrationArrowForget C ⋙ Arrow.leftFunc
  let R := cofibrationArrowForget C ⋙ Arrow.rightFunc
  let _ : IsIso α.left := by
    change IsIso (L.map α)
    infer_instance
  let _ : IsIso α.right := by
    change IsIso (R.map α)
    infer_instance
  refine ⟨(WaldhausenCategoryWithoutGluing.cofibrations (C := C)).of_isIso α.left,
    Y.right, α.right, Y.hom, 𝟙 Y.right, ?_, ?_, ?_, ?_⟩
  · exact IsPushout.of_vert_isIso
      ⟨(MorphismProperty.Arrow.w α).symm⟩
  · simp
  · simp
  · exact (WaldhausenCategoryWithoutGluing.cofibrations (C := C)).id_mem Y.right

instance cofibrationArrowCofibrations_respectsIso :
    (cofibrationArrowCofibrations C).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition <| by
    intro X Y α hα
    let _ : IsIso α := hα
    exact IsRelativeCofibration.of_isIso C α

/-- The right component of a relative cofibration is a cofibration. -/
theorem IsRelativeCofibration.right
    {X Y : CofibrationArrow C} {α : X ⟶ Y}
    (h : IsRelativeCofibration C α) :
    IsCofibration α.right := by
  obtain ⟨hleft, P, inB, inA, d, hpush, hinB, hinA, hd⟩ := h
  have hInB : IsCofibration inB :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout hpush hleft
  rw [← hinB]
  exact (WaldhausenCategoryWithoutGluing.cofibrations (C := C)).comp_mem
    inB d hInB hd

/-- Every relative cofibration is pointwise a cofibration. -/
theorem IsRelativeCofibration.pointwise
    {X Y : CofibrationArrow C} {α : X ⟶ Y}
    (h : IsRelativeCofibration C α) :
    arrowCofibrations C ((cofibrationArrowForget C).map α) :=
  ⟨h.1, h.right C⟩

/-- The identity arrow on the selected zero object. -/
noncomputable def arrowZero : Arrow C :=
  Arrow.mk (𝟙 (0 : C))

omit [WaldhausenCategoryWithoutGluing C] in
/-- `arrowZero` is a zero object of the arrow category. -/
theorem arrowZero_isZero : IsZero (arrowZero C) where
  unique_to X := ⟨{
    default := Arrow.homMk
      ((isZero_zero C).to_ X.left) ((isZero_zero C).to_ X.right)
      (by apply (isZero_zero C).eq_of_src)
    uniq := fun f => Arrow.hom_ext f _
      ((isZero_zero C).eq_of_src _ _)
      ((isZero_zero C).eq_of_src _ _) }⟩
  unique_from X := ⟨{
    default := Arrow.homMk
      ((isZero_zero C).from_ X.left) ((isZero_zero C).from_ X.right)
      (by apply (isZero_zero C).eq_of_tgt)
    uniq := fun f => Arrow.hom_ext f _
      ((isZero_zero C).eq_of_tgt _ _)
      ((isZero_zero C).eq_of_tgt _ _) }⟩

omit [WaldhausenCategoryWithoutGluing C] in
/-- A named zero-object value for local installation on `Arrow C`. -/
theorem arrowHasZeroObject : HasZeroObject (Arrow C) :=
  (arrowZero_isZero C).hasZeroObject

/-- The identity cofibration of the selected zero object. -/
noncomputable def cofibrationArrowZero : CofibrationArrow C :=
  MorphismProperty.Arrow.mk (𝟙 (0 : C))
    ((WaldhausenCategoryWithoutGluing.cofibrations (C := C)).id_mem (0 : C))

/-- `cofibrationArrowZero` is a zero object of `F₁ C`. -/
theorem cofibrationArrowZero_isZero :
    IsZero (cofibrationArrowZero C) := by
  apply IsZero.of_full_of_faithful_of_isZero (cofibrationArrowForget C)
  change IsZero (Arrow.mk (𝟙 (0 : C)))
  exact arrowZero_isZero C

/-- A named zero-object value for local installation on `F₁ C`. -/
theorem cofibrationArrowHasZeroObject :
    HasZeroObject (CofibrationArrow C) :=
  (cofibrationArrowZero_isZero C).hasZeroObject

end CategoryTheory.Waldhausen

end
