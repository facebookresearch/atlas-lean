/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.CofibrationArrow
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Horizontal pasting of actual cofibration corners

For two adjacent commutative squares, cofibration of both relative
corners implies cofibration of the corner of their horizontal composite.
The outer corner is constructed as a pushout of the second top arrow.
Its map to the second corner is a cobase change of the first corner map.

Only pushouts along base cofibrations and closure under composition are
used. The result selects no global pushout or Waldhausen structure.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Two adjacent actual cofibration corners give an actual cofibration
corner for their horizontal composite. The second top arrow is the
cofibration along which the new outer corner is constructed. -/
theorem cofibrationCorner_paste_horiz
    {A₀ A₁ A₂ B₀ B₁ B₂ P Q : C}
    {f₀₁ : A₀ ⟶ A₁} {f₁₂ : A₁ ⟶ A₂}
    {g₀₁ : B₀ ⟶ B₁} {g₁₂ : B₁ ⟶ B₂}
    {a₀ : A₀ ⟶ B₀} {a₁ : A₁ ⟶ B₁} {a₂ : A₂ ⟶ B₂}
    {p₁ : A₁ ⟶ P} {p₀ : B₀ ⟶ P} {dP : P ⟶ B₁}
    {q₂ : A₂ ⟶ Q} {q₁ : B₁ ⟶ Q} {dQ : Q ⟶ B₂}
    (hf₁₂ : IsCofibration f₁₂)
    (hP : IsPushout f₀₁ a₀ p₁ p₀)
    (hp₁ : p₁ ≫ dP = a₁) (hp₀ : p₀ ≫ dP = g₀₁)
    (hdP : IsCofibration dP)
    (hQ : IsPushout f₁₂ a₁ q₂ q₁)
    (hq₂ : q₂ ≫ dQ = a₂) (hq₁ : q₁ ≫ dQ = g₁₂)
    (hdQ : IsCofibration dQ) :
    ∃ (R : C) (r₂ : A₂ ⟶ R) (r₀ : B₀ ⟶ R) (dR : R ⟶ B₂),
      IsPushout (f₀₁ ≫ f₁₂) a₀ r₂ r₀ ∧
        r₂ ≫ dR = a₂ ∧ r₀ ≫ dR = g₀₁ ≫ g₁₂ ∧ IsCofibration dR := by
  obtain ⟨R, rP, r₂, hR, _⟩ :=
    WaldhausenCategoryWithoutGluing.cofibration_pushout (C := C) f₁₂ hf₁₂ P p₁
  have hOuter : IsPushout (f₀₁ ≫ f₁₂) a₀ r₂ (p₀ ≫ rP) :=
    hP.paste_horiz hR.flip
  have hagree : f₁₂ ≫ q₂ = p₁ ≫ (dP ≫ q₁) := by
    calc
      f₁₂ ≫ q₂ = a₁ ≫ q₁ := hQ.w
      _ = (p₁ ≫ dP) ≫ q₁ := by rw [hp₁]
      _ = p₁ ≫ (dP ≫ q₁) := Category.assoc _ _ _
  let e : R ⟶ Q := hR.flip.desc q₂ (dP ≫ q₁) hagree
  have hr₂ : r₂ ≫ e = q₂ := hR.flip.inl_desc _ _ _
  have hrP : rP ≫ e = dP ≫ q₁ := hR.flip.inr_desc _ _ _
  have hSecondOuter : IsPushout (p₁ ≫ dP) f₁₂ q₁ (r₂ ≫ e) := by
    rw [hp₁, hr₂]
    exact hQ.flip
  have hE : IsPushout dP rP q₁ e :=
    hSecondOuter.of_left hrP.symm hR
  have he : IsCofibration e :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout hE.flip hdP
  have hdR : IsCofibration (e ≫ dQ) :=
    (WaldhausenCategoryWithoutGluing.cofibrations (C := C)).comp_mem e dQ he hdQ
  refine ⟨R, r₂, p₀ ≫ rP, e ≫ dQ, hOuter, ?_, ?_, hdR⟩
  · rw [← Category.assoc, hr₂, hq₂]
  · calc
      (p₀ ≫ rP) ≫ (e ≫ dQ) = p₀ ≫ ((rP ≫ e) ≫ dQ) := by
        simp only [Category.assoc]
      _ = p₀ ≫ ((dP ≫ q₁) ≫ dQ) := by rw [hrP]
      _ = (p₀ ≫ dP) ≫ (q₁ ≫ dQ) := by simp only [Category.assoc]
      _ = g₀₁ ≫ g₁₂ := by rw [hp₀, hq₁]

end CategoryTheory.Waldhausen
