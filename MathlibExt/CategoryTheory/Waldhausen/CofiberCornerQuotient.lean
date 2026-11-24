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
# Quotient pushouts from actual cofiber corners

For a map between two cofiber sequences, the pushout corner of the first
arrows has the original source quotient as its quotient by the new source.
The induced map between the two quotients is a cobase change of the corner
map. A cofibration corner therefore gives a cofibration quotient map.

The quotient square is derived from the two actual cofiber rows and their
corner presentation. The argument uses the Waldhausen pushout axioms and
zero-object uniqueness, with no additive or exact-category structure.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The original source quotient is the quotient of the actual corner by
the new source, and its map to the target quotient is a cobase change of
the corner map. -/
theorem cofiberCorner_quotient_pushout
    {A B Q A' B' Q' P : C}
    {i : A ⟶ B} {q : B ⟶ Q} {i' : A' ⟶ B'} {q' : B' ⟶ Q'}
    (hSeq : IsCofiberSequence i q) (hSeq' : IsCofiberSequence i' q')
    (a : A ⟶ A') (b : B ⟶ B') (c : Q ⟶ Q')
    {inB : B ⟶ P} {inA : A' ⟶ P} {d : P ⟶ B'}
    (hP : IsPushout i a inB inA)
    (hinBd : inB ≫ d = b) (hinAd : inA ≫ d = i')
    (hqc : q ≫ c = b ≫ q') :
    ∃ e : P ⟶ Q, inB ≫ e = q ∧
      IsCofiberSequence inA e ∧ IsPushout d e q' c := by
  obtain ⟨hi, zS, uS, hS⟩ := hSeq
  obtain ⟨_, zT, uT, hT⟩ := hSeq'
  have hz : a ≫ zT = zS := (isZero_zero C).eq_of_tgt _ _
  have hdesc : i ≫ q = a ≫ (zT ≫ uS) := by
    rw [← Category.assoc, hz]
    exact hS.w.symm
  let e : P ⟶ Q := hP.desc q (zT ≫ uS) hdesc
  have hinBe : inB ≫ e = q := hP.inl_desc _ _ _
  have hinAe : inA ≫ e = zT ≫ uS := hP.inr_desc _ _ _
  have hOuter : IsPushout i (a ≫ zT) (inB ≫ e) uS := by
    rw [hz, hinBe]
    exact hS.flip
  have hE : IsPushout inA zT e uS := hOuter.of_top hinAe hP
  have hinA : IsCofibration inA :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout hP.flip hi
  have hu : uS ≫ c = uT := (isZero_zero C).eq_of_src _ _
  have hcomm : d ≫ q' = e ≫ c := by
    apply hP.hom_ext
    · calc
        inB ≫ (d ≫ q') = (inB ≫ d) ≫ q' :=
          (Category.assoc _ _ _).symm
        _ = b ≫ q' := by rw [hinBd]
        _ = q ≫ c := hqc.symm
        _ = (inB ≫ e) ≫ c := by rw [hinBe]
        _ = inB ≫ (e ≫ c) := Category.assoc _ _ _
    · calc
        inA ≫ (d ≫ q') = (inA ≫ d) ≫ q' :=
          (Category.assoc _ _ _).symm
        _ = i' ≫ q' := by rw [hinAd]
        _ = zT ≫ uT := hT.w.symm
        _ = zT ≫ (uS ≫ c) := by rw [hu]
        _ = (zT ≫ uS) ≫ c := (Category.assoc _ _ _).symm
        _ = (inA ≫ e) ≫ c := by rw [hinAe]
        _ = inA ≫ (e ≫ c) := Category.assoc _ _ _
  have hOuter' : IsPushout (inA ≫ d) zT q' (uS ≫ c) := by
    rw [hinAd, hu]
    exact hT.flip
  have hQuotient : IsPushout d e q' c := hOuter'.of_left hcomm hE
  exact ⟨e, hinBe, ⟨hinA, zT, uS, hE.flip⟩, hQuotient⟩

/-- A cofibration corner gives a cofibration quotient map by the derived
quotient pushout square. -/
theorem cofiberCorner_quotient_isCofibration
    {A B Q A' B' Q' P : C}
    {i : A ⟶ B} {q : B ⟶ Q} {i' : A' ⟶ B'} {q' : B' ⟶ Q'}
    (hSeq : IsCofiberSequence i q) (hSeq' : IsCofiberSequence i' q')
    (a : A ⟶ A') (b : B ⟶ B') (c : Q ⟶ Q')
    {inB : B ⟶ P} {inA : A' ⟶ P} {d : P ⟶ B'}
    (hP : IsPushout i a inB inA)
    (hinBd : inB ≫ d = b) (hinAd : inA ≫ d = i')
    (hqc : q ≫ c = b ≫ q') (hd : IsCofibration d) :
    IsCofibration c := by
  obtain ⟨e, _, _, hQuotient⟩ :=
    cofiberCorner_quotient_pushout C hSeq hSeq' a b c hP hinBd hinAd hqc
  exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout hQuotient.flip hd

/-- The quotient map of a relative cofibration of actual cofibration
arrows is a cofibration whenever the quotient rows and map commute. -/
theorem IsRelativeCofibration.quotient
    {X Y : CofibrationArrow C} {α : X ⟶ Y}
    {Q Q' : C} {q : X.right ⟶ Q} {q' : Y.right ⟶ Q'}
    (h : IsRelativeCofibration C α)
    (hSeq : IsCofiberSequence X.hom q) (hSeq' : IsCofiberSequence Y.hom q')
    {c : Q ⟶ Q'} (hqc : q ≫ c = α.right ≫ q') :
    IsCofibration c := by
  obtain ⟨_, P, inB, inA, d, hP, hinBd, hinAd, hd⟩ := h
  exact cofiberCorner_quotient_isCofibration C hSeq hSeq'
    α.left α.right c hP hinBd hinAd hqc hd

end CategoryTheory.Waldhausen
