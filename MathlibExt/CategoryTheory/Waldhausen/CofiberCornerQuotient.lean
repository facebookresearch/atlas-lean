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
# Quotients of cofiber pushout corners

Let C have a zero object and Waldhausen cofibration, weak-equivalence
and cofibration-pushout axioms. For two cofiber sequences A → B → Q and
A′ → B′ → Q′, form the pushout corner P=B⊔_A A′ and its map d:P → B′.
The source quotient Q is also the cofiber of A′ → P.

The square P → B′, P → Q, B′ → Q′, Q → Q′ is a pushout.
Hence a cofibration corner map d gives a cofibration between the quotient
objects. This applies to relative cofibrations of cofibration arrows.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Let C be a category with a zero object and Waldhausen cofibration,
weak-equivalence and cofibration-pushout axioms.
Take cofiber sequences A —i→ B —q→ Q and A′ —i′→ B′ —q′→ Q′.
Let P=B⊔_A A′ have pushout legs inB,inA, and let d:P → B′ satisfy
d∘inB=b and d∘inA=i′ for maps a:A → A′ and b:B → B′.
Let c:Q → Q′ satisfy c∘q=q′∘b.

There is e:P → Q with e∘inB=q, such that A′ —inA→ P —e→ Q is a cofiber sequence and the square with maps d,e,q′,c is a pushout. -/
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

/-- Let C be a category with a zero object and Waldhausen cofibration,
weak-equivalence and cofibration-pushout axioms.
Take cofiber sequences A —i→ B —q→ Q and A′ —i′→ B′ —q′→ Q′.
Let P=B⊔_A A′ have pushout legs inB,inA, and let d:P → B′ satisfy
d∘inB=b and d∘inA=i′ for maps a:A → A′ and b:B → B′.
Let c:Q → Q′ satisfy c∘q=q′∘b.

If the corner map d:P → B′ is a cofibration, then the induced quotient map c:Q → Q′ is a cofibration. -/
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

/-- Let C have a zero object and Waldhausen cofibration, weak-equivalence
and cofibration-pushout axioms. For a relative cofibration square
(a:X₀ → Y₀,b:X₁ → Y₁) between cofibration arrows
i:X₀ → X₁ and j:Y₀ → Y₁, choose cofiber sequences
X₀ —i→ X₁ —q→ Q and Y₀ —j→ Y₁ —q′→ Q′.
If c:Q → Q′ satisfies c∘q=q′∘b, then c is a cofibration. -/
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
