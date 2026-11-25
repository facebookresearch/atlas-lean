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

public import MathlibExt.CategoryTheory.Waldhausen.CofibrationArrowPushout
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberLevelwiseCofiberRow
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberRelativeZero

import Mathlib.Tactic.FinCases

/-!
# Actual pushouts along general cofiber-sequence cofibrations

The existing relative cofibration-arrow pushout supplies the first two
components. The quotient component cofibration supplies the last component
pushout. The existing levelwise assembler and the original cofiber-row
universal properties construct an actual apex cofiber sequence.

The presentation retains the actual apex, both maps, their three component
pushouts, and the genuine relative cobase leg. The whole raw and cofiber
category universal properties follow from those component pushouts.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

open CofiberSequenceCategory

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- A whole cofiber-sequence pushout whose cobase leg retains the genuine
relative cofibration property and whose three evaluations are pushouts. -/
structure CofiberRelativePushoutPresentation
    {R S T : CofiberSequenceCategory C} (i : R ⟶ S) (g : R ⟶ T) where
  /-- The actual apex cofiber sequence. -/
  apex : CofiberSequenceCategory C
  /-- The cobase leg starting at the second target. -/
  inl : T ⟶ apex
  /-- The other leg starting at the first target. -/
  inr : S ⟶ apex
  /-- The source-component square is a pushout. -/
  sourceIsPushout :
    IsPushout ((source C).map g) ((source C).map i)
      ((source C).map inl) ((source C).map inr)
  /-- The middle-component square is a pushout. -/
  middleIsPushout :
    IsPushout ((middle C).map g) ((middle C).map i)
      ((middle C).map inl) ((middle C).map inr)
  /-- The quotient-component square is a pushout. -/
  quotientIsPushout :
    IsPushout ((quotient C).map g) ((quotient C).map i)
      ((quotient C).map inl) ((quotient C).map inr)
  /-- The cobase leg is a genuine relative cofiber-sequence cofibration. -/
  inlRelative : relativeCofibrations C inl

namespace CofiberRelativePushoutPresentation

variable {C}
variable {R S T : CofiberSequenceCategory C} {i : R ⟶ S} {g : R ⟶ T}

/-- The three component pushouts give the whole raw composable-arrow
pushout, on the original underlying maps. -/
theorem forgetIsPushout (P : CofiberRelativePushoutPresentation C i g) :
    IsPushout g.hom i.hom P.inl.hom P.inr.hom := by
  apply IsPushout.of_forall_isPushout_app
  intro k
  fin_cases k
  · change IsPushout ((source C).map g) ((source C).map i)
      ((source C).map P.inl) ((source C).map P.inr)
    exact P.sourceIsPushout
  · change IsPushout ((middle C).map g) ((middle C).map i)
      ((middle C).map P.inl) ((middle C).map P.inr)
    exact P.middleIsPushout
  · change IsPushout ((quotient C).map g) ((quotient C).map i)
      ((quotient C).map P.inl) ((quotient C).map P.inr)
    exact P.quotientIsPushout

/-- The raw universal property reflects to the existing full cofiber
subcategory and gives the whole cofiber-sequence pushout. -/
theorem isPushout (P : CofiberRelativePushoutPresentation C i g) :
    IsPushout g i P.inl P.inr := by
  apply IsPushout.of_map_of_faithful (forget C)
  exact P.forgetIsPushout

private theorem isPushout_cocone_pt_aux (P : CofiberRelativePushoutPresentation C i g) :
    P.isPushout.cocone.pt = P.apex := rfl

/-- The actual pushout cocone has exactly the selected presentation apex. -/
theorem isPushout_cocone_pt (P : CofiberRelativePushoutPresentation C i g) :
    P.isPushout.cocone.pt = P.apex :=
  isPushout_cocone_pt_aux P

private theorem isPushout_cocone_ι_aux (P : CofiberRelativePushoutPresentation C i g) :
    P.isPushout.cocone.ι = (PushoutCocone.mk P.inl P.inr P.isPushout.w).ι := rfl

/-- The actual cocone legs are the literal legs of the same presentation,
with the same original pushout-square equation. -/
theorem isPushout_cocone_ι (P : CofiberRelativePushoutPresentation C i g) :
    P.isPushout.cocone.ι = (PushoutCocone.mk P.inl P.inr P.isPushout.w).ι :=
  isPushout_cocone_ι_aux P

/-- The original pushout cocone component with its codomain stated as
exactly the actual presentation apex. -/
noncomputable def coconeLeg (P : CofiberRelativePushoutPresentation C i g)
    (j : WalkingSpan) : (span g i).obj j ⟶ P.apex :=
  P.isPushout.cocone.ι.app j

private theorem isPushout_cocone_ι_app_aux (P : CofiberRelativePushoutPresentation C i g)
    (j : WalkingSpan) :
    P.isPushout.cocone.ι.app j = P.coconeLeg j := rfl

/-- Pointwise computation of the actual cocone leg, preserving the
actual-apex codomain rather than rewriting a whole natural transformation. -/
theorem isPushout_cocone_ι_app (P : CofiberRelativePushoutPresentation C i g)
    (j : WalkingSpan) :
    P.isPushout.cocone.ι.app j = P.coconeLeg j :=
  isPushout_cocone_ι_app_aux P j

private theorem coconeLeg_left_aux (P : CofiberRelativePushoutPresentation C i g) :
    P.coconeLeg WalkingSpan.left = P.inl := by
  unfold coconeLeg
  rfl

/-- The left actual-apex cocone leg is the original cobase map. -/
theorem coconeLeg_left (P : CofiberRelativePushoutPresentation C i g) :
    P.coconeLeg WalkingSpan.left = P.inl :=
  coconeLeg_left_aux P

private theorem coconeLeg_right_aux (P : CofiberRelativePushoutPresentation C i g) :
    P.coconeLeg WalkingSpan.right = P.inr := by
  unfold coconeLeg
  rfl

/-- The right actual-apex cocone leg is the original other map. -/
theorem coconeLeg_right (P : CofiberRelativePushoutPresentation C i g) :
    P.coconeLeg WalkingSpan.right = P.inr :=
  coconeLeg_right_aux P

private theorem coconeLeg_comp_aux (P : CofiberRelativePushoutPresentation C i g)
    (j : WalkingSpan) {Z : CofiberSequenceCategory C} (h : P.apex ⟶ Z) :
    P.isPushout.cocone.ι.app j ≫ h = P.coconeLeg j ≫ h := by
  unfold coconeLeg
  rfl

/-- Composing the original cocone component with an actual-apex map
normalizes the entire composition, including its middle object. -/
theorem coconeLeg_comp (P : CofiberRelativePushoutPresentation C i g)
    (j : WalkingSpan) {Z : CofiberSequenceCategory C} (h : P.apex ⟶ Z) :
    P.isPushout.cocone.ι.app j ≫ h = P.coconeLeg j ≫ h :=
  coconeLeg_comp_aux P j h

private theorem comp_coconeLeg_aux (P : CofiberRelativePushoutPresentation C i g)
    (j : WalkingSpan) {Z : CofiberSequenceCategory C} (h : Z ⟶ (span g i).obj j) :
    h ≫ P.isPushout.cocone.ι.app j = h ≫ P.coconeLeg j := by
  unfold coconeLeg
  rfl

/-- Precomposing an original cocone component normalizes the whole
composition to the same actual presentation apex. -/
theorem comp_coconeLeg (P : CofiberRelativePushoutPresentation C i g)
    (j : WalkingSpan) {Z : CofiberSequenceCategory C} (h : Z ⟶ (span g i).obj j) :
    h ≫ P.isPushout.cocone.ι.app j = h ≫ P.coconeLeg j :=
  comp_coconeLeg_aux P j h

/-- Construct the whole general extension pushout from the actual
relative cofibration and the base Waldhausen pushout axioms. -/
noncomputable def ofRelativeCofibration
    (i : R ⟶ S) (g : R ⟶ T) (hi : relativeCofibrations C i) :
    CofiberRelativePushoutPresentation C i g :=
  Classical.choice <| by
    let rArrow : Waldhausen.CofibrationArrow C :=
      MorphismProperty.Arrow.mk (R.obj.map' 0 1) R.property.1
    let sArrow : Waldhausen.CofibrationArrow C :=
      MorphismProperty.Arrow.mk (S.obj.map' 0 1) S.property.1
    let tArrow : Waldhausen.CofibrationArrow C :=
      MorphismProperty.Arrow.mk (T.obj.map' 0 1) T.property.1
    let iArrow : rArrow ⟶ sArrow :=
      MorphismProperty.Arrow.homMk (i.hom.app (0 : Fin 3)) (i.hom.app (1 : Fin 3))
        (i.hom.naturality (homOfLE (show (0 : Fin 3) ≤ 1 from by decide))).symm
    let gArrow : rArrow ⟶ tArrow :=
      MorphismProperty.Arrow.homMk (g.hom.app (0 : Fin 3)) (g.hom.app (1 : Fin 3))
        (g.hom.naturality (homOfLE (show (0 : Fin 3) ≤ 1 from by decide))).symm
    have hiArrow : Waldhausen.IsRelativeCofibration C iArrow := by
      change IsCofibration (i.hom.app (0 : Fin 3)) ∧
        ∃ (Q : C) (inB : R.obj.obj' 1 ⟶ Q) (inA : S.obj.obj' 0 ⟶ Q)
          (d : Q ⟶ S.obj.obj' 1),
          IsPushout (R.obj.map' 0 1) (i.hom.app (0 : Fin 3)) inB inA ∧
            inB ≫ d = i.hom.app (1 : Fin 3) ∧
            inA ≫ d = S.obj.map' 0 1 ∧ IsCofibration d
      exact (mem_relativeCofibrations_raw_iff C i).mp hi
    let P := Waldhausen.CofibrationArrowPushoutPresentation.ofRelativeCofibration
      (C := C) iArrow gArrow hiArrow
    have hiQuotient : IsCofibration (i.hom.app (2 : Fin 3)) :=
      (relativeCofibrations_components C i hi).2.2
    obtain ⟨Q, inT2, inS2, hQ, _⟩ :=
      WaldhausenCategoryWithoutGluing.cofibration_pushout (C := C)
        (i.hom.app (2 : Fin 3)) hiQuotient (T.obj.obj' 2) (g.hom.app (2 : Fin 3))
    let D : LevelwisePushoutData C :=
      { R := R.obj
        S := T.obj
        T := S.obj
        RS := g.hom
        RT := i.hom
        P0 := P.apex.left
        P1 := P.apex.right
        P2 := Q
        inlS0 := P.inl.left
        inrT0 := P.inr.left
        inlS1 := P.inl.right
        inrT1 := P.inr.right
        inlS2 := inT2
        inrT2 := inS2
        isPushout0 := by
          change IsPushout (g.hom.app (0 : Fin 3)) (i.hom.app (0 : Fin 3))
            P.inl.left P.inr.left
          exact P.isPushout_left
        isPushout1 := by
          change IsPushout (g.hom.app (1 : Fin 3)) (i.hom.app (1 : Fin 3))
            P.inl.right P.inr.right
          exact P.isPushout_right
        isPushout2 := hQ }
    have h01 : D.inducedMap01 = P.apex.hom := by
      apply D.isPushout0.hom_ext
      · exact (D.isPushout0.inl_desc _ _ _).trans P.inl.w.symm
      · exact (D.isPushout0.inr_desc _ _ _).trans P.inr.w.symm
    have hFirst : IsCofibration D.inducedMap01 := by
      rw [h01]
      exact P.apex.prop
    have hRow : cofiberSequenceProperty C D.assembled :=
      LevelwisePushoutData.isCofiberSequence (C := C) D
        R.property T.property S.property hFirst
    let apex : CofiberSequenceCategory C := ⟨D.assembled, hRow⟩
    let inl : T ⟶ apex := ⟨D.legS⟩
    let inr : S ⟶ apex := ⟨D.legT⟩
    have hInl : relativeCofibrations C inl := by
      apply (mem_relativeCofibrations_raw_iff C inl).mpr
      obtain ⟨hLeft, K, inB, inA, d, hCorner, hinBd, hinAd, hd⟩ := P.inl_relative
      refine ⟨?_, K, inB, inA, d, ?_, ?_, ?_, hd⟩
      · change IsCofibration P.inl.left
        exact hLeft
      · change IsPushout (T.obj.map' 0 1) P.inl.left inB inA
        exact hCorner
      · change inB ≫ d = P.inl.right
        exact hinBd
      · change inA ≫ d = D.inducedMap01
        exact hinAd.trans h01.symm
    exact ⟨{
      apex := apex
      inl := inl
      inr := inr
      sourceIsPushout := by
        change IsPushout (g.hom.app (0 : Fin 3)) (i.hom.app (0 : Fin 3))
          D.inlS0 D.inrT0
        exact D.isPushout0
      middleIsPushout := by
        change IsPushout (g.hom.app (1 : Fin 3)) (i.hom.app (1 : Fin 3))
          D.inlS1 D.inrT1
        exact D.isPushout1
      quotientIsPushout := by
        change IsPushout (g.hom.app (2 : Fin 3)) (i.hom.app (2 : Fin 3))
          D.inlS2 D.inrT2
        exact D.isPushout2
      inlRelative := hInl }⟩

end CofiberRelativePushoutPresentation

end CategoryTheory.Waldhausen.SConstruction
