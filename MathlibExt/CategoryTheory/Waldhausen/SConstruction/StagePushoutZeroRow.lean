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

public import MathlibExt.CategoryTheory.Waldhausen.CofibrationArrowCobaseChange
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StagePointwisePushout
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberLevelwiseCofiberRow
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageZeroRowCriterion
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# The genuine apex stage of a pointwise stage pushout

The raw initial-row arrows are compared with the existing actual relative
cofibration-arrow pushout through its whole universal property. They are
therefore cofibrations. Their original quotient rows follow from the
general levelwise cofiber theorem. Together with zero diagonals, the
zero-row criterion proves the full apex stage predicate.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

namespace StagePointwisePushoutPresentation

variable {n : ℕ} {A B D : Stage C n} {φ : A ⟶ B} {ψ : A ⟶ D}

private theorem zeroRowMap_cofibration_aux
    (P : StagePointwisePushoutPresentation C φ ψ)
    (hφ : stageCofibrations C n φ) {i j : Fin (n + 1)} (hij : i ≤ j) :
    IsCofibration (P.diagram.map (horiz (Fin.zero_le i) hij)) := by
  let a : Waldhausen.CofibrationArrow C :=
    MorphismProperty.Arrow.mk (A.obj.map (horiz (Fin.zero_le i) hij))
      (A.property.cofiber_triple (Fin.zero_le i) hij).1
  let b : Waldhausen.CofibrationArrow C :=
    MorphismProperty.Arrow.mk (B.obj.map (horiz (Fin.zero_le i) hij))
      (B.property.cofiber_triple (Fin.zero_le i) hij).1
  let d : Waldhausen.CofibrationArrow C :=
    MorphismProperty.Arrow.mk (D.obj.map (horiz (Fin.zero_le i) hij))
      (D.property.cofiber_triple (Fin.zero_le i) hij).1
  let f : a ⟶ b := MorphismProperty.Arrow.homMk
    (Stage.zeroRowApp φ i) (Stage.zeroRowApp φ j)
    (φ.hom.naturality (horiz (Fin.zero_le i) hij)).symm
  let g : a ⟶ d := MorphismProperty.Arrow.homMk
    (Stage.zeroRowApp ψ i) (Stage.zeroRowApp ψ j)
    (ψ.hom.naturality (horiz (Fin.zero_le i) hij)).symm
  have hf : Waldhausen.IsRelativeCofibration C f := by
    refine ⟨Stage.zeroRowApp_isCofibration C φ hφ i, ?_⟩
    obtain ⟨Q, qA, qB, c, hQ, hqA, hqB, hc⟩ := Stage.zeroRowPair_corner C φ hφ hij
    refine ⟨Q, qA, qB, c, ?_, hqA, ?_, hc⟩
    · rw [← MorphismProperty.Comma.Hom.hom_left f]
      simpa only [Stage.zeroRowPairMap_eq, Stage.zeroRowObj, Stage.zeroRowApp,
        a, b, f, MorphismProperty.Arrow.mk, MorphismProperty.Arrow.homMk,
        MorphismProperty.Comma.Hom.hom, Arrow.homMk, Functor.id_obj] using hQ
    · simpa only [Stage.zeroRowPairMap_eq, Stage.zeroRowObj, b,
        MorphismProperty.Arrow.mk, Functor.id_obj] using hqB
  let R := Waldhausen.CofibrationArrowPushoutPresentation.ofRelativeCofibration
    (C := C) f g hf
  let Qraw : Waldhausen.ArrowPushoutPresentation C
      ((Waldhausen.cofibrationArrowForget C).map f)
      ((Waldhausen.cofibrationArrowForget C).map g) :=
    { apex := Arrow.mk (P.diagram.map (horiz (Fin.zero_le i) hij))
      inl := Arrow.homMk
        (P.inl.app (interval 0 i (Fin.zero_le i)))
        (P.inl.app (interval 0 j (Fin.zero_le j)))
        (P.inl.naturality (horiz (Fin.zero_le i) hij)).symm
      inr := Arrow.homMk
        (P.inr.app (interval 0 i (Fin.zero_le i)))
        (P.inr.app (interval 0 j (Fin.zero_le j)))
        (P.inr.naturality (horiz (Fin.zero_le i) hij)).symm
      isPushout_left := P.appIsPushout (interval 0 i (Fin.zero_le i))
      isPushout_right := P.appIsPushout (interval 0 j (Fin.zero_le j))
      inl_cofibration :=
        ⟨P.inl_app_isCofibration hφ _, P.inl_app_isCofibration hφ _⟩ }
  let Qselected : Waldhausen.ArrowPushoutPresentation C
      ((Waldhausen.cofibrationArrowForget C).map f)
      ((Waldhausen.cofibrationArrowForget C).map g) :=
    { apex := (Waldhausen.cofibrationArrowForget C).obj R.apex
      inl := (Waldhausen.cofibrationArrowForget C).map R.inl
      inr := (Waldhausen.cofibrationArrowForget C).map R.inr
      isPushout_left := R.isPushout_left
      isPushout_right := R.isPushout_right
      inl_cofibration := R.inl_relative.pointwise C }
  let e : Arrow.mk R.apex.hom ≅
      Arrow.mk (P.diagram.map (horiz (Fin.zero_le i) hij)) :=
    Qselected.isPushout.isColimit.coconePointUniqueUpToIso Qraw.isPushout.isColimit
  exact ((WaldhausenCategoryWithoutGluing.cofibrations (C := C)).arrow_mk_iso_iff e).mp R.apex.prop

/-- Every original initial-row arrow of the raw apex is a cofibration,
derived from the actual relative-arrow pushout rather than assumed. -/
theorem zeroRowMap_isCofibration
    (P : StagePointwisePushoutPresentation C φ ψ)
    (hφ : stageCofibrations C n φ) {i j : Fin (n + 1)} (hij : i ≤ j) :
    IsCofibration (P.diagram.map (horiz (Fin.zero_le i) hij)) :=
  zeroRowMap_cofibration_aux P hφ hij

/-- Every diagonal of the actual raw apex is zero, since the component
pushout is a pushout of an isomorphism between the source zero diagonals. -/
theorem diag_isZero (P : StagePointwisePushoutPresentation C φ ψ)
    (i : Fin (n + 1)) : IsZero (P.diagram.obj (diag i)) := by
  let : IsIso (φ.hom.app (diag i)) :=
    IsZero.isIso (A.property.diag_isZero i) (B.property.diag_isZero i) _
  let : IsIso (P.inl.app (diag i)) :=
    (P.appIsPushout (diag i)).isIso_inl_of_isIso
  exact (D.property.diag_isZero i).of_iso (asIso (P.inl.app (diag i))).symm

/-- The original zero-row quotient of the actual raw apex is a cofiber
row, by the three component pushouts and original source cofiber rows. -/
theorem zeroRow_isCofiberSequence (P : StagePointwisePushoutPresentation C φ ψ)
    (hφ : stageCofibrations C n φ) {i j : Fin (n + 1)} (hij : i ≤ j) :
    IsCofiberSequence (P.diagram.map (horiz (Fin.zero_le i) hij))
      (P.diagram.map (vert (Fin.zero_le i) hij)) := by
  let E : LevelwisePushoutData C :=
    { R := ComposableArrows.mk₂ (A.obj.map (horiz (Fin.zero_le i) hij))
        (A.obj.map (vert (Fin.zero_le i) hij))
      S := ComposableArrows.mk₂ (D.obj.map (horiz (Fin.zero_le i) hij))
        (D.obj.map (vert (Fin.zero_le i) hij))
      T := ComposableArrows.mk₂ (B.obj.map (horiz (Fin.zero_le i) hij))
        (B.obj.map (vert (Fin.zero_le i) hij))
      RS := ComposableArrows.homMk₂
        (ψ.hom.app (interval 0 i (Fin.zero_le i)))
        (ψ.hom.app (interval 0 j (Fin.zero_le j))) (ψ.hom.app (interval i j hij))
        (ψ.hom.naturality (horiz (Fin.zero_le i) hij))
        (ψ.hom.naturality (vert (Fin.zero_le i) hij))
      RT := ComposableArrows.homMk₂
        (φ.hom.app (interval 0 i (Fin.zero_le i)))
        (φ.hom.app (interval 0 j (Fin.zero_le j))) (φ.hom.app (interval i j hij))
        (φ.hom.naturality (horiz (Fin.zero_le i) hij))
        (φ.hom.naturality (vert (Fin.zero_le i) hij))
      P0 := P.diagram.obj (interval 0 i (Fin.zero_le i))
      P1 := P.diagram.obj (interval 0 j (Fin.zero_le j))
      P2 := P.diagram.obj (interval i j hij)
      inlS0 := P.inl.app (interval 0 i (Fin.zero_le i))
      inrT0 := P.inr.app (interval 0 i (Fin.zero_le i))
      inlS1 := P.inl.app (interval 0 j (Fin.zero_le j))
      inrT1 := P.inr.app (interval 0 j (Fin.zero_le j))
      inlS2 := P.inl.app (interval i j hij)
      inrT2 := P.inr.app (interval i j hij)
      isPushout0 := P.appIsPushout (interval 0 i (Fin.zero_le i))
      isPushout1 := P.appIsPushout (interval 0 j (Fin.zero_le j))
      isPushout2 := P.appIsPushout (interval i j hij) }
  have h01 : E.inducedMap01 = P.diagram.map (horiz (Fin.zero_le i) hij) := by
    apply E.isPushout0.hom_ext
    · exact (E.isPushout0.inl_desc _ _ _).trans
        (P.inl.naturality (horiz (Fin.zero_le i) hij))
    · exact (E.isPushout0.inr_desc _ _ _).trans
        (P.inr.naturality (horiz (Fin.zero_le i) hij))
  have h12 : E.inducedMap12 = P.diagram.map (vert (Fin.zero_le i) hij) := by
    apply E.isPushout1.hom_ext
    · exact (E.isPushout1.inl_desc _ _ _).trans
        (P.inl.naturality (vert (Fin.zero_le i) hij))
    · exact (E.isPushout1.inr_desc _ _ _).trans
        (P.inr.naturality (vert (Fin.zero_le i) hij))
  have hFirst : IsCofibration E.inducedMap01 := by
    rw [h01]
    exact P.zeroRowMap_isCofibration hφ hij
  have hRow := LevelwisePushoutData.isCofiberSequence (C := C) E
    (A.property.cofiber_triple (Fin.zero_le i) hij)
    (D.property.cofiber_triple (Fin.zero_le i) hij)
    (B.property.cofiber_triple (Fin.zero_le i) hij) hFirst
  change IsCofiberSequence E.inducedMap01 E.inducedMap12 at hRow
  rwa [h01, h12] at hRow

/-- The whole raw apex satisfies every finite-stage cofiber triple,
with all arbitrary triples derived from its original zero-row quotients. -/
theorem isStage (P : StagePointwisePushoutPresentation C φ ψ)
    (hφ : stageCofibrations C n φ) : IsStage n P.diagram :=
  isStage_of_zeroRowCofiber P.diagram (P.diag_isZero)
    (fun hij => P.zeroRow_isCofiberSequence hφ hij)

/-- The actual raw cobase leg retains every zero-row relative corner.
This follows by cobase change in the existing cofibration-arrow category. -/
theorem inl_zeroRow_corner (P : StagePointwisePushoutPresentation C φ ψ)
    (hφ : stageCofibrations C n φ) {i j : Fin (n + 1)} (hij : i ≤ j) :
    ∃ (Q : C) (inD : D.zeroRowObj j ⟶ Q)
      (inP : P.diagram.obj (interval 0 i (Fin.zero_le i)) ⟶ Q)
      (c : Q ⟶ P.diagram.obj (interval 0 j (Fin.zero_le j))),
      IsPushout (D.obj.map (horiz (Fin.zero_le i) hij))
          (P.inl.app (interval 0 i (Fin.zero_le i))) inD inP ∧
        inD ≫ c = P.inl.app (interval 0 j (Fin.zero_le j)) ∧
        inP ≫ c = P.diagram.map (horiz (Fin.zero_le i) hij) ∧ IsCofibration c := by
  let a : Waldhausen.CofibrationArrow C :=
    MorphismProperty.Arrow.mk (A.obj.map (horiz (Fin.zero_le i) hij))
      (A.property.cofiber_triple (Fin.zero_le i) hij).1
  let b : Waldhausen.CofibrationArrow C :=
    MorphismProperty.Arrow.mk (B.obj.map (horiz (Fin.zero_le i) hij))
      (B.property.cofiber_triple (Fin.zero_le i) hij).1
  let d : Waldhausen.CofibrationArrow C :=
    MorphismProperty.Arrow.mk (D.obj.map (horiz (Fin.zero_le i) hij))
      (D.property.cofiber_triple (Fin.zero_le i) hij).1
  let p : Waldhausen.CofibrationArrow C :=
    MorphismProperty.Arrow.mk (P.diagram.map (horiz (Fin.zero_le i) hij))
      (P.zeroRowMap_isCofibration hφ hij)
  let f : a ⟶ b := MorphismProperty.Arrow.homMk
    (Stage.zeroRowApp φ i) (Stage.zeroRowApp φ j)
    (φ.hom.naturality (horiz (Fin.zero_le i) hij)).symm
  let g : a ⟶ d := MorphismProperty.Arrow.homMk
    (Stage.zeroRowApp ψ i) (Stage.zeroRowApp ψ j)
    (ψ.hom.naturality (horiz (Fin.zero_le i) hij)).symm
  let l : d ⟶ p := MorphismProperty.Arrow.homMk
    (P.inl.app (interval 0 i (Fin.zero_le i)))
    (P.inl.app (interval 0 j (Fin.zero_le j)))
    (P.inl.naturality (horiz (Fin.zero_le i) hij)).symm
  let r : b ⟶ p := MorphismProperty.Arrow.homMk
    (P.inr.app (interval 0 i (Fin.zero_le i)))
    (P.inr.app (interval 0 j (Fin.zero_le j)))
    (P.inr.naturality (horiz (Fin.zero_le i) hij)).symm
  have hf : Waldhausen.IsRelativeCofibration C f := by
    refine ⟨Stage.zeroRowApp_isCofibration C φ hφ i, ?_⟩
    obtain ⟨Q, qA, qB, c, hQ, hqA, hqB, hc⟩ := Stage.zeroRowPair_corner C φ hφ hij
    refine ⟨Q, qA, qB, c, ?_, hqA, ?_, hc⟩
    · rw [← MorphismProperty.Comma.Hom.hom_left f]
      simpa only [Stage.zeroRowPairMap_eq, Stage.zeroRowObj, Stage.zeroRowApp,
        a, b, f, MorphismProperty.Arrow.mk, MorphismProperty.Arrow.homMk,
        MorphismProperty.Comma.Hom.hom, Arrow.homMk, Functor.id_obj] using hQ
    · simpa only [Stage.zeroRowPairMap_eq, Stage.zeroRowObj, b,
        MorphismProperty.Arrow.mk, Functor.id_obj] using hqB
  let Qraw : Waldhausen.ArrowPushoutPresentation C
      ((Waldhausen.cofibrationArrowForget C).map f)
      ((Waldhausen.cofibrationArrowForget C).map g) :=
    { apex := (Waldhausen.cofibrationArrowForget C).obj p
      inl := (Waldhausen.cofibrationArrowForget C).map l
      inr := (Waldhausen.cofibrationArrowForget C).map r
      isPushout_left := P.appIsPushout (interval 0 i (Fin.zero_le i))
      isPushout_right := P.appIsPushout (interval 0 j (Fin.zero_le j))
      inl_cofibration :=
        ⟨P.inl_app_isCofibration hφ _, P.inl_app_isCofibration hφ _⟩ }
  have hPushout : IsPushout g f l r := by
    apply IsPushout.of_map_of_faithful (Waldhausen.cofibrationArrowForget C)
    exact Qraw.isPushout
  let : MorphismProperty.IsStableUnderCobaseChange
      (fun (X Y : Waldhausen.CofibrationArrow C) (f : X ⟶ Y) =>
        Waldhausen.IsRelativeCofibration C f) := by
    have h := Waldhausen.cofibrationArrowCofibrationsCobaseChange C
    unfold Waldhausen.cofibrationArrowCofibrations at h
    exact h
  have hl : Waldhausen.IsRelativeCofibration C l :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout hPushout hf
  exact hl.2

end StagePointwisePushoutPresentation

end CategoryTheory.Waldhausen.SConstruction
