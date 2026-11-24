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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberFunctorStageAdmission
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageEvaluationExactGeneral

/-!
# The original quotient row after a genuine stage cobase change

The original stage zero quotient pushout and genuine stage pushout define
an actual quotient map on the cobase-changed middle. Original pushout
pasting gives its whole zero quotient square. The named general stage
evaluations derive every original component cofiber sequence, and the
genuine first stage cofibration admits the entire relative extension stage.
-/

public section

open CategoryTheory Limits
open scoped ZeroObject

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- A constructed genuine stage pushout and original stage quotient
pushout supply the actual whole quotient and entire relative cofiber stage. -/
theorem GeneralStagePushoutPresentation.existsCofiberRow {n : ℕ}
    {A B T Q : Stage C n} {i : A ⟶ B} {k : A ⟶ T}
    (P : GeneralStagePushoutPresentation C i k) (p : B ⟶ Q)
    (O : Stage C n) (hO : IsZero O) (z : A ⟶ O) (q : O ⟶ Q)
    (hOld : IsPushout z i q p) :
    ∃ g : P.apex ⟶ Q,
      P.inr ≫ g = p ∧ P.inl ≫ g = hO.from_ T ≫ q ∧
        IsPushout (hO.from_ T) P.inl q g ∧
        ∃ hPoint : ∀ x : Ar n, IsCofiberSequence (P.inl.hom.app x) (g.hom.app x),
          (letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
            CofiberSequenceCategory.relativeWaldhausenCategory C;
            IsStage n (cofiberFunctorSequenceLift T.obj P.apex.obj Q.obj P.inl.hom g.hom hPoint)) :=
              by
  let zT : T ⟶ O := hO.from_ T
  have hZero : k ≫ zT = z := hO.eq_of_tgt _ _
  have hComm : k ≫ (zT ≫ q) = i ≫ p := by
    calc
      k ≫ (zT ≫ q) = (k ≫ zT) ≫ q := (Category.assoc _ _ _).symm
      _ = z ≫ q := congrArg (fun f => f ≫ q) hZero
      _ = i ≫ p := hOld.w
  let g : P.apex ⟶ Q := P.isPushout.desc (zT ≫ q) p hComm
  have hInl : P.inl ≫ g = zT ≫ q := P.isPushout.inl_desc _ _ _
  have hInr : P.inr ≫ g = p := P.isPushout.inr_desc _ _ _
  have hOuter : IsPushout (k ≫ zT) i q (P.inr ≫ g) := by
    rw [hInr, hZero]
    exact hOld
  have hNew : IsPushout zT P.inl q g := hOuter.of_left hInl.symm P.isPushout
  let : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
  let : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
  let e : O ≅ (0 : Stage C n) := hO.isoZero
  have hStage : IsCofiberSequence P.inl g := by
    refine ⟨(isCofibration_generalStageWaldhausenCategory_iff C n P.inl).mpr P.inlCofibration,
      zT ≫ e.hom, e.inv ≫ q, ?_⟩
    apply hNew.of_iso (Iso.refl T) e (Iso.refl P.apex) (Iso.refl Q)
    all_goals simp
  have hPoint : ∀ x : Ar n, IsCofiberSequence (P.inl.hom.app x) (g.hom.app x) := by
    intro x
    exact (evalIsGeneralStageWaldhausenExact C n x).map_cofibrationSequence hStage
  refine ⟨g, hInr, hInl, hNew, hPoint, ?_⟩
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
    CofiberSequenceCategory.relativeWaldhausenCategory C
  exact CofiberSequenceCategory.isStage_cofiberFunctorSequence_of_stageCofibration C n
    T P.apex Q P.inl g hPoint P.inlCofibration

end CategoryTheory.Waldhausen.SConstruction
