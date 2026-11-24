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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberRelativeStageCriterion
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageCofibrationCorners
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageZeroRowCriterion

/-!
# Whole stage admission for an original cofiber functor sequence

A pointwise cofiber functor sequence of original finite stages whose
first whole stage arrow is a genuine stage cofibration admits an entire
relative extension stage. The original zero-row corners and quotient
pushouts determine every full triple through the general zero-row criterion.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction.CofiberSequenceCategory

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The original universal cofiber functor diagram is a genuine relative
stage when its original first whole stage arrow has all genuine stage corners. -/
theorem isStage_cofiberFunctorSequence_of_stageCofibration (n : ℕ)
    (A₀ A₁ A₂ : Stage C n) (i : A₀ ⟶ A₁) (p : A₁ ⟶ A₂)
    (hPoint : ∀ x : Ar n, IsCofiberSequence (i.hom.app x) (p.hom.app x))
    (hi : stageCofibrations C n i) :
    letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      relativeWaldhausenCategory C;
    IsStage n (cofiberFunctorSequenceLift A₀.obj A₁.obj A₂.obj i.hom p.hom hPoint) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) := relativeWaldhausenCategory C
  let F := cofiberFunctorSequenceLift A₀.obj A₁.obj A₂.obj i.hom p.hom hPoint
  have hRows : ∀ k : Fin 3,
      IsStage n (F ⋙ ((forget C) ⋙ (evaluation (Fin 3) C).obj k)) := by
    intro k
    fin_cases k
    · change IsStage n (F ⋙ source C)
      rw [cofiberFunctorSequenceLift_source]
      exact A₀.property
    · change IsStage n (F ⋙ middle C)
      rw [cofiberFunctorSequenceLift_middle]
      exact A₁.property
    · change IsStage n (F ⋙ quotient C)
      rw [cofiberFunctorSequenceLift_quotient]
      exact A₂.property
  apply isStage_of_zeroRowCofiber F
  · intro j
    apply IsZero.of_full_of_faithful_of_isZero (forget C)
    exact Functor.isZero _ (fun k => (hRows k).diag_isZero j)
  · intro a b hab
    let r := horiz (Fin.zero_le a) hab
    let s := vert (Fin.zero_le a) hab
    have hRelative : relativeCofibrations C (F.map r) := by
      obtain ⟨P, inl, inr, d, hP, hinl, hinr, hd⟩ := Stage.zeroRowPair_corner C i hi hab
      apply (mem_relativeCofibrations_raw_iff C (F.map r)).mpr
      change IsCofibration (A₀.obj.map r) ∧
        ∃ (P : C) (inB : A₁.obj.obj (interval 0 a (Fin.zero_le a)) ⟶ P)
          (inA : A₀.obj.obj (interval 0 b (Fin.zero_le b)) ⟶ P)
          (d : P ⟶ A₁.obj.obj (interval 0 b (Fin.zero_le b))),
          IsPushout (i.hom.app (interval 0 a (Fin.zero_le a))) (A₀.obj.map r) inB inA ∧
            inB ≫ d = A₁.obj.map r ∧
            inA ≫ d = i.hom.app (interval 0 b (Fin.zero_le b)) ∧ IsCofibration d
      refine ⟨(A₀.property.cofiber_triple (Fin.zero_le a) hab).1,
        P, inr, inl, d, ?_, ?_, ?_, hd⟩
      · simpa only [Stage.zeroRowPairMap_eq, Stage.zeroRowApp, Stage.zeroRowObj] using hP.flip
      · simpa only [Stage.zeroRowPairMap_eq, Stage.zeroRowObj] using hinr
      · exact hinl
    apply (isCofiberSequence_relative_iff_evaluations C (F.map r) (F.map s)).mpr
    refine ⟨hRelative, ?_⟩
    intro k
    exact (hRows k).cofiber_triple (Fin.zero_le a) hab

end CategoryTheory.Waldhausen.SConstruction.CofiberSequenceCategory
