/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceRawCutEvaluation
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceRawBeadEvaluation
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedBeadTrimReadback
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceCutReassembly

/-!
# The SAME original component inverse identity

The actual full original evaluation followed by the original raw
component map is the identity on EVERY full original flagged component.
The proof uses whole beads and exact first-bead/suffix cut evaluation,
retaining all original input maps and every scalar coefficient.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open OriginalBead OriginalNecklaceHom SSet.OriginalNecklace

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The SAME entire original endpoint-joint object retains its original full raw component readback. -/
theorem rawHomMap_evaluation_wholeBead (T : Object K x y q)
    (hJ : T.necklace.joints = {0, Fin.last T.necklace.dimension}) :
    (Components.rawHomMap K x y).app q (evaluation T) = CategoryTheory.ConnectedComponents.mk T := by
  have he := (evaluation_natural (wholeBeadIso T hJ).hom).trans (evaluation_ofBead (wholeBead T hJ))
  have hc : CategoryTheory.ConnectedComponents.mk T =
      CategoryTheory.ConnectedComponents.mk (ofBead (wholeBead T hJ)) :=
    _root_.Quotient.sound (Zigzag.of_hom (wholeBeadIso T hJ).hom)
  exact (congrArg ((Components.rawHomMap K x y).app q) he).trans
    ((Components.rawHomMap_bead (wholeBead T hJ)).trans hc.symm)

private theorem binary_square_app {A B C D E F : SSet.{u}}
    (m : A ⊗ B ⟶ C) (m' : D ⊗ E ⟶ F) (a : A ⟶ D) (b : B ⟶ E) (c : C ⟶ F)
    (h : m ≫ c = (a ⊗ₘ b) ≫ m') (q : SimplexCategoryᵒᵖ) (x : A.obj q) (y : B.obj q) :
    c.app q (m.app q (x, y)) = m'.app q (a.app q x, b.app q y) := by
  have e := ConcreteCategory.congr_hom (congr_app h q) (show (A ⊗ B).obj q from (x, y))
  exact e

/-- EVERY SAME entire original flagged object has its actual original raw component evaluation readback. -/
theorem rawHomMap_evaluation (T : Object K x y q) :
    (Components.rawHomMap K x y).app q (evaluation T) = CategoryTheory.ConnectedComponents.mk T := by
  have H : ∀ n : ℕ, ∀ (a b : K _⦋0⦌) (S : Object K a b q), S.necklace.dimension = n →
      (Components.rawHomMap K a b).app q (evaluation S) = CategoryTheory.ConnectedComponents.mk S := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a b S hn
      by_cases h0 : S.necklace.dimension = 0
      · exact rawHomMap_evaluation_wholeBead S (zero_necklace_joints S.necklace h0)
      · let i : Fin S.necklace.dimension := ⟨0, Nat.pos_of_ne_zero h0⟩
        obtain ⟨c, j, hcj, hc, _hj⟩ := exists_bead_at_edge S.necklace i
        have hc0 : c = 0 := by
          apply Fin.ext
          change c.val = 0
          have hc' : c.val ≤ 0 := hc
          omega
        subst c
        let L := CutObjects.leftObject S j hcj.target
        let R := CutObjects.rightObject S j hcj.target
        have hL := rawHomMap_evaluation_wholeBead L (Cut.leftJoints_of_first_bead hcj)
        have hR := ih R.necklace.dimension ((Cut.rightDimension_lt S.necklace j hcj.positive).trans_eq hn)
          (inputVertex S j) b R rfl
        have hcomp := binary_square_app
          (eComp SSet.{u} (C := realization K) a (inputVertex S j) b)
          (Components.composition K a (inputVertex S j) b)
          (Components.rawHomMap K a (inputVertex S j)) (Components.rawHomMap K (inputVertex S j) b)
          (Components.rawHomMap K a b) (Components.rawHomMap_composition K a (inputVertex S j) b)
          q (evaluation L) (evaluation R)
        have hcc : CategoryTheory.ConnectedComponents.mk (concat L R) = CategoryTheory.ConnectedComponents.mk S :=
          _root_.Quotient.sound (Zigzag.of_hom (CutObjects.reassemblyIso S j hcj.target).hom)
        exact (congrArg ((Components.rawHomMap K a b).app q) (evaluation_cut S j hcj.target)).trans
          (hcomp.trans ((congrArg ((Components.composition K a (inputVertex S j) b).app q)
            (congrArg₂ Prod.mk hL hR)).trans hcc))
  exact H T.necklace.dimension x y T rfl

namespace Components

/-- The SAME actual full component evaluation followed by the original raw map is the component identity. -/
theorem rawEvaluationMap_rawHomMap (K : SSet.{u}) (x y : K _⦋0⦌) :
    rawEvaluationMap K x y ≫ rawHomMap K x y = 𝟙 (simplicialSet K x y) := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro c
  induction c using _root_.Quotient.inductionOn' with
  | h T => exact rawHomMap_evaluation T

end Components

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
