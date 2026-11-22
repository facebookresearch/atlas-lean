/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceRawEvaluationScalar
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceCoefficientCutLift

/-!
# The SAME original raw evaluation of both complete necklace cuts

The actual full native cut lifts are sent through the entire original
input map. The original source, cut vertex and target equations retain
both full raw input maps. Their SAME original raw composition is exactly
the evaluation of the whole original flagged necklace in every scalar.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open OriginalNecklaceHom SSet.OriginalNecklace SimplicialEnrichment

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The SAME whole original input reads its literal individual original cut vertex. -/
theorem input_vertex (T : Object K x y q) (j : Fin (T.necklace.dimension + 1)) :
    T.input.app (op ⦋0⦌) (nativeVertex T.necklace j) = inputVertex T j :=
  (SSet.yonedaEquiv_comp (vertexMap T.necklace.joints j) T.input).symm

/-- The SAME entire original input Hom map retains the complete prefix cut map. -/
theorem inputHomMap_leftCut (T : Object K x y q) (j : Fin (T.necklace.dimension + 1))
    (hj : j ∈ T.necklace.joints) :
    leftCutHomMap.{u} T.necklace j hj ≫ pointedHomMap T.input (input_source T) (input_vertex T j) =
      inputHomMap (CutObjects.leftObject T j hj) :=
  pointedHomMap_comp (Cut.leftMap T.necklace j hj) T.input
    ((SSet.yonedaEquiv_comp (Cut.leftData T.necklace j hj).source (Cut.leftMap T.necklace j hj)).symm.trans
      (congrArg SSet.yonedaEquiv (Cut.leftMap_source T.necklace j hj)))
    ((SSet.yonedaEquiv_comp (Cut.leftData T.necklace j hj).target (Cut.leftMap T.necklace j hj)).symm.trans
      (congrArg SSet.yonedaEquiv (Cut.leftMap_target T.necklace j hj)))
    (input_source T) (input_vertex T j)

/-- The SAME entire original input Hom map retains the complete suffix cut map. -/
theorem inputHomMap_rightCut (T : Object K x y q) (j : Fin (T.necklace.dimension + 1))
    (hj : j ∈ T.necklace.joints) :
    rightCutHomMap.{u} T.necklace j hj ≫ pointedHomMap T.input (input_vertex T j) (input_target T) =
      inputHomMap (CutObjects.rightObject T j hj) :=
  pointedHomMap_comp (Cut.rightMap T.necklace j hj) T.input
    ((SSet.yonedaEquiv_comp (Cut.rightData T.necklace j hj).source (Cut.rightMap T.necklace j hj)).symm.trans
      (congrArg SSet.yonedaEquiv (Cut.rightMap_source T.necklace j hj)))
    ((SSet.yonedaEquiv_comp (Cut.rightData T.necklace j hj).target (Cut.rightMap T.necklace j hj)).symm.trans
      (congrArg SSet.yonedaEquiv (Cut.rightMap_target T.necklace j hj)))
    (input_vertex T j) (input_target T)

private theorem binary_square_app {A B C D E F : SSet.{u}}
    (m : A ⊗ B ⟶ C) (m' : D ⊗ E ⟶ F) (a : A ⟶ D) (b : B ⟶ E) (c : C ⟶ F)
    (h : m ≫ c = (a ⊗ₘ b) ≫ m') (q : SimplexCategoryᵒᵖ) (x : A.obj q) (y : B.obj q) :
    c.app q (m.app q (x, y)) = m'.app q (a.app q x, b.app q y) := by
  have e := ConcreteCategory.congr_hom (congr_app h q) (show (A ⊗ B).obj q from (x, y))
  exact e

/-- EVERY complete original flagged necklace has its SAME actual full raw cut-composition evaluation. -/
theorem evaluation_cut (T : Object K x y q) (j : Fin (T.necklace.dimension + 1))
    (hj : j ∈ T.necklace.joints) :
    evaluation T = (eComp SSet.{u} (C := realization K) x (inputVertex T j) y).app q
      (evaluation (CutObjects.leftObject T j hj), evaluation (CutObjects.rightObject T j hj)) := by
  let l := coefficientLift (Cut.leftData T.necklace j hj) (jointCoefficient (CutObjects.leftObject T j hj))
  let r := coefficientLift (Cut.rightData T.necklace j hj) (jointCoefficient (CutObjects.rightObject T j hj))
  have hL := ConcreteCategory.congr_hom (congr_app (inputHomMap_leftCut T j hj) q) l
  have hR := ConcreteCategory.congr_hom (congr_app (inputHomMap_rightCut T j hj) q) r
  have hc := binary_square_app
    (eComp SSet.{u} (C := realization T.necklace.object.{u}) (sourceVertex T.necklace)
      (nativeVertex T.necklace j) (targetVertex T.necklace))
    (eComp SSet.{u} (C := realization K) x (inputVertex T j) y)
    (pointedHomMap T.input (input_source T) (input_vertex T j))
    (pointedHomMap T.input (input_vertex T j) (input_target T)) (inputHomMap T)
    (pointedHomMap_composition T.input (input_source T) (input_vertex T j) (input_target T)) q
    ((leftCutHomMap T.necklace j hj).app q l) ((rightCutHomMap T.necklace j hj).app q r)
  exact (congrArg ((inputHomMap T).app q) (coefficientLift_cut T.necklace j hj (jointCoefficient T))).trans
    (hc.trans (congrArg ((eComp SSet.{u} (C := realization K) x (inputVertex T j) y).app q)
      (congrArg₂ Prod.mk hL hR)))

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
