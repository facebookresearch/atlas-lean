/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceConcatenationCoefficientLift
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceRawCutEvaluation

/-!
# Full original concatenation evaluation in the SAME raw Hom

The entire original prefix and suffix input maps retain their common
input vertex. The actual full coefficient lift formula proves evaluation
preserves the SAME original raw Hom composition in every scalar degree.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open OriginalNecklaceHom SSet.OriginalNecklace SSet.OriginalTwoBead.OrdinalCharts

variable {K : SSet.{u}} {x y z : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The complete original concatenated input retains its original common vertex. -/
theorem input_vertex_concat_pivot (T : Object K x y q) (U : Object K y z q) :
    (concat T U).input.app (op ⦋0⦌)
        (nativeVertex (T.necklace.concat U.necklace) (pivot T.necklace.dimension U.necklace.dimension)) = y := by
  have hv := congrArg (fun v => (concat T U).input.app (op ⦋0⦌) v)
    (concatLeft_targetVertex.{u} T.necklace U.necklace)
  have hi := ConcreteCategory.congr_hom (congr_app (concat_first_input T U) (op ⦋0⦌))
    (targetVertex T.necklace)
  exact hv.symm.trans (hi.trans (input_target T))

/-- The SAME entire first input Hom map is retained by the original full concatenation. -/
theorem inputHomMap_concat_left (T : Object K x y q) (U : Object K y z q) :
    concatLeftHomMap.{u} T.necklace U.necklace ≫
        pointedHomMap (concat T U).input (input_source (concat T U)) (input_vertex_concat_pivot T U) =
      inputHomMap T :=
  (pointedHomMap_comp (concatLeft T.necklace U.necklace) (concat T U).input
    (concatLeft_sourceVertex T.necklace U.necklace) (concatLeft_targetVertex T.necklace U.necklace)
    (input_source (concat T U)) (input_vertex_concat_pivot T U)).trans
      (pointedHomMap_eq (concat_first_input T U)
        ((congrArg (fun v => (concat T U).input.app (op ⦋0⦌) v)
          (concatLeft_sourceVertex T.necklace U.necklace)).trans (input_source (concat T U)))
        ((congrArg (fun v => (concat T U).input.app (op ⦋0⦌) v)
          (concatLeft_targetVertex T.necklace U.necklace)).trans (input_vertex_concat_pivot T U))
        (input_source T) (input_target T))

/-- The SAME entire second input Hom map is retained by the original full concatenation. -/
theorem inputHomMap_concat_right (T : Object K x y q) (U : Object K y z q) :
    concatRightHomMap.{u} T.necklace U.necklace ≫
        pointedHomMap (concat T U).input (input_vertex_concat_pivot T U) (input_target (concat T U)) =
      inputHomMap U :=
  (pointedHomMap_comp (concatRight T.necklace U.necklace) (concat T U).input
    (concatRight_sourceVertex T.necklace U.necklace) (concatRight_targetVertex T.necklace U.necklace)
    (input_vertex_concat_pivot T U) (input_target (concat T U))).trans
      (pointedHomMap_eq (concat_second_input T U)
        ((congrArg (fun v => (concat T U).input.app (op ⦋0⦌) v)
          (concatRight_sourceVertex T.necklace U.necklace)).trans (input_vertex_concat_pivot T U))
        ((congrArg (fun v => (concat T U).input.app (op ⦋0⦌) v)
          (concatRight_targetVertex T.necklace U.necklace)).trans (input_target (concat T U)))
        (input_source U) (input_target U))

private theorem binary_square_app {A B C D E F : SSet.{u}}
    (m : A ⊗ B ⟶ C) (m' : D ⊗ E ⟶ F) (a : A ⟶ D) (b : B ⟶ E) (c : C ⟶ F)
    (h : m ≫ c = (a ⊗ₘ b) ≫ m') (q : SimplexCategoryᵒᵖ) (x : A.obj q) (y : B.obj q) :
    c.app q (m.app q (x, y)) = m'.app q (a.app q x, b.app q y) := by
  have e := ConcreteCategory.congr_hom (congr_app h q) (show (A ⊗ B).obj q from (x, y))
  exact e

/-- EVERY entire original concatenation evaluates by its SAME original full raw Hom composition. -/
theorem evaluation_concat (T : Object K x y q) (U : Object K y z q) :
    evaluation (concat T U) =
      (eComp SSet.{u} (C := realization K) x y z).app q (evaluation T, evaluation U) := by
  let l := coefficientLift T.necklace (jointCoefficient T)
  let r := coefficientLift U.necklace (jointCoefficient U)
  have hL := ConcreteCategory.congr_hom (congr_app (inputHomMap_concat_left T U) q) l
  have hR := ConcreteCategory.congr_hom (congr_app (inputHomMap_concat_right T U) q) r
  have hc := binary_square_app
    (eComp SSet.{u} (C := realization (T.necklace.concat U.necklace).object.{u})
      (sourceVertex (T.necklace.concat U.necklace))
      (nativeVertex (T.necklace.concat U.necklace) (pivot T.necklace.dimension U.necklace.dimension))
      (targetVertex (T.necklace.concat U.necklace)))
    (eComp SSet.{u} (C := realization K) x y z)
    (pointedHomMap (concat T U).input (input_source (concat T U)) (input_vertex_concat_pivot T U))
    (pointedHomMap (concat T U).input (input_vertex_concat_pivot T U) (input_target (concat T U)))
    (inputHomMap (concat T U))
    (pointedHomMap_composition (concat T U).input (input_source (concat T U))
      (input_vertex_concat_pivot T U) (input_target (concat T U))) q
    ((concatLeftHomMap T.necklace U.necklace).app q l)
    ((concatRightHomMap T.necklace U.necklace).app q r)
  exact (congrArg ((inputHomMap (concat T U)).app q)
    (coefficientLift_concat T.necklace U.necklace (jointCoefficient T) (jointCoefficient U)
      (jointCoefficient (concat T U)) rfl)).trans
    (hc.trans (congrArg ((eComp SSet.{u} (C := realization K) x y z).app q)
      (congrArg₂ Prod.mk hL hR)))

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
