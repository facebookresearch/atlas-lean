/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceRawConcatenationEvaluation
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceRawUnitEvaluation
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedComponentEnrichment

/-!
# The full original component evaluation enriched functor

Both the original full coefficient concatenation and the original zero
necklace evaluate by the SAME raw coherent Hom composition and identity.
The full evaluation therefore defines an enriched functor retaining all
original object labels and actual raw Hom maps.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components

/-- The actual full component evaluation retains the original raw identity. -/
theorem rawEvaluationMap_identity (K : SSet.{u}) (x : K _⦋0⦌) :
    identity K x ≫ rawEvaluationMap K x x = eId SSet.{u} (C := realization K) x := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro p
  exact evaluation_unit K x q

/-- Every entire original component pair evaluates by its SAME full original raw composition. -/
theorem rawEvaluation_concatenate (K : SSet.{u}) (x y z : K _⦋0⦌) (q : SimplexCategoryᵒᵖ)
    (a : (simplicialSet K x y).obj q) (b : (simplicialSet K y z).obj q) :
    rawEvaluation K x z q (concatenate a b) =
      (eComp SSet.{u} (C := realization K) x y z).app q
        (rawEvaluation K x y q a, rawEvaluation K y z q b) := by
  induction a using _root_.Quotient.inductionOn' with
  | h T =>
    induction b using _root_.Quotient.inductionOn' with
    | h U => exact evaluation_concat T U

/-- The SAME actual full component evaluation retains the entire raw Hom composition square. -/
theorem rawEvaluationMap_composition (K : SSet.{u}) (x y z : K _⦋0⦌) :
    composition K x y z ≫ rawEvaluationMap K x z =
      (rawEvaluationMap K x y ⊗ₘ rawEvaluationMap K y z) ≫ eComp SSet.{u} (C := realization K) x y z := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  rintro ⟨a, b⟩
  exact rawEvaluation_concatenate K x y z q a b

/-- The genuine full original component evaluation functor, with the SAME original vertex labels. -/
def evaluationFunctor (K : SSet.{u}) : category K ⟶ realization K where
  obj x := x
  map := rawEvaluationMap K
  map_id := rawEvaluationMap_identity K
  map_comp := rawEvaluationMap_composition K

/-- The original evaluation enriched functor retains every literal original input vertex. -/
theorem evaluationFunctor_obj (K : SSet.{u}) (x : K _⦋0⦌) : (evaluationFunctor K).obj x = x := rfl

/-- The original evaluation enriched functor retains its SAME entire raw Hom map. -/
theorem evaluationFunctor_map (K : SSet.{u}) (x y : K _⦋0⦌) :
    (evaluationFunctor K).map x y = rawEvaluationMap K x y := rfl

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components
