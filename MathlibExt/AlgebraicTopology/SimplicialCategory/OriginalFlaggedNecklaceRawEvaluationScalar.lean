/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceRawEvaluation
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceScalarComponentAugmentation

/-!
# EVERY scalar of the SAME original raw component evaluation

The actual full original flagged evaluation follows every face and
degeneracy through its complete coefficient lift and entire original
input Hom map. It therefore gives a genuine map from the SAME component
simplicial set to the SAME original raw Hom quotient.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open OriginalNecklaceHom

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q r : SimplexCategoryᵒᵖ}

/-- Every original scalar map retains the SAME entire original input Hom map. -/
theorem inputHomMap_scalar (T : Object K x y q) (θ : q ⟶ r) :
    inputHomMap (scalarObject θ T) = inputHomMap T := rfl

/-- EVERY original scalar operator retains the SAME complete raw evaluation. -/
theorem evaluation_scalar (T : Object K x y q) (θ : q ⟶ r) :
    (hom K x y).map θ (evaluation T) = evaluation (scalarObject θ T) := by
  have h := ConcreteCategory.congr_hom ((inputHomMap T).naturality θ)
    (coefficientLift T.necklace (jointCoefficient T))
  exact h.symm.trans (congrArg ((inputHomMap T).app r)
    (coefficientLift_scalar T.necklace θ (jointCoefficient T)))

namespace Components

/-- The SAME entire original component simplicial set maps to its original raw coherent Hom. -/
def rawEvaluationMap (K : SSet.{u}) (x y : K _⦋0⦌) : simplicialSet K x y ⟶ hom K x y where
  app q := ↾rawEvaluation K x y q
  naturality _q _r θ := by
    apply ConcreteCategory.hom_ext
    intro c
    induction c using _root_.Quotient.inductionOn' with
    | h T => exact (evaluation_scalar T θ).symm

/-- EVERY actual original full component representative retains its literal entire raw Hom evaluation. -/
theorem rawEvaluationMap_mk (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) (T : Object K x y q) :
    (rawEvaluationMap K x y).app q (CategoryTheory.ConnectedComponents.mk T) = evaluation T := rfl

end Components

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
