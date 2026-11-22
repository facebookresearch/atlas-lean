/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceRawBeadEvaluation
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceWholeBeadNormalization
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentBeadUnits

/-!
# The SAME original raw unit evaluation

The original zero necklace is evaluated through its entire native bead
chart and its original singleton coefficient. The actual original
identity relation identifies this full value with the same empty path.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open OriginalBead SimplicialQuiver

/-- The full original zero necklace evaluates to the SAME original raw identity. -/
theorem evaluation_unit (K : SSet.{u}) (x : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    evaluation (unit K q x) = (eId SSet.{u} (C := realization K) x).app q PUnit.unit := by
  let T := unit K q x
  have hJ : T.necklace.joints = {0, Fin.last T.necklace.dimension} :=
    zero_necklace_joints T.necklace rfl
  exact (evaluation_natural (wholeBeadIso T hJ).hom).trans
    ((evaluation_ofBead (wholeBead T hJ)).trans (zero_evaluation (wholeBead T hJ) rfl))

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
