/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelClassComparison
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedEmbedding
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorLeftClassClosedEmbedding

/-!
# CGWH model cofibrations are closed embeddings

The selected CGWH model cofibrations are contained in the inverse image of
closed embeddings in `TopCat`.  Only this one-way consequence is asserted.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MorphismProperty

universe u v

namespace CGWH

/-- Every selected CGWH model cofibration is a closed embedding after
forgetting to `TopCat`. -/
theorem modelCofibrations_le_closedEmbeddings :
    modelCofibrations.{u, v} ≤
      TopCat.closedEmbeddings.{v}.inverseImage
        cgwhToTop.{u, v} := by
  rw [modelCofibrations_eq_inverseImage]
  exact MorphismProperty.monotone_inverseImage cgwhToTop.{u, v}
    (le_trans
      (MorphismProperty.antitone_llp
        (MorphismProperty.antitone_rlp le_sup_left))
      TopCat.generatorUnion_llp_le_closedEmbeddings)

end CGWH
