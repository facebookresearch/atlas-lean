/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeAfterCofaceOperator
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeProperBoundaryOperator
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootBoundaryAfter

/-!
# The exact original supported positive-coface operator square

The same original proper coface image on the entire positive diagram
is its original positive-cone coface map followed by the actual full
positive inclusion into the root boundary. Both sides retain every
whole original subset word, scalar operator, path action and mark.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The original supported proper-coface lift on the whole positive cone is exactly the same original positive
coface image and unchanged root-boundary positive entry. -/
theorem coneProperBoundaryOperator_positive {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneAfterDiagramInclusion (⊥ : Vertex.{u} n) ≫
      coneProperBoundaryOperator (coneCofaceEmbedding j).toOrderHom (coneCofaceEmbedding_not_surjective j) =
        coneAfterCofaceOperator j hj ≫
          (enrichedDiagramRestrict (EnrichedFunctor.opposite (indexMap (coneCofaceEmbedding j).toOrderHom))).map
            (coneRootBoundaryAfterMap (n + 1)) := by
  apply EnrichedDiagramMap.ext
  funext i
  apply Hom.ext
  ext q a
  apply Subtype.ext
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => Subsingleton.elim _ _)

end SSet.Marked.CoherentWeight
