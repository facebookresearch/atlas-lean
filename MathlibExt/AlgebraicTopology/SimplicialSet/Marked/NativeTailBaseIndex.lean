/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeTailOperator
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLeftKanComposition
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentUnit

/-!
# The actual native zeroth-coface base index

The existing whole coherent-simplex insertion operator law identifies
the original restricted base simplex with the actual tail index
composite. Opposite restriction retains that same full operator and
all original vertices; the comparison is derived from the original
coherent unit equations.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization CategoryTheory.SimplicialEnrichment
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The actual original opposite tail index followed by the native base simplex is precisely its original
  zeroth-face base index. -/
theorem nativeTailIndex_comp_simplex (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    (coneTailIndex n).comp SSet.{u} (EnrichedFunctor.opposite (simplexInto B σ)) =
      EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ (0 : Fin (n + 2))).op σ)) := by
  change EnrichedFunctor.opposite
      (coherentSimplexMap (SimplexCategory.δ (0 : Fin (n + 2))) ≫ simplexInto B σ) = _
  exact congrArg (fun f => EnrichedFunctor.opposite f)
    (simplexInto_operator B (SimplexCategory.δ (0 : Fin (n + 2))) σ)

/-- Whole original native base restriction and tail restriction compose to exactly the original zeroth-face
  restriction functor. -/
theorem nativeTail_restriction_comp (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B σ)) ⋙
        enrichedDiagramRestrict (coneTailIndex n) =
      enrichedDiagramRestrict
        (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ (0 : Fin (n + 2))).op σ))) :=
  (enrichedDiagramRestrict_comp (coneTailIndex n) (EnrichedFunctor.opposite (simplexInto B σ))).trans
    (congrArg (fun f : EnrichedFunctor SSet.{u} (Index.{u} n)ᵒᵖ (realization B)ᵒᵖ => enrichedDiagramRestrict f)
      (nativeTailIndex_comp_simplex B n σ))

end SSet.Marked
