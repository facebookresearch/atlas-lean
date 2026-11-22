/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalInitialEdgeTailInclusions
import MathlibExt.AlgebraicTopology.SimplicialSpace.DiscreteSourceCoproductMapping
import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
# The whole leading-edge and tail mapping pullback of a Segal path row

The original cover pushout is sent by the actual source mapping
enrichment to its native pullback. Whole representable Yoneda
isomorphisms retain the original initial vertex and target endpoint.
Thus the leading-edge cover mapping target is the actual tail-simplex
and edge pullback, with both original restrictions unchanged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial SimplicialSpace.Inner

namespace SimplicialSpace.InitialEdgeTailMapping

/-- The whole actual mapping pullback induced by the original initial-edge/tail cover pushout. -/
theorem isPullback (W : SimplicialSpace.{u}) (n : ℕ) :
    IsPullback
      ((discreteSourceMapping W).map (SSet.Rezk.InitialEdgeTail.tailInclusion.{u} n).op)
      ((discreteSourceMapping W).map (SSet.Rezk.InitialEdgeTail.edgeInclusion.{u} n).op)
      ((discreteSourceMapping W).map (SSet.Rezk.InitialEdgeTail.vertexToTail.{u} n).op)
      ((discreteSourceMapping W).map (SSet.stdSimplex.δ (0 : Fin 2)).op) := by
  let _ := discreteSourceMapping_preservesLimitsOfShape WalkingCospan W
  exact ((SSet.Rezk.InitialEdgeTail.simplex_isPushout.{u} n).op.map
    (discreteSourceMapping W)).flip

/-- The complete original cover mapping target is its same native pullback of the original restrictions. -/
def coverIso (W : SimplicialSpace.{u}) (n : ℕ) :
    (discreteSourceMapping W).obj
        (op (SSet.Rezk.initialIntervalCover.{u} (n + 1) : SSet.{u})) ≅
      pullback
        ((discreteSourceMapping W).map (SSet.Rezk.InitialEdgeTail.vertexToTail.{u} n).op)
        ((discreteSourceMapping W).map (SSet.stdSimplex.δ (0 : Fin 2)).op) :=
  (isPullback W n).isoPullback

/-- The forward cover comparison retains the whole original tail restriction. -/
theorem coverIso_fst (W : SimplicialSpace.{u}) (n : ℕ) :
    (coverIso W n).hom ≫ pullback.fst _ _ =
      (discreteSourceMapping W).map (SSet.Rezk.InitialEdgeTail.tailInclusion.{u} n).op :=
  (isPullback W n).isoPullback_hom_fst

/-- The forward cover comparison retains the whole original leading-edge restriction. -/
theorem coverIso_snd (W : SimplicialSpace.{u}) (n : ℕ) :
    (coverIso W n).hom ≫ pullback.snd _ _ =
      (discreteSourceMapping W).map (SSet.Rezk.InitialEdgeTail.edgeInclusion.{u} n).op :=
  (isPullback W n).isoPullback_hom_snd

end SimplicialSpace.InitialEdgeTailMapping
