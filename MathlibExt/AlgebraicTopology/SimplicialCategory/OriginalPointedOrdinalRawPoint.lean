/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedOrdinalGadgets
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentStandardHomPoint

/-!
# Genuine raw Hom point weakness for original ordinal-source data

The supplied full original categorical weak map retains its two
original ordinal endpoints. The genuine original coherent Quillen
preservation and the whole original standard Hom contraction prove
point weakness of the same original source raw Hom.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalPointed

/-- Both original ordinal source-map endpoint equations retain their exact original vertex images. -/
theorem ordinalComparison_vertices (X : Category.{u}) (h : OrdinalComparison X) :
    h.map.app (op ⦋0⦌) (sourceVertex X) = SSet.yonedaEquiv (OriginalRawRightMapping.simplexVertex h.dimension 0) ∧
      h.map.app (op ⦋0⦌) (targetVertex X) =
        SSet.yonedaEquiv (OriginalRawRightMapping.simplexVertex h.dimension (Fin.last h.dimension)) :=
  ⟨(SSet.yonedaEquiv_comp (source X) h.map).symm.trans (congrArg SSet.yonedaEquiv h.source),
    (SSet.yonedaEquiv_comp (target X) h.map).symm.trans (congrArg SSet.yonedaEquiv h.target)⟩

/-- The same complete original ordinal-source raw Hom has its genuinely weak original point projection. -/
theorem ordinalComparison_rawPoint_weak (X : Category.{u}) (h : OrdinalComparison X) :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from (homObject X)) := by
  let f := pointedHomMap h.map (ordinalComparison_vertices X h).1 (ordinalComparison_vertices X h).2
  have hw := pointedHomMap_weak_of_categorical h.map h.categorical
    (ordinalComparison_vertices X h).1 (ordinalComparison_vertices X h).2
  have hp := standardHom_point_weak h.dimension 0 (Fin.last h.dimension) (Fin.zero_le _)
  have hc := SSet.realizationWeakEquivalences.comp_mem f _ hw hp
  have he : f ≫ SSet.stdSimplex.isTerminalObj₀.from
      (hom (Δ[h.dimension] : SSet.{u})
        (SSet.yonedaEquiv (OriginalRawRightMapping.simplexVertex h.dimension 0))
        (SSet.yonedaEquiv (OriginalRawRightMapping.simplexVertex h.dimension (Fin.last h.dimension)))) =
      SSet.stdSimplex.isTerminalObj₀.from (homObject X) := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact he ▸ hc

end CategoryTheory.CoherentRealization.OriginalPointed
