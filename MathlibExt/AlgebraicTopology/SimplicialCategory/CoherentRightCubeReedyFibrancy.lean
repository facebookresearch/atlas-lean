/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeOppositeMatching
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeWeakComparison
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeMaximumNaturality
import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyFibrantObjects
import MathlibExt.AlgebraicTopology.SimplicialSet.StandardSimplexOppositeMatching
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure
import Mathlib.AlgebraicTopology.ModelCategory.Opposite

/-!
# Actual opposite Reedy fibrancy of the coherent right-cube resolution

The original boundary matching identifications prove fibrancy in the
genuine opposite Kan–Quillen Reedy model. The same original maximum is
a Reedy weak equivalence between those actual fibrant objects.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen CategoryTheory.SimplicialObject.reedyModelCategory

namespace CategoryTheory.CoherentRealization.RightCubeReedyFibrancy

/-- The actual opposite right-cube diagram is fibrant in the selected opposite-coefficient Reedy model. -/
theorem cube_isFibrant : IsFibrant RightCubeCosimplicial.diagram.{u}.op := by
  apply (SimplicialObject.reedyModelCategory.isFibrant_iff_matchingMaps _).mpr
  intro n
  change Mono (SimplicialObject.matchingMap RightCubeCosimplicial.diagram.{u}.op n).unop
  exact RightCubeOppositeMatching.matching_unop_mono n

/-- The actual opposite standard simplex diagram is fibrant in that same original Reedy model. -/
theorem standard_isFibrant : IsFibrant SSet.stdSimplex.{u}.op := by
  apply (SimplicialObject.reedyModelCategory.isFibrant_iff_matchingMaps _).mpr
  intro n
  change Mono (SimplicialObject.matchingMap SSet.stdSimplex.{u}.op n).unop
  exact SSet.StandardSimplexOppositeMatching.matching_unop_mono n

/-- The original whole opposite maximum is a weak equivalence in the same actual Reedy model. -/
theorem maximum_weak : WeakEquivalence (NatTrans.op RightCubeMaximumNaturality.map.{u}) := by
  apply (weakEquivalence_iff _).mpr
  change ∀ q : SimplexCategoryᵒᵖ,
    SSet.realizationWeakEquivalences ((NatTrans.op RightCubeMaximumNaturality.map.{u}).app q).unop
  intro q
  exact RightCubeWeakComparison.maximum_weak q.unop.len

end CategoryTheory.CoherentRealization.RightCubeReedyFibrancy
