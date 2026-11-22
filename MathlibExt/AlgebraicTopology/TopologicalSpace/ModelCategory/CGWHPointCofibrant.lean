/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.CGWH.FiniteZero
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHGenerators
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelStructure
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelClassComparison

/-!
# Cofibrancy of the point in CGWH

This file identifies the zero-boundary generator with the map from the
initial object to the native point and proves that the point is cofibrant in
the selected CGWH model structure.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MorphismProperty
open HomotopicalAlgebra

namespace CGWH

section

open scoped CGWH.modelCategory

/-- The zero-boundary generator is isomorphic to the map from the initial
object to the native point. -/
noncomputable def realizedBoundaryInclusion_zero_arrowIso :
    Arrow.mk (realizedBoundaryInclusion.{v, u} 0) ≅
      Arrow.mk (initial.to point.{u, v}) :=
  Arrow.isoMk
    (SSet.toCGWHOfFinite_boundary_zero_isInitial.uniqueUpToIso
      initialIsInitial)
    SSet.toCGWHOfFinite_stdSimplex_zero_iso_point
    (point_isTerminal.hom_ext _ _)

/-- The native point is cofibrant in the selected CGWH model structure. -/
theorem point_isCofibrant : IsCofibrant point.{u, v} := by
  have hi : realizedBoundaryInclusions.{u, v}.rlp.llp
      (realizedBoundaryInclusion.{v, u} 0) :=
    realizedBoundaryInclusions.le_llp_rlp _
      (boundary_mem_realizedBoundaryInclusions 0)
  have hiTop : TopCat.realizedBoundaryInclusions.{v}.rlp.llp
      (cgwhToTop.{u, v}.map (realizedBoundaryInclusion.{v, u} 0)) := by
    rw [realizedBoundaryInclusions_rlp_llp] at hi
    rw [CompactlyGenerated.realizedBoundaryInclusions_rlp_llp] at hi
    exact hi
  have hiCof : cofibrations CGWH.{u, v}
      (realizedBoundaryInclusion.{v, u} 0) := by
    change modelCofibrations.{u, v}
      (realizedBoundaryInclusion.{v, u} 0)
    rw [modelCofibrations_eq_inverseImage]
    exact hiTop
  have hInitialPoint : cofibrations CGWH.{u, v}
      (initial.to point.{u, v}) :=
    ((cofibrations CGWH.{u, v}).arrow_mk_iso_iff
      realizedBoundaryInclusion_zero_arrowIso).mp hiCof
  rw [isCofibrant_iff, cofibration_iff]
  exact hInitialPoint

end

end CGWH
