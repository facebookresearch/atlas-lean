/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontReedyRawPoint
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontPointedZeroIso
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedOrdinalRawPoint
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedOrdinalReplacementPoint

/-!
# Actual ordinal comparison of every same original Reedy degree

The actual generated projection followed by the original zero quotient
iso is the full original categorical weak map to the walking arrow.
Both same original endpoints are retained by the actual pointed maps.
The independent raw and replacement-right point conclusions follow
from this genuine source geometry.
-/

noncomputable section

universe u

open CategoryTheory Opposite MorphismProperty
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

/-- The same original full Reedy degree maps to the original walking arrow by the actual generated projection. -/
def rawReedyWalkingMap (n : SimplexCategory) : rawReedyDegree.{u} n ⟶ walkingArrowPointed.{u} :=
  rawReedyProjection n ≫ pointedZeroIso.hom

/-- The same original zero-quotient source readback is the original initial ordinal endpoint. -/
theorem walkingArrowPointed_source : OriginalPointed.source walkingArrowPointed.{u} =
    OriginalRawRightMapping.simplexVertex 1 0 :=
  (SSet.boundary_ι_one_boundaryOneMap _ _).trans
    ((SSet.yonedaEquiv_symm_zero _).symm.trans (Equiv.symm_apply_apply SSet.yonedaEquiv _))

/-- The same original zero-quotient target readback is the original final ordinal endpoint. -/
theorem walkingArrowPointed_target : OriginalPointed.target walkingArrowPointed.{u} =
    OriginalRawRightMapping.simplexVertex 1 (Fin.last 1) :=
  (SSet.boundary_ι_zero_boundaryOneMap _ _).trans
    ((SSet.yonedaEquiv_symm_zero _).symm.trans (Equiv.symm_apply_apply SSet.yonedaEquiv _))

/-- Genuine original ordinal source data of every same actual Reedy degree, with both original endpoints. -/
def rawReedyOrdinalComparison (n : SimplexCategory) : OriginalPointed.OrdinalComparison (rawReedyDegree.{u} n) where
  dimension := 1
  map := (rawReedyWalkingMap n).right
  categorical := RespectsIso.postcomp SSet.categoricalEquivalences zeroObjectIso.hom
    (rawReedyProjection n).right (reedyReplacementProjection_app_categorical n)
  source := (OriginalPointed.source_map (rawReedyWalkingMap n)).trans walkingArrowPointed_source
  target := (OriginalPointed.target_map (rawReedyWalkingMap n)).trans walkingArrowPointed_target

/-- The same original full raw Reedy degree has genuine raw endpoint Hom point weakness. -/
theorem rawReedyDegree_rawPoint_weak (n : SimplexCategory) :
    SSet.realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from (OriginalPointed.homObject (rawReedyDegree.{u} n))) :=
  OriginalPointed.ordinalComparison_rawPoint_weak _ (rawReedyOrdinalComparison n)

/-- The same canonical original replacement of every raw Reedy degree has genuine original right-mapping point
weakness. -/
theorem rawReedyDegree_replacementRightPoint_weak (n : SimplexCategory) :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from
      (SSet.mappingSpaceRight (OriginalPointed.replacementFunctor.obj (rawReedyDegree.{u} n)).right
        (OriginalPointed.source (OriginalPointed.replacementFunctor.obj (rawReedyDegree.{u} n)))
        (OriginalPointed.target (OriginalPointed.replacementFunctor.obj (rawReedyDegree.{u} n))))) :=
  OriginalPointed.ordinalReplacementRightMapping_point_weak _ (rawReedyOrdinalComparison n)

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction
