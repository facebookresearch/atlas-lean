/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontReedyFibrantDegrees
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontReedyOrdinalComparison
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedRightMappingFunctor

/-!
# Both genuine original endpoint point properties of the actual Reedy degrees

Every full original generated degree is actually fibrant. Its actual
same projection to the original walking arrow is categorical weak and
retains both endpoint maps. Thus BOTH independent original raw Hom and
original right-mapping point maps are genuinely weak. The same
fixed-front/Reedy full Hom comparison remains the actual original map.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFixedFrontContraction

open OriginalRawRightMapping

/-- The same entire original Reedy degree has genuine original right-mapping point weakness. -/
theorem rawReedyDegree_rightPoint_weak (n : SimplexCategory) :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from
      (SSet.mappingSpaceRight (rawReedyDegree.{u} n).right
        (OriginalPointed.source (rawReedyDegree.{u} n))
        (OriginalPointed.target (rawReedyDegree.{u} n)))) := by
  let _ : SSet.Quasicategory (rawReedyDegree.{u} n).right := reedyReplacement_raw_quasicategory n
  let h := rawReedyOrdinalComparison.{u} n
  let f := SSet.mappingSpaceRight.map _ _ _ h.map ≫
    (SSet.PointedRightMappingSpace.endpointIso h.source h.target).hom
  have hf : SSet.realizationWeakEquivalences f :=
    SSet.realizationWeakEquivalences.comp_mem _ _
      (h.categorical.rightMappingSpaceMap_weak (OriginalPointed.source (rawReedyDegree n))
        (OriginalPointed.target (rawReedyDegree n)))
      (SSet.realizationWeakEquivalences.of_isIso
        (SSet.PointedRightMappingSpace.endpointIso h.source h.target).hom)
  have hp := simplexMappingPoint_weak (0 : Fin 2) (Fin.last 1) (Fin.zero_le _)
  have hw := SSet.realizationWeakEquivalences.comp_mem f _ hf hp
  have he : f ≫ SSet.stdSimplex.isTerminalObj₀.from
      (SSet.mappingSpaceRight (Δ[1] : SSet.{u}) (simplexVertex 1 0) (simplexVertex 1 (Fin.last 1))) =
      SSet.stdSimplex.isTerminalObj₀.from
        (SSet.mappingSpaceRight (rawReedyDegree.{u} n).right
          (OriginalPointed.source (rawReedyDegree.{u} n))
          (OriginalPointed.target (rawReedyDegree.{u} n))) := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact he ▸ hw

/-- Both same original endpoint point projections of every actual full original Reedy degree are genuinely weak. -/
theorem rawReedyDegree_both_point_weak (n : SimplexCategory) :
    SSet.realizationWeakEquivalences
      (SSet.stdSimplex.isTerminalObj₀.from (OriginalPointed.homObject (rawReedyDegree.{u} n))) ∧
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from
      (SSet.mappingSpaceRight (rawReedyDegree.{u} n).right
        (OriginalPointed.source (rawReedyDegree.{u} n))
        (OriginalPointed.target (rawReedyDegree.{u} n)))) :=
  ⟨rawReedyDegree_rawPoint_weak n, rawReedyDegree_rightPoint_weak n⟩

end CategoryTheory.CoherentRealization.OriginalFixedFrontContraction
