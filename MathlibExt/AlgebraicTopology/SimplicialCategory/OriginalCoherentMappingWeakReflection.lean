/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRawRightMappingRealizationWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRawRightMappingSourceNaturality
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightCubeEvaluationCounitWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedDwyerKanClasses

/-!
# The SAME realization reflects every original right mapping weak map

The whole original source-naturality square and the proved original
raw comparisons give weakness of every original right mapping map
between quasicategories whenever the actual realization is locally
weak. Both original endpoint equality transports are retained.
No local Kan hypothesis on either raw realization is used.
-/

noncomputable section

universe u

open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalQuillenComparison

open SimplicialEnrichment OriginalRawRightMapping

/-- The SAME original raw Hom map with its exact two vertex-image transports is weak whenever the original realization
is locally weak. -/
theorem targetHomMap_weak {K L : SSet.{u}} (f : K ⟶ L)
    (hf : EnrichedDwyerKan.localWeak (realizationMap f)) (a b : (Δ[0] : SSet.{u}) ⟶ K) :
    SSet.realizationWeakEquivalences (targetHomMap a b f) := by
  let e : hom L ((realizationMap f).obj (SSet.yonedaEquiv a))
      ((realizationMap f).obj (SSet.yonedaEquiv b)) ≅
        hom L (SSet.yonedaEquiv (a ≫ f)) (SSet.yonedaEquiv (b ≫ f)) :=
    eqToIso (congrArg₂ (hom L)
      (OriginalRawRightMapping.vertex_map f a) (OriginalRawRightMapping.vertex_map f b))
  exact SSet.realizationWeakEquivalences.comp_mem _ _
    (hf (SSet.yonedaEquiv a) (SSet.yonedaEquiv b))
    (SSet.realizationWeakEquivalences.of_isIso e.hom)

/-- The actual original realization local weak predicate reflects weakness of EVERY SAME original right mapping-space
map between quasicategories. -/
theorem rightMappingMap_weak_of_realizationLocalWeak {K L : SSet.{u}}
    [SSet.Quasicategory K] [SSet.Quasicategory L] (f : K ⟶ L)
    (hf : EnrichedDwyerKan.localWeak (realizationMap f)) (a b : (Δ[0] : SSet.{u}) ⟶ K) :
    SSet.realizationWeakEquivalences (SSet.mappingSpaceRight.map K a b f) := by
  have hSquare := realizationComparison_map a b f
  have hComposite : SSet.realizationWeakEquivalences
      (OriginalRightCubeRealization.map (SSet.mappingSpaceRight.map K a b f) ≫
        realizationComparison (a ≫ f) (b ≫ f)) :=
    hSquare.symm ▸ SSet.realizationWeakEquivalences.comp_mem _ _
      (realizationComparison_weak a b) (targetHomMap_weak f hf a b)
  exact (OriginalRightCubeRealization.map_weak_iff _).mp
    (SSet.realizationWeakEquivalences.of_postcomp _ _
      (realizationComparison_weak (a ≫ f) (b ≫ f)) hComposite)

end CategoryTheory.CoherentRealization.OriginalQuillenComparison
