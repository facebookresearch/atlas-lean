/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentCubeMappingWeakComparison
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMappingKan

/-!
# Genuine original Hom comparison for a locally Kan enrichment

The actual cube chart, original Hom-complex functor and Brown argument
prove weakness of the constructed Hom-to-right-mapping-space map. Only
the supplied original Hom object needs to be Kan for this weak-map
statement. Genuine local Kan hypotheses on all original Homs also give
the established quasicategory and Kan mapping-space consequences.
-/

noncomputable section
universe u
open CategoryTheory Opposite HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory.CoherentRealization.HomMapping
open SimplicialEnrichment
variable {C : Carrier.{u}} (x y : C)

/-- The constructed whole original Hom-to-right-mapping-space map is a realization weak equivalence whenever
  that supplied original Hom object is Kan. -/
theorem map_weak [SSet.KanComplex (x ⟶[SSet.{u}] y)] :
    SSet.realizationWeakEquivalences (map x y) := by
  apply (SSet.realizationWeakEquivalences.postcomp_iff
    (map x y) (CubeMappingSpace.iso x y).hom
    (SSet.realizationWeakEquivalences.of_isIso (CubeMappingSpace.iso x y).hom)).mp
  exact (CubeMappingSpace.original_comparison x y).symm ▸
    CubeMappingSpace.comparison_weak (x ⟶[SSet.{u}] y)

/-- Under actual local Kan hypotheses, the same original comparison is a weak equivalence of actual Kan complexes. -/
theorem map_kanWeak (hKan : ∀ a b : C, SSet.KanComplex (a ⟶[SSet.{u}] b)) :
    SSet.KanComplex.W (map x y) := by
  let _ : SSet.KanComplex (x ⟶[SSet.{u}] y) := hKan x y
  let _ : SSet.KanComplex (SSet.mappingSpaceRight (coherentNerveFunctor.obj C)
      (HomSimplexEndpoints.vertex x) (HomSimplexEndpoints.vertex y)) :=
    MappingKan.rightMappingKan C hKan x y
  exact (SSet.KanComplex.W_iff_realizationWeakEquivalence (map x y)).mpr (map_weak x y)

end CategoryTheory.CoherentRealization.HomMapping
