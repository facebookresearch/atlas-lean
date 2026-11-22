/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootBoundaryInverseSection

/-!
# The actual native full root-boundary chart inverse map

The genuine entire enriched inverse section has its original native
left-extension adjoint. Its same source comparison recovers the full
native root-boundary chart identity by actual universal units. Its
complete original positive-chart restriction is exactly the existing
genuine positive inverse. The remaining source identity is separate.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The same full original native root-boundary chart maps to the actual native all-face source through its genuine
entire enriched inverse section and original native adjunction. -/
def nativeRootBoundaryChartInverse (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    nativeRootBoundaryChart B (n + 1) σ ⟶ nativeSubcomplexChart B (n + 1) σ (boundary (n + 1)) :=
  (EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B σ)) (coneRootBoundaryDiagram (n + 1))
    (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1)))).symm (nativeRootBoundaryInverseSection B n σ)

/-- The actual original native chart inverse reads exactly its same genuine whole enriched root-boundary inverse
section. -/
theorem nativeRootBoundaryChartInverse_homEquiv (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B σ)) (coneRootBoundaryDiagram (n + 1))
      (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))) (nativeRootBoundaryChartInverse B n σ) =
        nativeRootBoundaryInverseSection B n σ :=
  (EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B σ)) (coneRootBoundaryDiagram (n + 1))
    (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1)))).apply_symm_apply (nativeRootBoundaryInverseSection B n σ)

/-- The same actual all-face source comparison recovers the unchanged full native root-boundary chart identity from
its genuine native chart inverse. -/
theorem nativeRootBoundaryChartInverse_source (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    nativeRootBoundaryChartInverse B n σ ≫ nativeBoundaryRootSourceMap B n σ = 𝟙 _ := by
  let j := EnrichedFunctor.opposite (simplexInto B σ)
  let W := coneRootBoundaryDiagram.{u} (n + 1)
  let R := nativeRootBoundaryChart B (n + 1) σ
  let U := EnrichedLeftKan.universalHomEquiv j W R
  let η := EnrichedLeftKan.unit j W
  have hi : U (𝟙 R) = η :=
    (EnrichedLeftKan.universalHomEquiv_unit j W R (𝟙 R)).trans
      ((congrArg (fun f => η ≫ f) ((enrichedDiagramRestrict j).map_id R)).trans (Category.comp_id _))
  apply U.injective
  exact (EnrichedLeftKan.universalHomEquiv_natural_right j W (nativeRootBoundaryChartInverse B n σ)
      (nativeBoundaryRootSourceMap B n σ)).trans
    ((congrArg (fun f => f ≫ (enrichedDiagramRestrict j).map (nativeBoundaryRootSourceMap B n σ))
      (nativeRootBoundaryChartInverse_homEquiv B n σ)).trans
        ((nativeRootBoundaryInverseSection_source B n σ).trans hi.symm))

/-- The same actual full native chart inverse retains exactly its genuine whole original positive-chart inverse
under the unchanged original positive entry. -/
theorem nativeRootBoundaryChartInverse_positive (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    nativePositiveRootBoundaryMap B (n + 1) σ ≫ nativeRootBoundaryChartInverse B n σ = nativeBoundaryPositiveInverse
      B n σ := by
  let j := EnrichedFunctor.opposite (simplexInto B σ)
  let W := coneAfterDiagram (⊥ : Vertex.{u} (n + 1))
  let S := nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))
  apply (EnrichedLeftKan.universalHomEquiv j W S).injective
  exact (enrichedLeftKan_universal_map_post j (coneRootBoundaryAfterMap (n + 1)) (nativeRootBoundaryChartInverse B n
    σ)).trans
    ((congrArg (fun f => coneRootBoundaryAfterMap (n + 1) ≫ f) (nativeRootBoundaryChartInverse_homEquiv B n σ)).trans
      (nativeRootBoundaryInverseSection_positive B n σ))

end SSet.Marked
