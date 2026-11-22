/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootBoundaryChart
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeProperBoundaryOperator

/-!
# Original proper-image, native-unit and base-transport squares

The proper cone-image lift retains its exact original inclusion.
Naturality of the original left-extension unit gives the complete
supported-to-full unit square. Naturality of the original coherent
base-restriction equality gives its full transport square. These are
proved commuting squares of the same original maps in all degrees.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The whole actual proper-image lift has its unchanged original cone operator as attaching composite. -/
theorem coneProperBoundaryImageSquare {n m : ℕ} (f : Vertex.{u} n →o Vertex.{u} m)
    (hf : ¬ Function.Surjective f) :
    CommSq (coneOperator f) (coneProperBoundaryOperator f hf)
      (𝟙 ((enrichedDiagramRestrict (EnrichedFunctor.opposite (indexMap f))).obj (coneDiagram m)))
      ((enrichedDiagramRestrict (EnrichedFunctor.opposite (indexMap f))).map
        (coneRootBoundaryDiagramInclusion m)) := by
  constructor
  apply EnrichedDiagramMap.ext
  funext i
  apply Hom.ext
  rfl

/-- The genuine whole native root-boundary unit square uses the same original supported inclusion and actual
target-unit maps. -/
theorem nativeRootBoundaryUnitSquare (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    CommSq (coneRootBoundaryDiagramInclusion n)
      (EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ)) (coneRootBoundaryDiagram n))
      (EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ)) (coneDiagram n))
      ((enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B σ))).map
        (nativeRootBoundaryChartMap B n σ)) :=
  ⟨(EnrichedLeftKan.adjunction (EnrichedFunctor.opposite (simplexInto B σ))).unit.naturality
    (coneRootBoundaryDiagramInclusion n)⟩

/-- The original coherent base-restriction transport commutes with the same entire native supported inclusion. -/
theorem nativeRootBoundaryBaseTransportSquare (B : SSet.{u}) {n m : ℕ}
    (f : ⦋n⦌ ⟶ ⦋m⦌) (σ : B _⦋m⦌) :
    CommSq
      ((enrichedDiagramRestrict (EnrichedFunctor.opposite (indexMap f.toOrderHom.uliftMap))).map
        ((enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B σ))).map
          (nativeRootBoundaryChartMap B m σ)))
      ((eqToHom (nativeChartBase_restriction_comp B f σ)).app (nativeRootBoundaryChart B m σ))
      ((eqToHom (nativeChartBase_restriction_comp B f σ)).app (nativeSimplexChart B m σ))
      ((enrichedDiagramRestrict
        (EnrichedFunctor.opposite (simplexInto B (B.map f.op σ)))).map
          (nativeRootBoundaryChartMap B m σ)) :=
  ⟨(eqToHom (nativeChartBase_restriction_comp B f σ)).naturality (nativeRootBoundaryChartMap B m σ)⟩

end SSet.Marked
