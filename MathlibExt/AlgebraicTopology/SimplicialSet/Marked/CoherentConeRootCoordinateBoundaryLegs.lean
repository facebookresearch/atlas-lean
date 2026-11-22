/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinatePairs
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeLowerRootFace
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeUpperRootBoundaryUnit

/-!
# The unchanged original complete coordinate-boundary legs at the root

The original marked coordinate-boundary multicofork retains every
original lower and upper coordinate inclusion. The genuine original
supported-root isomorphism gives their unchanged entries into the
same complete marked root-boundary coefficient and full root cone.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- Every whole original marked coordinate enters the unchanged supported root-boundary coefficient by its original
full coordinate multicofork leg. -/
def coneRootCoordinateFaceToBoundary (n : ℕ) (a : RootCoordinateIndex.{u} n) :
    coneRootCoordinateFaceWeight n a ⟶ coneRootBoundaryMarked (⊥ : Vertex.{u} (n + 1)) :=
  ((coneCoordinateBoundaryDiagram (⊥ : Vertex.{u} (n + 1))).multicofork.map
    (subcomplexFunctor (coneWeight (⊥ : Vertex.{u} (n + 1))))).π a ≫ (coneRootBoundaryRootIso (n + 1)).inv

/-- Every original complete marked coordinate-boundary leg keeps its unchanged full root-cone inclusion. -/
theorem coneRootCoordinateFaceToBoundary_inclusion (n : ℕ) (a : RootCoordinateIndex.{u} n) :
    coneRootCoordinateFaceToBoundary n a ≫ coneRootBoundaryInclusion (⊥ : Vertex.{u} (n + 1)) =
      coneRootCoordinateFaceInclusion n a := by
  apply Hom.ext
  rfl

/-- The original lower root-coordinate boundary entry is the same original complete coordinate multicofork leg. -/
theorem coneRootCoordinateFaceToBoundary_lower (n : ℕ) (j : Fin (n + 2)) (hj : 0 < j) :
    coneRootCoordinateFaceToBoundary.{u} n (coneRootLowerIndex n j hj) = coneLowerRootFaceToBoundary j hj := rfl

/-- The original upper root-coordinate boundary entry is the same original complete coordinate multicofork leg. -/
theorem coneRootCoordinateFaceToBoundary_upper (n : ℕ) (j : Fin (n + 2)) (hj : 0 < j) :
    coneRootCoordinateFaceToBoundary.{u} n (coneRootUpperIndex n j hj) = coneUpperRootFaceToBoundary j hj := rfl

end SSet.Marked.CoherentWeight
