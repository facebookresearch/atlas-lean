/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.ThreeManifold

-- The three-dimensional half-space satisfies the boundary-manifold predicate.
example : IsThreeManifoldWithBoundary (EuclideanHalfSpace 3) := by
  let : SecondCountableTopology (EuclideanHalfSpace 3) :=
    Topology.IsEmbedding.subtypeVal.isInducing.secondCountableTopology
  let : T2Space (EuclideanHalfSpace 3) :=
    Topology.IsEmbedding.subtypeVal.t2Space
  exact ⟨⟩

-- Clients use the bundled properties with a three-dimensional boundary atlas.
example (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsThreeManifoldWithBoundary M] : T2Space M ∧ SecondCountableTopology M :=
  ⟨inferInstance, inferInstance⟩

-- The boundaryless three-dimensional model is unaffected.
example : IsThreeManifold (EuclideanSpace ℝ (Fin 3)) := ⟨⟩

#print axioms IsThreeManifoldWithBoundary
