/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Topological 3-manifolds

A **topological 3-manifold** is a topological space that is locally homeomorphic to `ℝ³`,
Hausdorff, and second-countable.  In Mathlib, "locally homeomorphic to `ℝ³`" is exactly a
`ChartedSpace (EuclideanSpace ℝ (Fin 3)) M` instance, so `IsThreeManifold` is a thin predicate
over the `ChartedSpace` API bundling the two remaining point-set conditions.

We also provide the manifold-with-boundary variant `IsThreeManifoldWithBoundary`, modelled on the
Euclidean half-space `EuclideanHalfSpace 3`.

## Main definitions

* `IsThreeManifold M`: `M` is a (boundaryless) topological 3-manifold.
* `IsThreeManifoldWithBoundary M`: `M` is a topological 3-manifold with boundary.

## References

* John M. Lee, *Introduction to Topological Manifolds*, definition of a topological manifold.
-/

@[expose] public section

/-- A **topological 3-manifold**: a Hausdorff, second-countable topological space that is locally
homeomorphic to `ℝ³` (encoded by a `ChartedSpace (EuclideanSpace ℝ (Fin 3)) M` instance). -/
class IsThreeManifold (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] : Prop
    extends T2Space M, SecondCountableTopology M

/-- A **topological 3-manifold with boundary**: a Hausdorff, second-countable topological space
locally homeomorphic to the Euclidean half-space `EuclideanHalfSpace 3`. -/
class IsThreeManifoldWithBoundary (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] : Prop
    extends T2Space M, SecondCountableTopology M

variable (M : Type*) [TopologicalSpace M]

/-- `M` is a topological 3-manifold iff it is Hausdorff and second-countable, given that it is
locally homeomorphic to `ℝ³`. -/
theorem isThreeManifold_iff [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    IsThreeManifold M ↔ T2Space M ∧ SecondCountableTopology M :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => ⟨⟩⟩

/-- A topological 3-manifold is locally compact, since `ℝ³` is. -/
theorem IsThreeManifold.locallyCompactSpace [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsThreeManifold M] : LocallyCompactSpace M :=
  ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) M

/-- Every topological 3-manifold with boundary is Hausdorff. -/
example [ChartedSpace (EuclideanHalfSpace 3) M] [IsThreeManifoldWithBoundary M] : T2Space M :=
  inferInstance

/-- `ℝ³` is a topological 3-manifold (the model, boundaryless case). -/
example : IsThreeManifold (EuclideanSpace ℝ (Fin 3)) := ⟨⟩

/-- The Euclidean half-space is a topological 3-manifold with boundary (boundary case). -/
example : IsThreeManifoldWithBoundary (EuclideanHalfSpace 3) :=
  haveI : SecondCountableTopology (EuclideanHalfSpace 3) :=
    Topology.IsEmbedding.subtypeVal.isInducing.secondCountableTopology
  haveI : T2Space (EuclideanHalfSpace 3) := Topology.IsEmbedding.subtypeVal.t2Space
  ⟨⟩
