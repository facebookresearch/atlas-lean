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
Euclidean half-space `EuclideanHalfSpace 2`.

## Main definitions

* `IsThreeManifold M`: `M` is a (boundaryless) topological 3-manifold.
* `IsThreeManifoldWithBoundary M`: `M` is a topological 3-manifold with boundary.

## References

* John M. Lee, *Introduction to Topological Manifolds*, definition of a topological manifold.
-/

@[expose] public section

/-- **Topological 3-manifold.** Let $M$ be a topological space equipped with an atlas of charts,
each a homeomorphism from an open subset of $M$ onto an open subset of $\mathbb{R}^3$, whose domains
cover $M$. Then $M$ is a topological 3-manifold if it is Hausdorff and second-countable. -/
class IsThreeManifold (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] : Prop
    extends T2Space M, SecondCountableTopology M

/-- A **topological 3-manifold with boundary**: a Hausdorff, second-countable topological space
locally homeomorphic to the Euclidean half-space `EuclideanHalfSpace 2`. -/
class IsThreeManifoldWithBoundary (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M] : Prop
    extends T2Space M, SecondCountableTopology M

variable (M : Type*) [TopologicalSpace M]

/-- **Characterization of topological 3-manifolds.** Let $M$ be a topological space equipped
with an atlas of charts modelled on $\mathbb{R}^3$, so that $M$ is locally homeomorphic to
$\mathbb{R}^3$. Then $M$ is a topological 3-manifold if and only if $M$ is Hausdorff and
second-countable. -/
theorem isThreeManifold_iff [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    IsThreeManifold M ↔ T2Space M ∧ SecondCountableTopology M :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => ⟨⟩⟩

/-- **Topological 3-manifolds are locally compact.** Every topological 3-manifold $M$ is locally
compact, since $\mathbb{R}^3$ is. -/
theorem IsThreeManifold.locallyCompactSpace [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsThreeManifold M] : LocallyCompactSpace M :=
  ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) M

/-- Every topological 3-manifold with boundary is Hausdorff. -/
example [ChartedSpace (EuclideanHalfSpace 2) M] [IsThreeManifoldWithBoundary M] : T2Space M :=
  inferInstance

/-- `ℝ³` is a topological 3-manifold (the model, boundaryless case). -/
example : IsThreeManifold (EuclideanSpace ℝ (Fin 3)) := ⟨⟩

/-- The Euclidean half-space is a topological 3-manifold with boundary (boundary case). -/
example : IsThreeManifoldWithBoundary (EuclideanHalfSpace 2) :=
  haveI : SecondCountableTopology (EuclideanHalfSpace 2) :=
    Topology.IsEmbedding.subtypeVal.isInducing.secondCountableTopology
  haveI : T2Space (EuclideanHalfSpace 2) := Topology.IsEmbedding.subtypeVal.t2Space
  ⟨⟩
