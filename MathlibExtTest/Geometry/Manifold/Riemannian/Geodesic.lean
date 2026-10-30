/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.MetricSpace.Geodesic
import MathlibExt.Geometry.Manifold.Riemannian.Volume

/-!
# Tests for geodesics and volume on Riemannian manifolds

Statement shapes for closed geodesics of a closed Riemannian manifold, and the normalization of the
Riemannian volume (Lebesgue measure on `ℝ`). The metric geodesic predicates themselves are tested
in `MathlibExtTest/Topology/MetricSpace/Geodesic.lean`.
-/

open Bundle Manifold Metric Set
open scoped Manifold ContDiff NNReal

noncomputable section

namespace RiemannianGeodesicTests

section Statements

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] [CompactSpace M]

/-- Statement shape: infinitely many geometrically distinct closed geodesics. -/
example : Prop := {S : Set M | ∃ γ : ℝ → M, IsClosedGeodesic γ ∧ range γ = S}.Infinite

end Statements

/-- The Riemannian volume of `ℝ` is Lebesgue measure. -/
example : riemannianVolume 𝓘(ℝ, ℝ) ℝ = MeasureTheory.volume := riemannianVolume_real

end RiemannianGeodesicTests

end
