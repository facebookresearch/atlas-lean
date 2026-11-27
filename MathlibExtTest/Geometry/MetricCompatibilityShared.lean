/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import MathlibExt.Geometry.MetricCompatibilityShared

/-!
# Tests for `IsMetricCompatible`

Mathlib's metric compatibility of a covariant derivative on the tangent bundle, which asks for
the product rule on vector fields differentiable at the point, implies `IsMetricCompatible`
(`IsMetricCompatible.of_isMetricCompatible`). In particular Mathlib's Levi-Civita connection
satisfies it, on any Riemannian manifold and on the Euclidean plane.
-/

open Bundle MathlibExt.Geometry.MetricCompatibilityShared
open scoped Manifold ContDiff

namespace MetricCompatibilitySharedTests

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

/-- Any covariant derivative that is metric-compatible in Mathlib's sense satisfies the product
rule of `IsMetricCompatible`, unfolded, for smooth vector fields and every tangent vector. -/
example (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (Y Z : Π x : M, TangentSpace I x) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (x : M)
    (v : TangentSpace I x) :
    mvfderiv I (fun y : M ↦ inner ℝ (Y y) (Z y)) x v =
      inner ℝ (cov Y x v) (Z x) + inner ℝ (Y x) (cov Z x v) :=
  IsMetricCompatible.of_isMetricCompatible hcov Y Z hY hZ x v

/-- Mathlib's Levi-Civita connection is compatible with the metric in the sense of
`IsMetricCompatible`. -/
example : IsMetricCompatible (CovariantDerivative.leviCivitaConnection I M) :=
  .of_isMetricCompatible (CovariantDerivative.isMetricCompatible_leviCivitaConnection I)

/-- The product rule of `IsMetricCompatible`, unfolded, for the Levi-Civita connection. -/
example (Y Z : Π x : M, TangentSpace I x) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (x : M)
    (v : TangentSpace I x) :
    mvfderiv I (fun y : M ↦ inner ℝ (Y y) (Z y)) x v =
      inner ℝ (CovariantDerivative.leviCivitaConnection I M Y x v) (Z x) +
        inner ℝ (Y x) (CovariantDerivative.leviCivitaConnection I M Z x v) :=
  IsMetricCompatible.of_isMetricCompatible
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) Y Z hY hZ x v

/-- On the Euclidean plane, with its standard metric, Mathlib's Levi-Civita connection satisfies
`IsMetricCompatible`. -/
example : IsMetricCompatible (CovariantDerivative.leviCivitaConnection
    𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2))) :=
  .of_isMetricCompatible (CovariantDerivative.isMetricCompatible_leviCivitaConnection _)

end MetricCompatibilitySharedTests
