/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.AnalyticCurrents
import MathlibExt.AlgebraicGeometry.KahlerClassGeometry
import MathlibExt.AlgebraicGeometry.CoordinateFormIntegrals

open MathlibExt.AlgebraicGeometry
open CoordinateFormIntegrals KahlerClassGeometry AnalyticCurrents ManifoldDifferentialForms
open scoped Manifold ContDiff

example : standardRealFrame 1 (0 : Fin 2) = EuclideanSpace.single 0 (1 : ℂ) := by
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

example : standardRealFrame 1 (1 : Fin 2) = EuclideanSpace.single 0 Complex.I := by
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

example (n : ℕ) (M : Type) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (Coordinates n) M]
    [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [ExteriorTheory ℝ (Coordinates n) M]
    [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] (T : Current n M 1) (h : 2 ≤ n * 2)
    (beta : Forms n M (n * 2 - 2)) :
    differentialFunctional n M T h beta =
      T.functional ((castFormLinear n M (by omega))
        (d ℝ (Coordinates n) M (n * 2 - 2) beta)) := by
  simp [differentialFunctional]

example (n : ℕ) (M : Type) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (Coordinates n) M]
    [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [ExteriorTheory ℝ (Coordinates n) M]
    [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] (T : Current n M 0) (h : 1 ≤ n * 2)
    (beta : Forms n M (n * 2 - 1)) :
    differentialFunctional n M T h beta =
      -T.functional ((castFormLinear n M (by omega))
        (d ℝ (Coordinates n) M (n * 2 - 1) beta)) := by
  simp [differentialFunctional]

/-- On a compact manifold, currents are defined. -/
example (M : Type) [TopologicalSpace M] [CompactSpace M] [ChartedSpace (Coordinates 1) M] :
    Type :=
  Current 1 M 0

/-- Currents are only defined on compact manifolds: `ℂ` is not one. -/
example : True := by
  fail_if_success
    have : Type := Current 1 (Coordinates 1) 0
  trivial
