/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.DirichletSineEigenfunctions

@[expose] public section

open MathlibExt.Analysis.ODE.DirichletSineEigenfunctions
open MathlibExt.Analysis.ODE.GreensOperator (sineBasisFun sine_product_integral)

namespace MathlibExtTest.Analysis.ODE.DirichletSineEigenfunctionsTests

/-!
# Tests for Dirichlet sine eigenfunctions

Concrete checks: the first eigenfunction at the midpoint, the eigenvalue
equation for `k = 1`, Dirichlet boundary values, nonvanishing,
orthogonality of distinct eigenfunctions, and normalization.
-/

/-- The first eigenfunction at the midpoint is `√2`. -/
example : sineBasisFun 1 (1 / 2) = Real.sqrt 2 := by
  have harg : (((1 : ℕ+) : ℝ) * Real.pi * (1 / 2) = Real.pi / 2) := by
    push_cast
    ring
  unfold sineBasisFun
  rw [harg, Real.sin_pi_div_two, mul_one]

/-- The first Dirichlet eigenvalue is `π²`. -/
example : dirichletLaplacianEigenvalue 1 = Real.pi ^ 2 := by
  simp [dirichletLaplacianEigenvalue]

/-- The eigenvalue equation for `k = 1` at an arbitrary point. -/
example (x : ℝ) :
    iteratedDeriv 2 (sineBasisFun 1) x = -(Real.pi ^ 2) * sineBasisFun 1 x := by
  have h := dirichletSine_iteratedDeriv_two 1 x
  simpa [dirichletLaplacianEigenvalue] using h

/-- The Sturm-Liouville form of the eigenvalue equation for `k = 2`. -/
example (x : ℝ) :
    -iteratedDeriv 2 (sineBasisFun 2) x =
      dirichletLaplacianEigenvalue 2 * sineBasisFun 2 x :=
  neg_iteratedDeriv_two_eq 2 x

/-- Dirichlet boundary values of the second eigenfunction. -/
example : sineBasisFun 2 0 = 0 ∧ sineBasisFun 2 1 = 0 :=
  ⟨dirichletSine_zero 2, dirichletSine_one 2⟩

/-- The first eigenfunction is nonzero. -/
example : sineBasisFun 1 ≠ 0 :=
  dirichletSine_ne_zero 1

/-- The first eigenfunction is smooth. -/
example : ContDiff ℝ ⊤ (sineBasisFun 1) :=
  dirichletSine_contDiff 1

/-- The first two eigenfunctions are orthogonal on `[0, 1]`. -/
example : ∫ x in (0 : ℝ)..1, sineBasisFun 1 x * sineBasisFun 2 x = 0 := by
  rw [sine_product_integral]
  simp

/-- The third eigenfunction is normalized on `[0, 1]`. -/
example : ∫ x in (0 : ℝ)..1, (sineBasisFun 3 x) ^ 2 = 1 :=
  by simpa [pow_two] using sine_product_integral (3 : ℕ+) 3

end MathlibExtTest.Analysis.ODE.DirichletSineEigenfunctionsTests
