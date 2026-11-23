/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

public import MathlibExt.Analysis.ODE.GreensOperator

@[expose] public section

namespace MathlibExt.Analysis.ODE.DirichletSineEigenfunctions

open MathlibExt.Analysis.ODE.GreensOperator (sineBasisFun)

/-!
# Sine eigenfunctions of the Dirichlet Laplacian on `[0, 1]`

For `k : ℕ+`, the function `u_k(x) = √2 sin(kπx)` satisfies the
homogeneous Sturm-Liouville (Dirichlet eigenvalue) problem

  `-u_k'' = (kπ)² u_k` on `ℝ`,  `u_k(0) = u_k(1) = 0`,

and the family `{u_k}` is orthonormal for the `L²` inner product on
`[0, 1]`, in the concrete interval-integral form
`∫₀¹ u_j u_k = δ_{jk}`.

This is the differential-operator side of the Green's operator story.
Batch 6 (`GreensOperator`) proved the integral-operator side: the Green's
operator for `-d²/dx²` with Dirichlet boundary conditions has eigenvalues
`1 / (k²π²)` with these same functions as eigenvectors. The eigenvalue
equation for the differential operator itself, the Dirichlet boundary
values and nonvanishing are proved here. The canonical Green module
already proves the interval orthonormality, which this module reuses, and
the Sturm-Liouville batches (Batch 4 uniqueness, Batch 14 existence)
prove existence and uniqueness for the inhomogeneous problem with a
general potential `V`, without exhibiting any eigenfunctions. Nothing
here is in the pinned Mathlib: Mathlib has the derivatives of `sin` and
`cos` and the fundamental theorem of calculus, but no sine-eigenfunction
statement for the Dirichlet Laplacian.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
the Green's operator / sine-basis material (the target stating that the
Green's operator has orthonormal eigenvectors `u_k(x) = √2 sin(kπx)`
with eigenvalues `λ_k = 1 / (k²π²)`) and the Sturm-Liouville section
(`-u'' + Vu = f` with `u(0) = u(1) = 0`). The statements below describe
the differential spectral counterpart
of the Green operator: `-u_k'' = λ_k u_k` with `λ_k = (kπ)²`.
Both operator APIs use the existing `GreensOperator.sineBasisFun`.
Its existing product-integral theorem supplies orthonormality.
-/

/-- The `k`-th Dirichlet eigenvalue: `λ_k = (kπ)²`, the eigenvalue of
`-d²/dx²` for the eigenfunction `sineBasisFun k`. -/
noncomputable def dirichletLaplacianEigenvalue (k : ℕ+) : ℝ :=
  ((k : ℝ) * Real.pi) ^ 2

/-- First derivative of the `k`-th sine eigenfunction. -/
theorem dirichletSine_hasDerivAt (k : ℕ+) (x : ℝ) :
    HasDerivAt (sineBasisFun k)
      (Real.sqrt 2 * ((k : ℝ) * Real.pi) * Real.cos ((k : ℝ) * Real.pi * x)) x := by
  have h1 : HasDerivAt (fun y : ℝ => (k : ℝ) * Real.pi * y) ((k : ℝ) * Real.pi) x := by
    simpa using (hasDerivAt_id x).const_mul ((k : ℝ) * Real.pi)
  have h3 := (h1.sin).const_mul (Real.sqrt 2)
  convert h3 using 1
  · ext y
    simp [sineBasisFun, mul_assoc]
  · ring

/-- The derivative of the `k`-th sine eigenfunction, as a function. -/
theorem dirichletSine_deriv (k : ℕ+) (x : ℝ) :
    deriv (sineBasisFun k) x =
      Real.sqrt 2 * ((k : ℝ) * Real.pi) * Real.cos ((k : ℝ) * Real.pi * x) :=
  (dirichletSine_hasDerivAt k x).deriv

/-- Second-derivative (eigenvalue) equation for the `k`-th sine
eigenfunction: `u_k'' = -(kπ)² u_k`. -/
theorem dirichletSine_iteratedDeriv_two (k : ℕ+) (x : ℝ) :
    iteratedDeriv 2 (sineBasisFun k) x =
      -dirichletLaplacianEigenvalue k * sineBasisFun k x := by
  have h2 : iteratedDeriv 2 (sineBasisFun k) = deriv (deriv (sineBasisFun k)) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2]
  have hderiv : deriv (sineBasisFun k) =
      fun y => Real.sqrt 2 * ((k : ℝ) * Real.pi) * Real.cos ((k : ℝ) * Real.pi * y) := by
    funext y
    exact dirichletSine_deriv k y
  rw [hderiv]
  have h1 : HasDerivAt (fun y : ℝ => (k : ℝ) * Real.pi * y) ((k : ℝ) * Real.pi) x := by
    simpa using (hasDerivAt_id x).const_mul ((k : ℝ) * Real.pi)
  have hcos : HasDerivAt (fun y : ℝ => Real.cos ((k : ℝ) * Real.pi * y))
      (-Real.sin ((k : ℝ) * Real.pi * x) * ((k : ℝ) * Real.pi)) x := h1.cos
  have h := hcos.const_mul (Real.sqrt 2 * ((k : ℝ) * Real.pi))
  rw [h.deriv]
  simp [sineBasisFun, dirichletLaplacianEigenvalue]
  ring

/-- The Dirichlet eigenvalue equation in Sturm-Liouville form:
`-u_k'' = λ_k u_k` with `λ_k = (kπ)²`. -/
theorem neg_iteratedDeriv_two_eq (k : ℕ+) (x : ℝ) :
    -iteratedDeriv 2 (sineBasisFun k) x =
      dirichletLaplacianEigenvalue k * sineBasisFun k x := by
  rw [dirichletSine_iteratedDeriv_two]
  ring

/-- Left Dirichlet boundary value: `u_k(0) = 0`. -/
theorem dirichletSine_zero (k : ℕ+) : sineBasisFun k 0 = 0 := by
  simp [sineBasisFun]

/-- Right Dirichlet boundary value: `u_k(1) = 0`. -/
theorem dirichletSine_one (k : ℕ+) : sineBasisFun k 1 = 0 := by
  simp only [sineBasisFun]
  have h : (k : ℝ) * Real.pi * (1 : ℝ) = (k : ℝ) * Real.pi := by ring
  rw [h, Real.sin_nat_mul_pi]
  simp

/-- The sine eigenfunctions are smooth. -/
theorem dirichletSine_contDiff (k : ℕ+) : ContDiff ℝ ⊤ (sineBasisFun k) := by
  unfold sineBasisFun
  exact contDiff_const.mul
    (ContDiff.sin ((contDiff_const (c := (k : ℝ) * Real.pi)).mul contDiff_id))

/-- The sine eigenfunctions are nonzero (so they are genuine
eigenfunctions, not the trivial solution). The witness point is
`x = 1 / (2k)`, where `u_k = √2`. -/
theorem dirichletSine_ne_zero (k : ℕ+) : sineBasisFun k ≠ 0 := by
  intro h
  have hk : (0 : ℝ) < (k : ℝ) := by exact_mod_cast k.pos
  have hval : sineBasisFun k (1 / (2 * (k : ℝ))) = Real.sqrt 2 := by
    have harg : (k : ℝ) * Real.pi * (1 / (2 * (k : ℝ))) = Real.pi / 2 := by
      rw [mul_one_div, div_eq_iff (ne_of_gt (by positivity : (0 : ℝ) < 2 * (k : ℝ)))]
      ring
    unfold sineBasisFun
    rw [harg, Real.sin_pi_div_two, mul_one]
  have h0 : sineBasisFun k (1 / (2 * (k : ℝ))) = 0 := by
    rw [h]
    rfl
  rw [hval] at h0
  exact (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne' h0

end MathlibExt.Analysis.ODE.DirichletSineEigenfunctions
