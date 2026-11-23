/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.CentralCurvatureHarmonicBundles

/-!
# Central monodromy and rank of centrally curved bundles

The puncture monodromy `exp(2πi d/r)` of a degree-`d`, rank-`r` bundle with normalized central
curvature is scalar: it is trivial when the rank divides the degree, it is `-1` for degree one and
rank two, and it is a primitive cube root of unity (not `1`) for degree one and rank three. The
normalized central curvature conditions exclude the zero bundle.
-/

namespace MathlibExtTest.AlgebraicGeometry.CentralCurvatureHarmonicBundles

open MathlibExt.AlgebraicGeometry.CentralCurvatureHarmonicBundles

/-- When the rank divides the degree, the central monodromy is trivial. -/
example (r : ℕ) (hr : 0 < r) (m : ℤ) : punctureMonodromy (m * r) r = 1 := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (((m * r : ℤ) : ℂ) / (r : ℂ)) =
      (m : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    field_simp
  simp only [punctureMonodromy]
  rw [h, Complex.exp_int_mul_two_pi_mul_I, one_smul]

/-- Degree one and rank two give `-1`. -/
example : punctureMonodromy 1 2 = -(1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  rank_two_degree_one_monodromy

/-- Degree one and rank three give a nontrivial scalar. -/
example : punctureMonodromy 1 3 ≠ 1 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp only [punctureMonodromy, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    mul_one, Int.cast_one, Nat.cast_ofNat] at h00
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h00
  have h3 : (1 : ℂ) / 3 = n := by
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ hpi
    linear_combination hn
  have h3r := congrArg Complex.re h3
  have hn1 : (n : ℝ) * 3 = 1 := by
    have h3r' : (1 : ℝ) / 3 = n := by simpa using h3r
    rw [← h3r']
    norm_num
  have : n * 3 = 1 := by exact_mod_cast hn1
  omega

section RankZero

/-! Rank zero is excluded; positive rank has the normalized coefficient. -/

open MathlibExt.AlgebraicGeometry.KahlerClassGeometry
open MathlibExt.AlgebraicGeometry.ManifoldDifferentialForms
open MathlibExt.AlgebraicGeometry.SmoothHarmonicBundleGeometry
open scoped Manifold ContDiff

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates 1) M]
  [IsManifold 𝓘(ℝ, Coordinates 1) ∞ M] [IsManifold 𝓘(ℂ, Coordinates 1) ∞ M]
  [ExteriorTheory ℝ (Coordinates 1) M] (P : CurveNormalization M)
  (B : SmoothComplexBundle 1 M 0)

/-- On the zero bundle the degree-normalized curvature condition fails for every degree. -/
example (d : ℤ) (A : SmoothConnection B) : ¬ HasNormalizedCentralCurvature P B d A :=
  fun h ↦ lt_irrefl 0 h.1

example (d : ℤ) (h : HermitianMetric B) (H : HolomorphicHiggsField B) :
    ¬ IsCentralHarmonicMetric P B d h H :=
  fun h ↦ lt_irrefl 0 h.1

/-- Degree one, rank two: the central curvature scalar is `-πi/∫ω`. -/
example : centralScalar P 1 2 * (area P : ℂ) = -(Real.pi : ℂ) * Complex.I := by
  have ha : (area P : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt P.area_positive)
  simp only [centralScalar, Int.cast_one, Nat.cast_ofNat]
  field_simp

/-- Degree one, rank two: `(i/2π) tr F` is the positive form `ω/∫ω`. -/
example (x : M) (u v : Coordinates 1) :
    (Complex.I / ((2 : ℂ) * (Real.pi : ℂ))) * Matrix.trace (centralCurvatureValue P 1 2 x u v) =
      ((1 : ℂ) / (area P : ℂ)) * (evaluateTwoForm 1 M P.kahler.form.val x u v : ℂ) := by
  simpa using central_trace_normalization P 1 2 (by norm_num) x u v

end RankZero

end MathlibExtTest.AlgebraicGeometry.CentralCurvatureHarmonicBundles
