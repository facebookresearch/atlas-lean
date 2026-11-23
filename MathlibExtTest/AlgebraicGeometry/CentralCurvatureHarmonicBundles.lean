/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.CentralCurvatureHarmonicBundles

/-!
# Central monodromy of projectively flat bundles

The puncture monodromy `exp(2πi d/r)` of a degree-`d`, rank-`r` projectively flat bundle is
scalar: it is trivial when the rank divides the degree, it is `-1` for degree one and rank two,
and it is a primitive cube root of unity (not `1`) for degree one and rank three.
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

end MathlibExtTest.AlgebraicGeometry.CentralCurvatureHarmonicBundles
