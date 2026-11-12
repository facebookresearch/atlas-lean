/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.G12SampleCovariance

/-!
# Tests for ensemble covariance foundations (G12)

Closed checks: the `N = 2` scalar sample variance is `(x1 - x2)^2 / 2`,
identical samples give sample covariance `0`, and the PSD / rank
theorems apply to a concrete two-point data set. The unbiasedness
theorem itself is the module-level statement; its probabilistic
hypotheses are not re-instantiated here.
-/

@[expose] public section

open Matrix

namespace MathlibExt.Probability.G12SampleCovariance

/-- `N = 2` scalar samples: the sample variance is `(x1 - x2)^2 / 2`. -/
example (x1 x2 : ℝ) :
    g12SampleCov !![x1; x2] (0 : Fin 1) (0 : Fin 1) = (x1 - x2) ^ 2 / 2 := by
  rw [g12SampleCov_apply]
  simp only [g12ColMean, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Identical samples give sample covariance `0`. -/
example {N d : ℕ} (hN : 0 < N) (c : Fin d → ℝ) :
    g12SampleCov (Matrix.of fun _ j => c j : Matrix (Fin N) (Fin d) ℝ) = 0 := by
  have hcenter : g12Center (Matrix.of fun _ j => c j : Matrix (Fin N) (Fin d) ℝ) = 0 := by
    ext i j
    simp only [g12Center, Matrix.of_apply, Matrix.zero_apply, g12ColMean, Matrix.of_apply]
    have hsum : (∑ i' : Fin N, c j) = (N : ℝ) * c j := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hsum]
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
    simp
  rw [g12SampleCov, hcenter]
  simp

/-- PSD and rank on a concrete two-point data set in dimension `2`. -/
example : (g12SampleCov !![(1 : ℝ), 0; 0, 1]).PosSemidef :=
  g12SampleCov_posSemidef _

example : (g12SampleCov !![(1 : ℝ), 0; 0, 1]).rank ≤ min 2 (2 - 1) := by
  have h := g12SampleCov_rank_le (N := 2) (d := 2) (by norm_num) !![(1 : ℝ), 0; 0, 1]
  simpa using h

#print axioms g12SampleCov_posSemidef
#print axioms g12SampleCov_rank_le
#print axioms g12SampleCov_expectation

end MathlibExt.Probability.G12SampleCovariance
