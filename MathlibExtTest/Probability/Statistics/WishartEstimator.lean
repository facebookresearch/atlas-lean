/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.WishartEstimator
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Regression tests for finite real Wishart moments and their fit

The Gaussian expectations below use two rows, three columns and unit entry variance.
The deterministic fixtures are actual data matrices, not probability laws. One gives Gram
eigenvalues `1, 3`; another is an arbitrary nonzero column in two dimensions, so its Gram
is singular despite strictly positive dispersion. The degenerate examples use a single row,
no columns, or a law with zero variance; the almost-sure positive example has two rows,
one column and positive variance. A two-column diagonal sample gives a nonintegral fitted
count `100/9` and fitted entry variance `9/40`.
-/

open MeasureTheory ProbabilityTheory.Wishart
open Matrix (diagonal diagonal_pow)

namespace WishartEstimatorTest

example : (∫ M, firstTrace M ∂matrixLaw 2 3 1) = 6 ∧
    (∫ M, secondTrace M ∂matrixLaw 2 3 1) = 36 ∧
    (∫ M, firstTrace M ^ 2 ∂matrixLaw 2 3 1) = 48 ∧
    (∫ M, 2 * secondTrace M + firstTrace M ^ 2 ∂matrixLaw 2 3 1) = 120 := by
  have h := trace_moments 2 3 1
  norm_num at h
  exact h

example : ∀ᵐ M ∂matrixLaw 2 1 2, 0 < dispersion M :=
  ae_dispersion_pos 2 (by norm_num) (by decide) (by decide)

example : ∀ᵐ M ∂matrixLaw 3 2 0, M = 0 ∧ dispersion M = 0 := ae_zero_of_zero_variance 3 2

example (M : Fin 1 → Fin 3 → ℝ) : dispersion M = 0 := dispersion_one_row M

example (M : Fin 2 → Fin 0 → ℝ) : dispersion M = 0 := dispersion_no_columns M

private def sample : Fin 2 → Fin 4 → ℝ := ![![1, 0, 0, 0], ![0, 1, 1, 1]]

private lemma sample_gram : gram sample = diagonal ![1, 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gram, sample, Matrix.mul_apply, Fin.sum_univ_succ, diagonal]

example : ∑ i, (gram_posSemidef sample).isHermitian.eigenvalues i ^ 2 = 10 := by
  rw [← (trace_power_sums sample).2]
  norm_num [secondTrace, sample_gram, diagonal_pow, Fin.sum_univ_two]

example (r u : ℝ) : (0 < r ∧ 4 = 2 * r * u ∧ 36 = 8 * r * (r + 2) * u ^ 2) ↔
    r = 16 ∧ u = 1 / 8 := by
  have hs : firstTrace sample = 4 := by norm_num [firstTrace, sample_gram, Fin.sum_univ_two]
  have ht : secondTrace sample = 10 := by
    norm_num [secondTrace, sample_gram, diagonal_pow, Fin.sum_univ_two]
  have hd : dispersion sample = 4 := by norm_num [dispersion, hs, ht]
  have hf := (methodOfMoments sample (by rw [hd]; norm_num)).2.2.2 r u
  norm_num [fittedVariance, effectiveCount, hd, hs, ht] at hf ⊢
  exact hf

example (M : Fin 2 → Fin 1 → ℝ) (hn : M ≠ 0) :
    (gram M).det = 0 ∧ 0 < dispersion M ∧ effectiveCount M = 4 := by
  have hs : firstTrace M = (M 0 0) ^ 2 + (M 1 0) ^ 2 := by
    simp [firstTrace, gram, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two, sq]
  have hp : 0 < firstTrace M := by
    rw [hs]
    by_contra! h
    apply hn
    funext i j
    have ha : M 0 0 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (M 0 0), sq_nonneg (M 1 0)])
    have hb : M 1 0 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (M 0 0), sq_nonneg (M 1 0)])
    fin_cases i <;> fin_cases j
    · exact ha
    · exact hb
  have ht : secondTrace M = firstTrace M ^ 2 := by
    simp [hs, secondTrace, sq, gram, Matrix.mul_apply, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
    ring
  have hd : dispersion M = firstTrace M ^ 2 := by rw [dispersion, ht]; push_cast; ring
  refine ⟨?_, hd ▸ sq_pos_of_pos hp, ?_⟩
  · simp [Matrix.det_fin_two, gram, Matrix.mul_apply]; ring
  · rw [effectiveCount, hd, div_eq_iff (pow_ne_zero _ hp.ne')]
    norm_num

-- Two actual columns need not give an integral fitted count.
private def diagonalSample : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![0, 2]]

example : effectiveCount diagonalSample = 100 / 9 ∧ fittedVariance diagonalSample = 9 / 40 := by
  have hX : gram diagonalSample = diagonal ![1, 4] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [gram, diagonalSample, Matrix.mul_apply, Fin.sum_univ_two, diagonal]
  have hs : firstTrace diagonalSample = 5 := by norm_num [firstTrace, hX, Fin.sum_univ_two]
  have ht : secondTrace diagonalSample = 17 := by
    norm_num [secondTrace, hX, diagonal_pow, Fin.sum_univ_two]
  have hd : dispersion diagonalSample = 9 := by norm_num [dispersion, hs, ht]
  norm_num [fittedVariance, effectiveCount, hs, hd]

end WishartEstimatorTest
