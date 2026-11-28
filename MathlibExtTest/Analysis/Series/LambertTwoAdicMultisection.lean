/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Series.LambertTwoAdicMultisection
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- Expand the geometric denominator before taking the coefficient of q^d. The term for
-- (n, m) comes from n^μ q^n times (±q^n)^m, after substituting q ↦ q^scale. For d > 0
-- and scale > 0, only 1 ≤ n ≤ d and 0 ≤ m < d can contribute.
private def lambertCoeff (sign : ℤ) (μ d scale : ℕ) : ℤ :=
  ∑ n ∈ Finset.range d, ∑ m ∈ Finset.range d,
    if scale * (n + 1) * (m + 1) = d then (n + 1 : ℤ) ^ μ * sign ^ m else 0

-- Both j and k can be truncated at d since 2^(j+k) ≥ j+k+1. Vary the multiplier of j
-- to compute the printed and corrected coefficients from the same geometric expansions.
private def multisectionCoeff (weight μ d : ℕ) : ℤ :=
  ∑ j ∈ Finset.range d, ∑ k ∈ Finset.range d, (2 : ℤ) ^ (weight * j + k) *
    (lambertCoeff (-1) μ d (2 ^ (j + k)) -
      2 ^ (μ + 1) * lambertCoeff (-1) μ d (2 ^ (j + k + 1)))

example : lambertCoeff 1 1 2 1 = 3 ∧ multisectionCoeff (1 + 1) 1 2 = 3 := by decide

example : lambertCoeff 1 2 2 1 = 5 ∧ multisectionCoeff (2 + 1) 2 2 = 5 ∧
    multisectionCoeff 2 2 2 = 1 := by decide

private def zeroDisk : {q : ℂ // ‖q‖ < 1} := ⟨0, by simp⟩

private theorem lambertFMu_at_zero (μ : {μ : ℕ // 1 ≤ μ}) : lambertFMu zeroDisk μ = 0 := by
  obtain ⟨C, _, hC⟩ := exists_norm_lambertFMu_le μ (r := 1 / 2) (by norm_num) (by norm_num)
  have hnorm : ‖lambertFMu zeroDisk μ‖ ≤ 0 := by
    simpa [zeroDisk] using hC zeroDisk (by norm_num [zeroDisk])
  exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))

private theorem lambertGMu_at_zero (μ : {μ : ℕ // 1 ≤ μ}) : lambertGMu zeroDisk μ = 0 := by
  rw [lambertGMu_eq_sub_lambertFMu_sq, lambertFMu_at_zero]
  have h : (⟨(zeroDisk : ℂ) ^ 2, by simp [zeroDisk]⟩ : {q : ℂ // ‖q‖ < 1}) = zeroDisk :=
    Subtype.ext (by simp [zeroDisk])
  rw [h, lambertFMu_at_zero, mul_zero, sub_zero]

-- Compute both sides at q = 0 without using the multisection theorem.
example (μ : {μ : ℕ // 1 ≤ μ}) : lambertFMu zeroDisk μ = 0 ∧
    (∑' p : ℕ × ℕ, (2 : ℂ) ^ (((μ : ℕ) + 1) * p.1 + p.2) *
      (lambertGMu ⟨(0 : ℂ) ^ 2 ^ (p.1 + p.2), by simp [zero_pow (by positivity : 2 ^ _ ≠ 0)]⟩ μ
        - 2 ^ ((μ : ℕ) + 1) * lambertGMu
          ⟨(0 : ℂ) ^ 2 ^ (p.1 + p.2 + 1), by simp [zero_pow (by positivity : 2 ^ _ ≠ 0)]⟩ μ)) =
      0 := by
  refine ⟨lambertFMu_at_zero μ, ?_⟩
  have h (n : ℕ) (hn : ‖(0 : ℂ) ^ 2 ^ n‖ < 1) :
      (⟨(0 : ℂ) ^ 2 ^ n, hn⟩ : {q : ℂ // ‖q‖ < 1}) = zeroDisk :=
    Subtype.ext (zero_pow (by positivity))
  simp only [h, lambertGMu_at_zero, mul_zero, sub_zero, tsum_zero]

#check lambertMu_sigma_eq_tsum_twoAdic
