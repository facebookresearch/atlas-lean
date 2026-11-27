/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.StatisticalGenetics.SpearmanKarberExpectVariance
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Tests for `Domains.Biology.StatisticalGenetics.SpearmanKarberExpectVariance`

The variance upper bound is derived from the exact variance (`expect_variance`)
together with the pointwise bound `Pᵢ (1 - Pᵢ) ≤ 1/4`; unbiasedness is checked on the
two-dose instance `k = 1`, `n = 2`.
-/

@[expose] public section

namespace DomainsTest.Biology.StatisticalGenetics.SpearmanKarberExpectVariance

open Finset WantedExt.Biology.StatisticalGenetics.SpearmanKarberWanted

/-- Each `Pᵢ (1 - Pᵢ)` is at most `1/4`. -/
private theorem mul_one_sub_le_quarter (P : ℝ) : P * (1 - P) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (P - 1 / 2)]

/-- **Variance upper bound.** From the exact variance (`expect_variance`), the estimator's
mean squared error is at most `d² (k + 1) / (4 n)`. -/
theorem variance_le (x₀ d : ℝ) (hd : 0 < d) (k n : ℕ) (hn : 1 ≤ n)
    (P : Fin (k + 1) → ℝ) (hP : ∀ i, 0 ≤ P i ∧ P i ≤ 1) (h₀ : P 0 = 0)
    (hk₁ : P (Fin.last k) = 1) (hmono : ∀ i : Fin k, P i.castSucc ≤ P i.succ) :
    expect n P (fun r => (estimator x₀ d n r - spearmanKarber x₀ d P) ^ 2)
      ≤ d ^ 2 * ((k + 1) / 4) / n := by
  rw [(expect_variance x₀ d hd k n hn P hP h₀ hk₁ hmono).2]
  have hsum : (∑ i, P i * (1 - P i)) ≤ (k + 1) / 4 := by
    calc (∑ i, P i * (1 - P i)) ≤ ∑ _i : Fin (k + 1), (1 / 4 : ℝ) :=
          sum_le_sum (fun i _ => mul_one_sub_le_quarter (P i))
      _ = (k + 1) / 4 := by
          simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hd2 : (0 : ℝ) ≤ d ^ 2 := sq_nonneg d
  rw [div_eq_mul_inv, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hn0.le)
  exact mul_le_mul_of_nonneg_left hsum hd2

/-- Two-dose unbiasedness: with `k = 1`, `n = 2` and `Pᵢ = i`, the mean estimate is the
midpoint of the two doses. -/
example (x₀ d : ℝ) (hd : 0 < d) :
    expect 2 (fun i : Fin 2 => (i.val : ℝ)) (estimator x₀ d 2)
      = (x₀ + (x₀ + d)) / 2 := by
  have hP : ∀ i : Fin 2, 0 ≤ (i.val : ℝ) ∧ (i.val : ℝ) ≤ 1 := by
    intro i
    refine ⟨Nat.cast_nonneg _, ?_⟩
    have hi : i.val ≤ 1 := by
      have h2 := i.is_lt
      omega
    exact_mod_cast hi
  have h₀ : (((0 : Fin 2).val : ℕ) : ℝ) = 0 := by simp
  have hk₁ : (((Fin.last 1).val : ℕ) : ℝ) = 1 := by simp
  have hmono : ∀ i : Fin 1, (((i.castSucc.val : ℕ)) : ℝ) ≤ ((i.succ.val : ℕ) : ℝ) := by
    intro i
    rw [Fin.val_castSucc, Fin.val_succ]
    have hi0 : i.val = 0 := by
      have h1 := i.is_lt
      omega
    rw [hi0]
    simp
  have h := (expect_variance x₀ d hd 1 2 one_le_two (fun i : Fin 2 => (i.val : ℝ)) hP h₀
    hk₁ hmono).1
  rw [h]
  simp only [spearmanKarber, Fin.sum_univ_one]
  simp

end DomainsTest.Biology.StatisticalGenetics.SpearmanKarberExpectVariance
