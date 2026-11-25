/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Finset.Max

open scoped BigOperators

namespace Matrix

/-- **Row-normalized spatial averages lie between neighbouring extremes.** Let `W` be a
nonnegative real matrix and let the weights of row `i` sum to one. For any vector `x`, there
are indices `lo` and `hi` of positive weight in that row for which `x lo` and `x hi` are,
respectively, the least and greatest positively weighted values. The average `(W *ᵥ x) i`
lies between them. Only the selected row must sum to one; in particular, it cannot be zero. -/
public theorem exists_mulVec_bounds_of_sum_row_eq_one {m n : Type*} [Fintype n]
    {W : Matrix m n ℝ} (i : m) (hW : ∀ a j, 0 ≤ W a j) (hsum : ∑ j, W i j = 1)
    (x : n → ℝ) :
    ∃ lo hi : n, 0 < W i lo ∧ 0 < W i hi ∧
      (∀ j, 0 < W i j → x lo ≤ x j ∧ x j ≤ x hi) ∧
      x lo ≤ (W *ᵥ x) i ∧ (W *ᵥ x) i ≤ x hi := by
  classical
  let s := Finset.univ.filter (fun j => 0 < W i j)
  have hmem (j : n) : j ∈ s ↔ 0 < W i j := by simp [s]
  have hnonneg (j : n) : 0 ≤ W i j := hW i j
  have hne : s.Nonempty := by
    by_contra hs
    have hz (j : n) : W i j = 0 :=
      le_antisymm (le_of_not_gt (fun hj => hs ⟨j, (hmem j).2 hj⟩)) (hnonneg j)
    simp [hz] at hsum
  obtain ⟨lo, hlo, hlo_min⟩ := s.exists_min_image x hne
  obtain ⟨hi, hhi, hhi_max⟩ := s.exists_max_image x hne
  refine ⟨lo, hi, (hmem lo).1 hlo, (hmem hi).1 hhi,
    fun j hj => ⟨hlo_min j ((hmem j).2 hj), hhi_max j ((hmem j).2 hj)⟩, ?_, ?_⟩
  · calc
      x lo = ∑ j, W i j * x lo := by rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ (W *ᵥ x) i := by
        apply Finset.sum_le_sum
        intro j _
        change W i j * x lo ≤ W i j * x j
        by_cases hj : 0 < W i j
        · exact mul_le_mul_of_nonneg_left (hlo_min j ((hmem j).2 hj)) (hnonneg j)
        · simp [le_antisymm (le_of_not_gt hj) (hnonneg j)]
  · calc
      (W *ᵥ x) i ≤ ∑ j, W i j * x hi := by
        apply Finset.sum_le_sum
        intro j _
        change W i j * x j ≤ W i j * x hi
        by_cases hj : 0 < W i j
        · exact mul_le_mul_of_nonneg_left (hhi_max j ((hmem j).2 hj)) (hnonneg j)
        · simp [le_antisymm (le_of_not_gt hj) (hnonneg j)]
      _ = x hi := by rw [← Finset.sum_mul, hsum, one_mul]

end Matrix
