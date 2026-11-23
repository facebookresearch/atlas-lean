/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.SampleMeanSquaredDeviation

import Mathlib.Tactic

@[expose] public section


namespace MathlibExtTest.Probability.SampleMeanSquaredDeviation

open MathlibExt.Probability.FiniteProbability

/-! ### Even sample with two different middle values -/

/-- Four observations with middle values `2` and `3`. -/
noncomputable def evenSample : Fin 4 → ℝ := ![1, 2, 3, 10]

theorem sampleMean_evenSample : sampleMean evenSample = 4 := by
  rw [sampleMean_eq_sum_div]
  simp [evenSample, Fin.sum_univ_four]
  norm_num

/-- The squared loss of the even sample has exactly the minimizer `4`. -/
theorem evenSample_minimizer_iff (c : ℝ) :
    (∀ d, ∑ i, (evenSample i - c) ^ 2 ≤ ∑ i, (evenSample i - d) ^ 2) ↔ c = 4 := by
  rw [forall_sum_sq_sub_le_iff_eq_sampleMean, sampleMean_evenSample]

/-- Neither middle value minimizes the squared loss. -/
theorem evenSample_middle_values_not_minimizers :
    ¬ (∀ d, ∑ i, (evenSample i - 2) ^ 2 ≤ ∑ i, (evenSample i - d) ^ 2) ∧
      ¬ (∀ d, ∑ i, (evenSample i - 3) ^ 2 ≤ ∑ i, (evenSample i - d) ^ 2) := by
  rw [evenSample_minimizer_iff, evenSample_minimizer_iff]
  norm_num

/-- The upper middle value is strictly worse than the mean. -/
theorem evenSample_mean_lt_upper_middle :
    ∑ i, (evenSample i - 4) ^ 2 < ∑ i, (evenSample i - 3) ^ 2 := by
  have h := sum_sq_sub_sampleMean_lt evenSample (c := 3) (by rw [sampleMean_evenSample]; norm_num)
  rwa [sampleMean_evenSample] at h

/-- Contrast: the absolute loss ties at both middle values, so it has no unique minimizer here. -/
theorem evenSample_abs_loss_tie :
    ∑ i, |evenSample i - 2| = ∑ i, |evenSample i - 3| := by
  simp [evenSample, Fin.sum_univ_four, abs_of_nonneg, abs_of_nonpos]
  norm_num [abs_of_nonneg, abs_of_nonpos]

/-! ### All observations equal -/

noncomputable def constantSample : Fin 3 → ℝ := fun _ => 5

theorem sampleMean_constantSample : sampleMean constantSample = 5 := by
  rw [sampleMean_eq_sum_div]
  simp [constantSample]

/-- The only minimizer of a constant sample is its common value, with minimum `0`. -/
theorem constantSample_minimizer_iff (c : ℝ) :
    (∀ d, ∑ i, (constantSample i - c) ^ 2 ≤ ∑ i, (constantSample i - d) ^ 2) ↔ c = 5 := by
  rw [forall_sum_sq_sub_le_iff_eq_sampleMean, sampleMean_constantSample]

theorem constantSample_loss (c : ℝ) :
    ∑ i, (constantSample i - c) ^ 2 = 3 * (5 - c) ^ 2 := by
  rw [sum_sq_sub_eq_sum_sq_sub_sampleMean_add, sampleMean_constantSample]
  simp [constantSample]

/-! ### Simpson reversal -/

/-- Treated units: one in stratum A with value `9`, three in stratum B with value `1`. -/
noncomputable def treated : Fin 1 ⊕ Fin 3 → ℝ := Sum.elim ![9] ![1, 1, 1]

/-- Control units: three in stratum A with value `8`, one in stratum B with value `0`. -/
noncomputable def control : Fin 3 ⊕ Fin 1 → ℝ := Sum.elim ![8, 8, 8] ![0]

/-- The mean of `n + 1` copies of `a`. -/
theorem sampleMean_const_fin (n : ℕ) (a : ℝ) : sampleMean (fun _ : Fin (n + 1) => a) = a := by
  rw [sampleMean_eq_sum_div]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem sampleMean_treated : sampleMean treated = 3 := by
  have h := card_mul_sampleMean_sumElim (fun _ : Fin 1 => (9 : ℝ)) (fun _ : Fin 3 => (1 : ℝ))
  rw [sampleMean_const_fin 0, sampleMean_const_fin 2, Fintype.card_fin, Fintype.card_fin] at h
  have ht : treated = Sum.elim (fun _ : Fin 1 => (9 : ℝ)) (fun _ : Fin 3 => (1 : ℝ)) := by
    funext i; rcases i with i | i <;> fin_cases i <;> rfl
  rw [ht]
  push_cast at h
  linarith

theorem sampleMean_control : sampleMean control = 6 := by
  have h := card_mul_sampleMean_sumElim (fun _ : Fin 3 => (8 : ℝ)) (fun _ : Fin 1 => (0 : ℝ))
  rw [sampleMean_const_fin 2, sampleMean_const_fin 0, Fintype.card_fin, Fintype.card_fin] at h
  have hc : control = Sum.elim (fun _ : Fin 3 => (8 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) := by
    funext i; rcases i with i | i <;> fin_cases i <;> rfl
  rw [hc]
  push_cast at h
  linarith

/-- Within each stratum the treated mean exceeds the control mean, but the pooled least-squares
location of the treated units is below that of the control units. -/
theorem simpson_reversal :
    sampleMean (![9] : Fin 1 → ℝ) > sampleMean (![8, 8, 8] : Fin 3 → ℝ) ∧
      sampleMean (![1, 1, 1] : Fin 3 → ℝ) > sampleMean (![0] : Fin 1 → ℝ) ∧
      (∀ c, (∀ d, ∑ i, (treated i - c) ^ 2 ≤ ∑ i, (treated i - d) ^ 2) ↔ c = 3) ∧
      (∀ c, (∀ d, ∑ i, (control i - c) ^ 2 ≤ ∑ i, (control i - d) ^ 2) ↔ c = 6) := by
  refine ⟨?_, ?_, fun c => ?_, fun c => ?_⟩
  · simp only [sampleMean_eq_sum_div, Fintype.card_fin, Fin.sum_univ_one, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    norm_num
  · simp only [sampleMean_eq_sum_div, Fintype.card_fin, Fin.sum_univ_one, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    norm_num
  · rw [forall_sum_sq_sub_le_iff_eq_sampleMean, sampleMean_treated]
  · rw [forall_sum_sq_sub_le_iff_eq_sampleMean, sampleMean_control]

/-! ### Unweighted group averages versus the pooled mean -/

/-- Groups of sizes `1` and `3` with different means: the pooled mean is not the unweighted
average `2` of the group means. -/
theorem unequal_sizes_pooled_ne_average :
    sampleMean (Sum.elim (![0] : Fin 1 → ℝ) (![4, 4, 4] : Fin 3 → ℝ)) ≠
      (sampleMean (![0] : Fin 1 → ℝ) + sampleMean (![4, 4, 4] : Fin 3 → ℝ)) / 2 := by
  rw [Ne, sampleMean_sumElim_eq_average_iff]
  simp only [Fintype.card_fin, sampleMean_eq_sum_div, Fin.sum_univ_one, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  norm_num

/-- With the same unequal groups, the unweighted average `2` loses to the pooled mean `3` under
squared loss. -/
theorem unequal_sizes_average_not_minimizer :
    ¬ (∀ d, ∑ i, (Sum.elim (![0] : Fin 1 → ℝ) (![4, 4, 4] : Fin 3 → ℝ) i - 2) ^ 2 ≤
      ∑ i, (Sum.elim (![0] : Fin 1 → ℝ) (![4, 4, 4] : Fin 3 → ℝ) i - d) ^ 2) := by
  rw [forall_sum_sq_sub_le_iff_eq_sampleMean]
  have h := card_mul_sampleMean_sumElim (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 3 => (4 : ℝ))
  rw [sampleMean_const_fin 0, sampleMean_const_fin 2, Fintype.card_fin, Fintype.card_fin] at h
  have hg : Sum.elim (![0] : Fin 1 → ℝ) (![4, 4, 4] : Fin 3 → ℝ) =
      Sum.elim (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 3 => (4 : ℝ)) := by
    funext i; rcases i with i | i <;> fin_cases i <;> rfl
  rw [hg]
  intro h2
  rw [← h2] at h
  norm_num at h

/-- Groups of equal size: the pooled mean is the unweighted average even though the group means
differ. -/
theorem equal_sizes_pooled_eq_average :
    sampleMean (Sum.elim (![0, 0] : Fin 2 → ℝ) (![4, 4] : Fin 2 → ℝ)) =
      (sampleMean (![0, 0] : Fin 2 → ℝ) + sampleMean (![4, 4] : Fin 2 → ℝ)) / 2 :=
  (sampleMean_sumElim_eq_average_iff _ _).mpr (Or.inl rfl)

/-! ### Zero-mass boundaries -/

/-- Empty sample: the decomposition holds with both sides `0`. -/
theorem empty_sample_decomposition (x : Fin 0 → ℝ) (c : ℝ) :
    ∑ i, (x i - c) ^ 2 = ∑ i, (x i - sampleMean x) ^ 2 + 0 * (sampleMean x - c) ^ 2 := by
  have h := sum_sq_sub_eq_sum_sq_sub_sampleMean_add x c
  rwa [Fintype.card_fin, Nat.cast_zero] at h

/-- Empty sample: the junk mean is `0`, and the minimizing inequality itself still applies
(both sums are `0`). The standalone inequality therefore needs no `Nonempty ι`. -/
theorem empty_sample_mean_zero_and_le (x : Fin 0 → ℝ) (c : ℝ) :
    sampleMean x = 0 ∧ ∑ i, (x i - sampleMean x) ^ 2 ≤ ∑ i, (x i - c) ^ 2 := by
  refine ⟨?_, sum_sq_sub_sampleMean_le x c⟩
  simp [sampleMean_eq_sum_div, Fintype.card_fin]

/-- Empty sample: uniqueness fails, because every point (here `0` and `1`) is a minimizer; so
`Nonempty ι` cannot be dropped from the uniqueness statements. -/
theorem empty_sample_not_unique (x : Fin 0 → ℝ) :
    ¬ ∃! c : ℝ, ∀ d, ∑ i, (x i - c) ^ 2 ≤ ∑ i, (x i - d) ^ 2 := by
  rintro ⟨c, -, hc⟩
  have h0 := hc 0 (fun d => by simp)
  have h1 := hc 1 (fun d => by simp)
  norm_num [← h0] at h1

/-- Empty group: the pooled mean `2` is not the unweighted average `(0 + 2) / 2` that uses the
junk mean `0` of the empty group, as the characterization predicts (sizes `0 ≠ 2`, means
`0 ≠ 2`). -/
theorem empty_group_pooled_ne_average :
    sampleMean (Sum.elim (Fin.elim0 : Fin 0 → ℝ) (![2, 2] : Fin 2 → ℝ)) ≠
      (sampleMean (Fin.elim0 : Fin 0 → ℝ) + sampleMean (![2, 2] : Fin 2 → ℝ)) / 2 := by
  rw [Ne, sampleMean_sumElim_eq_average_iff]
  simp only [Fintype.card_fin, sampleMean_eq_sum_div, Finset.univ_eq_empty, Finset.sum_empty,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

end MathlibExtTest.Probability.SampleMeanSquaredDeviation
