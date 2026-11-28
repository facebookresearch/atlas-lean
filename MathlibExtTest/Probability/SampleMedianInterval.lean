/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.SampleMedianInterval
import Mathlib.Tactic.NormNum

/-! # Examples for the sample median interval -/

open MetaMathlibExt

private def sample (i : Fin 4) : ℝ := 2 * (i.val : ℝ)

private theorem sample_mono : Monotone sample := by
  intro i j hij
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Fin.le_iff_val_le_val.mp hij)) (by norm_num)

-- For the sorted sample 0, 2, 4, 6, an interior point minimizes absolute deviation.
example : ∀ t : ℝ, (∑ i, |sample i - 3|) ≤ ∑ i, |sample i - t| := by
  apply (sample_median_interval_iff_minimizes sample_mono 3).2
  change sample (1 : Fin 4) ≤ 3 ∧ 3 ≤ sample (2 : Fin 4)
  norm_num [sample]

-- Both middle observations (2 and 4) also minimize absolute deviation.
example : ∀ t : ℝ, (∑ i, |sample i - 2|) ≤ ∑ i, |sample i - t| := by
  apply (sample_median_interval_iff_minimizes sample_mono 2).2
  change sample (1 : Fin 4) ≤ 2 ∧ 2 ≤ sample (2 : Fin 4)
  norm_num [sample]

example : ∀ t : ℝ, (∑ i, |sample i - 4|) ≤ ∑ i, |sample i - t| := by
  apply (sample_median_interval_iff_minimizes sample_mono 4).2
  change sample (1 : Fin 4) ≤ 4 ∧ 4 ≤ sample (2 : Fin 4)
  norm_num [sample]

-- A point below the lower middle observation is not a minimizer.
example : ¬ (∀ t : ℝ, (∑ i, |sample i - 1|) ≤ ∑ i, |sample i - t|) := by
  intro h
  have hlow := ((sample_median_interval_iff_minimizes sample_mono 1).1 h).1
  change sample (1 : Fin 4) ≤ 1 at hlow
  norm_num [sample] at hlow

-- Repeated observations are retained; with all entries equal there is only one minimizer.
example (a m : ℝ) :
    (∀ t : ℝ, (∑ _ : Fin 3, |a - m|) ≤ ∑ _ : Fin 3, |a - t|) ↔ m = a := by
  exact (sample_median_interval_iff_minimizes
    (x := fun _ : Fin 3 => a) monotone_const m).trans
      ⟨fun ⟨hl, hu⟩ => le_antisymm hu hl, fun h => h ▸ ⟨le_rfl, le_rfl⟩⟩

-- There is no middle index for an empty sample: every candidate gives the empty sum.
example (x : Fin 0 → ℝ) (m t : ℝ) : (∑ i, |x i - m|) = ∑ i, |x i - t| := by
  simp
