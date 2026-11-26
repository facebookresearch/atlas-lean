/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HataEulerMascheroniFarey
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

-- Splitting [1/2, 1] at 2/3 leaves a remainder of 1/12.
example : (3 : ℝ) / 2 - 7 / 12 - 5 / 6 = 1 / 12 := by
  obtain ⟨hsplit, hdet⟩ := farey_interval_mediant_telescoping
    (a := 1) (b := 2) (c := 1) (d := 1) (by decide) (by decide) (by decide)
  convert hsplit.trans hdet using 2 <;> norm_num

-- A whole reciprocal interval attains both endpoint bounds, including [1/2, 1] at k = 1.
example (k : ℕ) (hk : 0 < k) :
    ∃ n : ℕ, 0 < n ∧ Set.Icc ((1 : ℚ) / (k + 1)) (1 / k) ⊆
      Set.Icc (1 / (n + 1)) (1 / n) := by
  obtain ⟨n, hn, hl, hr⟩ := farey_interval_subset_reciprocal_interval
    (a := 1) (b := k + 1) (c := 1) (d := k) (by decide) hk (by simp)
  exact ⟨n, hn, Set.Icc_subset_Icc (by simpa using hl) (by simpa using hr)⟩

-- The leftmost interval attains the length bound in every generation.
example (n : ℕ) : IsGreatest
    ((fun q : ℕ × ℕ × ℕ × ℕ => (q.2.2.1 : ℚ) / q.2.2.2 - q.1 / q.2.1) ''
      (fareyGeneration n : Set (ℕ × ℕ × ℕ × ℕ))) (1 / (n + 1)) := by
  constructor
  · refine ⟨(0, 1, 1, n + 1), ?_, by simp⟩
    change (0, 1, 1, n + 1) ∈ fareyGeneration n
    induction n with
    | zero => decide
    | succ n ih =>
      apply Finset.mem_biUnion.mpr
      exact ⟨(0, 1, 1, n + 1), ih, by simp [Nat.add_comm 1 (n + 1)]⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact fareyGeneration_length_le hq

end MetaMathlibExt
