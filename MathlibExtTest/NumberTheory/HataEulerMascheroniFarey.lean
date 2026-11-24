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

end MetaMathlibExt
