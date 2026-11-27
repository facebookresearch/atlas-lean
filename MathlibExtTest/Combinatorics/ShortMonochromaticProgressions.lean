/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ShortMonochromaticProgressions

open MathlibExt.Combinatorics.ShortMonochromaticProgressionsErdosProblem984Wanted

-- At the first positive integer a single finite cutoff works for all common differences.
example : ∃ c : ℕ → Fin 2, ∃ M : ℕ, ∀ d k : ℕ, 0 < d → M ≤ k →
    ∃ i < k, c (1 + i * d) ≠ c 1 := by
  obtain ⟨c, hc⟩ := twoColouringShortProgressions_holds
  obtain ⟨C, hC⟩ := hc 1 zero_lt_one
  obtain ⟨M, hM⟩ := exists_nat_gt C
  refine ⟨c, M, fun d k hd hk ↦ ?_⟩
  by_contra! hm
  have h : (k : ℝ) ≤ C := by simpa using hC 1 d k le_rfl hd hm
  exact (not_lt_of_ge h) (hM.trans_le (by exact_mod_cast hk))
