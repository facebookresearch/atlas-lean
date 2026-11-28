/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ErdosDivisibilityFamilyGrowth

open MathlibExt.NumberTheory.ErdosDivisibilityFamilyGrowthWanted

-- The positive answer forces `π n < F n` for every large `n`.
example : ∀ᶠ n : ℕ in Filter.atTop, Nat.primeCounting n < F n := by
  obtain ⟨C, hC, h⟩ := conjecture_holds
  filter_upwards [h.eventually (lt_mem_nhds hC), Filter.eventually_gt_atTop 1] with n hn hn1
  have hden : 0 < (n : ℝ) ^ ((2 : ℝ) / 3) / Real.log n ^ 2 := by
    have := Real.log_pos (by exact_mod_cast hn1 : (1 : ℝ) < n)
    positivity
  have hpos := (div_pos_iff_of_pos_right hden).mp hn
  push_cast at hpos
  exact_mod_cast sub_pos.mp hpos

-- A set of primes is good.
example : Good {2, 3, 5, 7} := by
  unfold Good
  decide

-- `b = c` is allowed: `4 ∣ 2 * 2`, so `{2, 4}` is not good.
example : ¬ Good {2, 4} := by
  unfold Good
  decide

-- No element may divide the product of two others: `6 ∣ 10 * 15`.
example : ¬ Good {6, 10, 15} := by
  unfold Good
  decide

-- `1` divides every product, so it is good only on its own.
example : Good {1} ∧ ¬ Good {1, 2} := by
  unfold Good
  decide

-- Elements must be positive.
example : ¬ Good {0} := by
  unfold Good
  decide

-- Products of prime triples meeting pairwise in one prime form a good set, as in the lower bound.
example : Good {2 * 3 * 5, 2 * 7 * 11, 3 * 7 * 13} := by
  unfold Good
  decide

-- `F 3 = 2`: `{2, 3}` is good, but `{1, 2, 3}` is not, since `1 ∣ 2 * 3`.
example : F 3 = 2 := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨{2, 3}, by decide, by unfold Good; decide, rfl⟩, ?_⟩
  rintro k ⟨A, hA, hgood, rfl⟩
  have key : ∀ B ∈ (Finset.Icc 1 3).powerset, Good B → B.card ≤ 2 := by
    unfold Good
    decide
  exact key A (Finset.mem_powerset.mpr hA) hgood
