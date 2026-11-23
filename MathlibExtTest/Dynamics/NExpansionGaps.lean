/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Dynamics.NExpansionGaps
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.NormNum.Basic

/-! # Tests for `MathlibExt.Dynamics.NExpansionGaps` -/

namespace MathlibExtTest.Dynamics.NExpansionGaps

open MetaMathlibExt

-- Test section: the two recursion rules alternate. `d_4 = [j, abb]`, so `d_5` comes from the
-- second rule and ends with `ab, ab`; then `d_6` comes from the first rule and ends with `abb`.
example : (idealPeriodWord 5).drop ((idealPeriodWord 5).length - 4) =
    [[2, 1, 1], [2, 2], [2, 1, 1], [2, 2]] := by
  decide

example : (idealPeriodWord 6).drop ((idealPeriodWord 6).length - 3) =
    [[2, 1, 1], [2, 2], [2, 2]] := by
  decide

-- Test section: block counts computed directly from the recursion, beyond the explicit words.
-- `d_6` has `2^5 = 32` blocks `2, 2` and `(2^6 - 1)/3 = 21` blocks `2, 1, 1`; `d_7` has `64` and
-- `(2^7 + 1)/3 = 43`.
example : (idealPeriodWord 6).count [2, 2] = 32 ∧ (idealPeriodWord 6).count [2, 1, 1] = 21 := by
  decide

set_option maxRecDepth 4000 in
example : (idealPeriodWord 7).count [2, 2] = 64 ∧ (idealPeriodWord 7).count [2, 1, 1] = 43 := by
  decide

-- Test section: Lemma 8 at `n = 10`, where `d_10` has `2^9 = 512` blocks `2, 2` and
-- `(2^10 - 1)/3 = 341` blocks `2, 1, 1`.
example : (idealPeriodWord 10).count [2, 2] = 512 ∧ (idealPeriodWord 10).count [2, 1, 1] = 341 := by
  obtain ⟨hb, ha⟩ := idealPeriodWord_count_blocks (n := 10) (by norm_num)
  refine ⟨hb, ?_⟩
  norm_num at ha
  omega

-- Test section: the two parity forms of the count `c_n` of blocks `2, 1, 1`:
-- `3 c_n = 2^n + 1` for odd `n` and `3 c_n = 2^n - 1` for even `n ≥ 2`.
example {n : ℕ} (hn : Odd n) : 3 * ((idealPeriodWord n).count [2, 1, 1] : ℤ) = 2 ^ n + 1 := by
  have h₁ : 1 ≤ n := by
    obtain ⟨k, rfl⟩ := hn
    omega
  rw [(idealPeriodWord_count_blocks h₁).2, hn.neg_one_pow, sub_neg_eq_add]

example {n : ℕ} (hn : Even n) (hn₂ : 2 ≤ n) :
    3 * ((idealPeriodWord n).count [2, 1, 1] : ℤ) = 2 ^ n - 1 := by
  rw [(idealPeriodWord_count_blocks (by omega)).2, hn.neg_one_pow]

-- Test section: the number of blocks `2, 2` doubles from each word to the next.
example {n : ℕ} (hn : 1 ≤ n) :
    (idealPeriodWord (n + 1)).count [2, 2] = 2 * (idealPeriodWord n).count [2, 2] := by
  rw [(idealPeriodWord_count_blocks (by omega)).1, (idealPeriodWord_count_blocks hn).1,
    ← pow_succ']
  congr 1
  omega

-- Test section: the hypothesis `1 ≤ n` is needed. The placeholder `d_0` is empty, so it has no
-- block `2, 2`, while `2^(0 - 1) = 1` in `ℕ`.
example : ¬ (idealPeriodWord 0).count [2, 2] = 2 ^ (0 - 1) := by
  decide

end MathlibExtTest.Dynamics.NExpansionGaps
