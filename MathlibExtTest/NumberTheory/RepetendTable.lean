/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RepetendTable
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Tests for `MathlibExt.NumberTheory.RepetendTable` -/

namespace MathlibExtTest.RepetendTable

open MetaMathlibExt

-- Test section: the remainders `c_j = m b^j mod n` and digits `r_j = ⌊b c_j / n⌋` of the
-- statement, for `1/7 = 0.142857…` in base `10`: the remainders return to `1` after six steps.
example : (List.range 7).map (fun j => 1 * 10 ^ j % 7) = [1, 3, 2, 6, 4, 5, 1] := by decide

example : (List.range 6).map (fun j => 10 * (1 * 10 ^ j % 7) / 7) = [1, 4, 2, 8, 5, 7] := by
  decide

-- Test section: the case `k = 1` for an arbitrary proper fraction reads
-- `m/n = r_0/b + c_1/(n b)`, with `c_0 = m mod n` and `c_1 = m b mod n`.
example (m n b : ℕ) (hmn : m < n) (hb : 0 < b) :
    (m : ℚ) / n = ((b * (m % n) / n : ℕ) : ℚ) / b + ((m * b % n : ℕ) : ℚ) / (n * b) := by
  simpa using (long_division_remainder_expansion m n b hmn hb).1 1

-- Test section: a consequence. The first `k` digits approximate `m/n` from below within `b^(-k)`,
-- because the error is `c_k/(n b^k)` with `0 ≤ c_k < n`.
example (m n b k : ℕ) (hmn : m < n) (hb : 0 < b) :
    let s : ℚ := ∑ i ∈ Finset.range k, ((b * (m * b ^ i % n) / n : ℕ) : ℚ) / (b : ℚ) ^ (i + 1)
    0 ≤ (m : ℚ) / n - s ∧ (m : ℚ) / n - s < 1 / (b : ℚ) ^ k := by
  intro s
  have h := (long_division_remainder_expansion m n b hmn hb).1 k
  beta_reduce at h
  have hn : (0 : ℚ) < n := by exact_mod_cast (Nat.zero_le m).trans_lt hmn
  have hbk : (0 : ℚ) < (b : ℚ) ^ k := by positivity
  have hc : ((m * b ^ k % n : ℕ) : ℚ) < n := by exact_mod_cast Nat.mod_lt _ (by omega)
  rw [h, add_sub_cancel_left]
  refine ⟨by positivity, ?_⟩
  rw [div_lt_div_iff₀ (by positivity) hbk, one_mul]
  exact mul_lt_mul_of_pos_right hc hbk

-- Test section: boundary probes. Without `m < n` the case `k = 0` fails: for `3/2` it would read
-- `3/2 = c_0/2` with `c_0 = 3 mod 2 = 1`.
example : ¬ ((3 : ℚ) / 2 = ((3 * 10 ^ 0 % 2 : ℕ) : ℚ) / (2 * 10 ^ 0)) := by norm_num

-- Without `0 < b` the case `k = 1` fails: in base `0` every term of the right side divides by
-- `0`, so for `1/2` it would read `1/2 = 0`.
example : ¬ ((1 : ℚ) / 2 =
    ((0 * (1 * 0 ^ 0 % 2) / 2 : ℕ) : ℚ) / (0 : ℚ) ^ (0 + 1) +
      ((1 * 0 ^ 1 % 2 : ℕ) : ℚ) / (2 * (0 : ℚ) ^ 1)) := by
  norm_num

end MathlibExtTest.RepetendTable
