/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.QFallingFactorialSums

open Finset

namespace MetaMathlibExt

-- With r = 1 and k = 0 the closed form is the geometric sum `∑_{i<N} q^i = [N]`.
example {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) (N : ℕ) : ∑ i ∈ range N, q ^ i = qBracket q N := by
  simpa [qBracket_one hq1] using sum_qpow_mul_qFalling q hq0 hq1 1 0 N one_pos

-- With r = 1 only the term ℓ = 0 remains: the `q`-analogue of the hockey-stick identity
-- `∑_{i<N} q^i [i]_k = q^k [N]_{k+1} / [k+1]`.
example {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) (k N : ℕ) :
    ∑ i ∈ range N, q ^ i * ∏ j ∈ range k, qBracket q ((i : ℝ) - j) =
      q ^ k / qBracket q ((k : ℝ) + 1) * ∏ j ∈ range (k + 1), qBracket q ((N : ℝ) - j) := by
  simpa using sum_qpow_mul_qFalling q hq0 hq1 1 k N one_pos

-- With N = k the sum vanishes: each `[i]_k` with `i < k` has the factor `[i - i] = [0] = 0`, and
-- on the closed-form side so does `[k]_{k+1}`.
example {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) (r k : ℕ) (hr : 0 < r) :
    ∑ i ∈ range k, q ^ (i * r) * ∏ j ∈ range k, qBracket q ((i : ℝ) - j) = 0 := by
  rw [sum_qpow_mul_qFalling q hq0 hq1 r k k hr]
  exact mul_eq_zero_of_right _
    (prod_eq_zero (mem_range.mpr k.lt_succ_self) (by simp [qBracket_zero]))

-- For q = 2, r = 2, k = 1 and N = 3 the summands are 0, 4 · [1] = 4 and 16 · [2] = 48, and the
-- closed form is (2^4 / [3] + 2^2 [1] / ([3] [2])) [3] [2] = (16/7 + 4/21) · 21 = 52.
example : ∑ i ∈ range 3, (2 : ℝ) ^ (i * 2) * ∏ j ∈ range 1, qBracket 2 ((i : ℝ) - j) = 52 := by
  rw [sum_qpow_mul_qFalling 2 two_pos (by norm_num) 2 1 3 two_pos]
  norm_num [sum_range_succ, prod_range_succ, qBracket]

end MetaMathlibExt
