/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# An auxiliary logarithmic inequality for Mandl's inequality
-/

namespace MetaMathlibExt

/-- **An auxiliary inequality in $\log n$ and $\log\log n$.** For every integer $n \ge 2$, with
$L = \log n$,
$$\frac{4.151332(\log L - 2)}{L} + \frac{3.151332(\log L - 1)}{L} +
\frac{3.151332(\log L - 2)}{L^2} \le 1.$$

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Proposition 3, inequality (25) (`integers-2025-A58-prop-3`). -/
public theorem loglog_ratio_sum_le_one (n : ℕ) (hn : 2 ≤ n) :
    4.151332 * (Real.log (Real.log n) - 2) / Real.log n +
        3.151332 * (Real.log (Real.log n) - 1) / Real.log n +
        3.151332 * (Real.log (Real.log n) - 2) / Real.log n ^ 2 ≤ 1 := by
  set L := Real.log n
  have hL : 0 < L := Real.log_pos (Nat.one_lt_cast.mpr hn)
  -- Bound log L by its tangent at 8, using log 8 = 3 log 2.
  have hlog : Real.log L ≤ L / 8 + 5 / 4 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < L / 8 by positivity)
    rw [Real.log_div hL.ne' (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at h
    linarith only [h, Real.log_two_lt_d9]
  field_simp
  nlinarith only [hlog, mul_le_mul_of_nonneg_right hlog hL.le, hL.le, sq_nonneg L]

end MetaMathlibExt
