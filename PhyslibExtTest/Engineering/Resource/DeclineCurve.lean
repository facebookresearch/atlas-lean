/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Engineering.Resource.DeclineCurve

import Mathlib.Tactic.NormNum

/-!
# Tests for decline curves

Boundary checks for `PhyslibExt.Engineering.Resource.DeclineCurve`: unit
initial rate and decline give rate `exp (-t)` and cumulative
`1 - exp (-t)`, positive at `t = 1`; the zero-decline boundary is the
constant-rate law. The hyperbolic checks use the exact `b = 1 / 2`
instance and exclude the singular endpoints `b = 0` and `b = 1`.
-/

namespace Engineering.Resource.DeclineCurve.Tests

open Engineering.Resource.DeclineCurve

-- qi = D = 1 gives q = exp (-t) and Np = 1 - exp (-t).
example (t : ℝ) : expRate 1 1 t = Real.exp (-t) := by
  unfold expRate
  rw [one_mul]
  congr 1
  ring

example (t : ℝ) : expCumulative 1 1 t = 1 - Real.exp (-t) := by
  have h : (-1 : ℝ) * t = -t := by ring
  simp [expCumulative, expRate, h]

-- Positive cumulative production at t = 1, and zero at t = 0.
example : 0 < expCumulative 1 1 1 := by
  have h : expCumulative (1 : ℝ) 1 1 = 1 - Real.exp (-1) := by
    have h1 : (-1 : ℝ) * (1 : ℝ) = -1 := by ring
    simp [expCumulative, expRate, h1]
  rw [h]
  have hexp : Real.exp (-1 : ℝ) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  linarith

example : expCumulative 1 1 0 = 0 := by
  exact expCumulative_zero 1 1

-- The D = 0 boundary is the constant-rate law: rate stays qi and the
-- cumulative after time 3 at rate 2 is 6.
example : expRate 2 0 5 = 2 ∧ constCumulative 2 3 = 6 := by
  constructor
  · exact expRate_zero_decline 2 5
  · unfold constCumulative
    norm_num

end Engineering.Resource.DeclineCurve.Tests

namespace Engineering.Resource.Decline.Tests

open Engineering.Resource.Decline

-- Exact b = 1 / 2 instance at qi = Di = 1:
-- Np(t) = 2 * (1 - 1 / (1 + t / 2)), so Np(2) = 1.
set_option linter.unusedVariables false in
example (t : ℝ) (ht : 0 ≤ t) :
    hyperbolic_cumulative 1 1 (1 / 2) t = 2 * (1 - 1 / (1 + t / 2)) := by
  have hexp : ((1 / 2 - 1 : ℝ) / (1 / 2)) = -1 := by norm_num
  have hbase : (1 : ℝ) + (1 / 2) * 1 * t = 1 + t / 2 := by ring
  unfold hyperbolic_cumulative
  rw [hexp, Real.rpow_neg_one, hbase, one_div]
  ring

example : hyperbolic_cumulative 1 1 (1 / 2) 2 = 1 := by
  have hexp : ((1 / 2 - 1 : ℝ) / (1 / 2)) = -1 := by norm_num
  have hbase : (1 : ℝ) + (1 / 2) * 1 * 2 = 2 := by norm_num
  unfold hyperbolic_cumulative
  rw [hexp, hbase, Real.rpow_neg_one]
  norm_num

example : hyperbolic_cumulative 1 1 (1 / 2) 0 = 0 := by
  exact hyperbolic_cumulative_zero 1 1 (1 / 2)

-- The endpoints b = 0 and b = 1 fail the standing hypothesis 0 < b < 1;
-- they are excluded singular branches, not evaluated formulas.
example : ¬ ((0 : ℝ) < 1 ∧ (1 : ℝ) < 1) ∧ ¬ ((0 : ℝ) < 0 ∧ (0 : ℝ) < 1) := by
  constructor
  · intro h
    exact absurd h.2 (lt_irrefl (1 : ℝ))
  · intro h
    exact absurd h.1 (lt_irrefl (0 : ℝ))

end Engineering.Resource.Decline.Tests
