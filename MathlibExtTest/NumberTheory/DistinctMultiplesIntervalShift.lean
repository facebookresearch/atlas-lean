/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DistinctMultiplesIntervalShift
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Positivity

open Filter MetaMathlibExt

-- At the old least length the matching exists on the diagonal and fails at the chosen shift.
example : ∀ᶠ n : ℕ in atTop, ∃ m > 0,
    HasDistinctMultiplesInInterval n n (distinctMultiplesIntervalLength n n) ∧
    ¬ HasDistinctMultiplesInInterval n m (distinctMultiplesIntervalLength n n) := by
  filter_upwards [exists_distinctMultiplesIntervalLength_sub_gt, eventually_ge_atTop 3]
    with n ⟨m, hm, hgap⟩ hn
  have hen : Real.exp 1 < (n : ℝ) := Real.exp_one_lt_three.trans_le (by exact_mod_cast hn)
  have hlog : 1 < Real.log (n : ℝ) := (Real.lt_log_iff_exp_lt (by positivity)).2 hen
  have hpos : 0 < Real.log (Real.log (n : ℝ)) := Real.log_pos hlog
  have hnum : 0 < Real.log (n : ℝ) := zero_lt_one.trans hlog
  have hdiff := lt_trans (by positivity) hgap
  refine ⟨m, hm, hasDistinctMultiplesInInterval_distinctMultiplesIntervalLength n n, ?_⟩
  intro h
  have hle := distinctMultiplesIntervalLength_le_iff.mpr h
  exact (sub_pos.mp hdiff).not_ge (by exact_mod_cast hle)
