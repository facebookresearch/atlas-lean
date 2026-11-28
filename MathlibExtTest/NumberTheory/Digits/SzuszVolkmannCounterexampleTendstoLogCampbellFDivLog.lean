/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.SzuszVolkmannCounterexampleTendstoLogCampbellFDivLog

/-!
# Tests for the growth exponent of Campbell's interpolation

Corollaries of `tendsto_log_campbellF_div_log`: the ratio minus two tends to zero, and
the ratio is eventually strictly between one and three.
-/

@[expose] public section

namespace MathlibExtTest.NumberTheory.Digits.SzuszVolkmannCounterexampleTendstoLogCampbellFDivLog

open MetaMathlibExt

/-- The ratio minus two tends to zero. -/
theorem test_sub_two_tendsto_zero :
    Filter.Tendsto (fun x => Real.log (campbellF x) / Real.log x - 2) Filter.atTop (nhds 0) :=
  tendsto_sub_nhds_zero_iff.mpr tendsto_log_campbellF_div_log

/-- The ratio is eventually strictly between one and three. -/
theorem test_eventually_between_one_and_three :
    ∀ᶠ x in Filter.atTop,
      1 < Real.log (campbellF x) / Real.log x ∧ Real.log (campbellF x) / Real.log x < 3 :=
  (tendsto_log_campbellF_div_log.eventually (eventually_gt_nhds (show (1 : ℝ) < 2 by norm_num))).and
    (tendsto_log_campbellF_div_log.eventually (eventually_lt_nhds (show (2 : ℝ) < 3 by norm_num)))

end MathlibExtTest.NumberTheory.Digits.SzuszVolkmannCounterexampleTendstoLogCampbellFDivLog
