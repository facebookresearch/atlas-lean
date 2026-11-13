/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.FuturesMarginAccount

/-! # Tests for `MathlibExt.Probability.Finance.FuturesMarginAccount` -/

namespace MathlibExtTest.FuturesMarginAccount

open MathlibExt.Probability.Finance.FuturesMarginAccount

example : futuresMarginGain 2 (fun i => (i : ℝ) ^ 2) 3 = 18 :=
  futuresMarginGain_example

example : futuresMarginGain 2 (fun i => (i : ℝ) ^ 2) 3
    = 2 * ((((3 : ℕ) : ℝ)) ^ 2 - (((0 : ℕ) : ℝ)) ^ 2) :=
  futuresMarginGain_eq 2 (fun i => (i : ℝ) ^ 2) 3

end MathlibExtTest.FuturesMarginAccount
