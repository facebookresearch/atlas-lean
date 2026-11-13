/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.OptionPayoffs
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Probability.Finance.OptionPayoffs` -/

namespace MathlibExtTest.OptionPayoffs

open MathlibExt.Probability.Finance.OptionPayoffs

example : europeanCallPayoff 110 100 - europeanPutPayoff 110 100 = 10 :=
  callPayoff_sub_putPayoff_example

example : europeanCallPayoff 110 100 - europeanPutPayoff 110 100 = 110 - 100 :=
  callPayoff_sub_putPayoff 110 100

example (S K : ℝ) : 0 ≤ europeanCallPayoff S K := europeanCallPayoff_nonneg S K

-- Out of the money (`S = 90 < K = 100`) the call payoff is `0`, so the bound is attained.
example : europeanCallPayoff 90 100 = 0 := by
  unfold europeanCallPayoff
  norm_num

example : 0 ≤ europeanCallPayoff 90 100 := europeanCallPayoff_nonneg 90 100

end MathlibExtTest.OptionPayoffs
