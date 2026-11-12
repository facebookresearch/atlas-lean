/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.ButterflyPayoff
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Probability.Finance.ButterflyPayoff` -/

namespace MathlibExtTest.ButterflyPayoff

open MathlibExt.Probability.Finance.ButterflyPayoff

example : 0 ≤ butterflyPayoff 105 90 100 110 :=
  butterflyPayoff_nonneg (by norm_num) (by norm_num) (by norm_num)

example : 0 ≤ butterflyPayoff 105 90 100 110 :=
  butterflyPayoff_example

example : 0 ≤ ∑ _ : Unit, (1 : ℝ) * butterflyPayoff 105 90 100 110 :=
  butterflyPrice_nonneg (fun _ => by norm_num) (by norm_num) (by norm_num) (by norm_num)

end MathlibExtTest.ButterflyPayoff
