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

/-! Direct evaluations of the payoff formula, strikes `90, 100, 110`. -/

/-- The documented value at `S = 105`: `15 - 2 * 5 + 0 = 5`. -/
example : butterflyPayoff 105 90 100 110 = 5 := by norm_num [butterflyPayoff]

/-- Peak at the middle strike: `10 - 0 + 0 = 10`. -/
example : butterflyPayoff 100 90 100 110 = 10 := by norm_num [butterflyPayoff]

/-- Zero below the lowest strike. -/
example : butterflyPayoff 80 90 100 110 = 0 := by norm_num [butterflyPayoff]

/-- Zero at the lowest strike. -/
example : butterflyPayoff 90 90 100 110 = 0 := by norm_num [butterflyPayoff]

/-- Zero at the highest strike: `20 - 20 + 0 = 0`. -/
example : butterflyPayoff 110 90 100 110 = 0 := by norm_num [butterflyPayoff]

/-- Zero above the highest strike, since `K2` is the midpoint: `40 - 40 + 20 = 0`. -/
example : butterflyPayoff 130 90 100 110 = 0 := by norm_num [butterflyPayoff]

/-! The inequality `K1 + K3 ≤ 2 * K2`, strikes `0, 2, 3`, where it is strict. -/

/-- Above `K3` the payoff is the positive constant `2 * 2 - 0 - 3 = 1`: `5 - 6 + 2 = 1`. -/
example : butterflyPayoff 5 0 2 3 = 1 := by norm_num [butterflyPayoff]

/-- Nonnegative for every terminal price, although `K2` is not the midpoint. -/
example (S : ℝ) : 0 ≤ butterflyPayoff S 0 2 3 :=
  butterflyPayoff_nonneg (by norm_num) (by norm_num) (by norm_num)

/-- Violating the inequality (`0 + 100 > 2 * 1`) gives a negative payoff above
`K2`: `100 - 198 + 0 = -98`. -/
example : butterflyPayoff 100 0 1 100 = -98 := by norm_num [butterflyPayoff]

end MathlibExtTest.ButterflyPayoff
