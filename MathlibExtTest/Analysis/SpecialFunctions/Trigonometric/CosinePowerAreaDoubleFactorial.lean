/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Trigonometric.CosinePowerAreaDoubleFactorial
import Mathlib.Tactic.NormNum

/-! # Tests for the double-factorial limits of cosine-power areas -/

namespace MathlibExtTest.CosinePowerAreaDoubleFactorial

open Real Filter Topology MetaMathlibExt

-- The odd sum includes its zero index, representing `(-1)!!`.
example : Tendsto (cosPowArea 1) atTop (𝓝 (8 / π)) := by
  simpa using (tendsto_cosPowArea_doubleFactorial 1).1 (by decide)

-- The even sum begins at exponent two.
example : Tendsto (cosPowArea 2) atTop (𝓝 (4 / π)) := by
  convert (tendsto_cosPowArea_doubleFactorial 2).2 (by decide) (by decide) using 2
  norm_num [Nat.doubleFactorial, Nat.factorial_succ]
  ring

-- At exponents three and four each sum has two terms.
example : Tendsto (cosPowArea 3) atTop (𝓝 (56 / (9 * π))) := by
  convert (tendsto_cosPowArea_doubleFactorial 3).1 (by decide) using 2
  norm_num [Nat.doubleFactorial, Nat.factorial_succ, Finset.sum_range_succ]
  ring

example : Tendsto (cosPowArea 4) atTop (𝓝 (4 / π)) := by
  convert (tendsto_cosPowArea_doubleFactorial 4).2 (by decide) (by decide) using 2
  norm_num [Nat.doubleFactorial, Nat.factorial_succ, Finset.sum_range_succ]
  ring

/-- info: 'MetaMathlibExt.tendsto_cosPowArea_doubleFactorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MetaMathlibExt.tendsto_cosPowArea_doubleFactorial

end MathlibExtTest.CosinePowerAreaDoubleFactorial
