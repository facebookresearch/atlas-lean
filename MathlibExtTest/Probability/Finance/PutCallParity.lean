/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.PutCallParity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for `MathlibExt.Probability.Finance.PutCallParity` -/

namespace MathlibExtTest.PutCallParity

open MathlibExt.Probability.Finance.PutCallParity

/-- Payoff identity at the pinned example values (`S = 110`, `K = 100`). -/
example : callPayoff 110 100 - putPayoff 110 100 = (110 : ℝ) - 100 :=
  callPayoff_sub_putPayoff 110 100

/-- Main parity theorem at the pinned example values. -/
example : (fun f : ℝ → ℝ => f 110 / 1) (fun ω => callPayoff ω 100) -
    (fun f : ℝ → ℝ => f 110 / 1) (fun ω => putPayoff ω 100) = (110 - 0) - 100 / 1 := by
  have hSub : ∀ f g : ℝ → ℝ, (f 110 - g 110) / 1 = f 110 / 1 - g 110 / 1 :=
    fun f g => by ring
  have hStock : (110 : ℝ) / 1 = 110 - 0 := by norm_num
  have hBond : (100 : ℝ) / 1 = 100 / 1 := rfl
  exact putCallParity (price := fun f : ℝ → ℝ => f 110 / 1) hSub hStock hBond rfl rfl

/-- Concrete instance from the pinned example. -/
example :
    let price : (ℝ → ℝ) → ℝ := fun f => f 110 / 1
    price (fun ω => callPayoff ω 100) - price (fun ω => putPayoff ω 100) =
      (110 - 0) - 100 / 1 :=
  putCallParity_example

end MathlibExtTest.PutCallParity
