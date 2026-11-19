/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.PutCallParity
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for `MathlibExt.Probability.Finance.PutCallParity` -/

namespace MathlibExtTest.PutCallParity

open MathlibExt.Probability.Finance.PutCallParity

/-- Payoff identity at the pinned example values (`S = 110`, `K = 100`). -/
example : callPayoff 110 100 - putPayoff 110 100 = (110 : ℝ) - 100 :=
  callPayoff_sub_putPayoff 110 100

/-- Main parity theorem at the pinned example values: `price` is evaluation at
the single terminal state `ω = 110`, an additive functional, with `R = 1`. -/
example : Pi.evalAddMonoidHom (fun _ : ℝ => ℝ) 110 (fun ω => callPayoff ω 100) -
    Pi.evalAddMonoidHom (fun _ : ℝ => ℝ) 110 (fun ω => putPayoff ω 100) =
      (110 - 0) - 100 / 1 :=
  putCallParity (price := Pi.evalAddMonoidHom (fun _ : ℝ => ℝ) 110) one_pos (by simp)
    (by simp) rfl rfl

/-- Concrete instance from the pinned example. -/
example :
    let price : (ℝ → ℝ) → ℝ := fun f => f 110 / 1
    price (fun ω => callPayoff ω 100) - price (fun ω => putPayoff ω 100) =
      (110 - 0) - 100 / 1 :=
  putCallParity_example

end MathlibExtTest.PutCallParity
