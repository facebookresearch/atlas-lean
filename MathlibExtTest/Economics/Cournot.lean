/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Economics.Cournot
import Mathlib.Tactic

/-! # Tests for `MathlibExt.Economics.Cournot`

With demand `10 - Q` and unit costs `1`, outputs `(3, 3)` are the Cournot equilibrium (profit `9`),
and the joint-monopoly split `(9/4, 9/4)` is not. -/

open MathlibExt.Economics.Cournot

namespace MathlibExtTest.Economics.Cournot

/-- (a) With `a = 10`, `b = 1`, `c₁ = c₂ = 1`, the candidate is `(3, 3)`, a Cournot–Nash
equilibrium. -/
example : IsCournotNash 10 1 1 1 3 3 := by
  have h := isCournotNash_linear (a := 10) (b := 1) (c₁ := 1) (c₂ := 1) (by norm_num) (by norm_num)
    (by norm_num)
  rw [show (10 - 2 * (1 : ℝ) + 1) / (3 * 1) = 3 by norm_num] at h
  exact h

/-- (b) Equilibrium profit of each firm is `9`. -/
example : profit 10 1 1 3 3 = 9 := by
  unfold profit
  norm_num

/-- (c) Deviating to `q = 4` against `3` yields `8 < 9`. -/
example : profit 10 1 1 4 3 = 8 ∧ profit 10 1 1 4 3 < 9 := by
  constructor
  · unfold profit
    norm_num
  · unfold profit
    norm_num

/-- (d) The joint-monopoly split `(9/4, 9/4)` is not Cournot–Nash. -/
example : ¬ IsCournotNash 10 1 1 1 (9 / 4) (9 / 4) := by
  intro h
  obtain ⟨-, -, hbr1, -⟩ := h
  have hle := hbr1 3 (by norm_num)
  unfold profit at hle
  norm_num at hle

end MathlibExtTest.Economics.Cournot
