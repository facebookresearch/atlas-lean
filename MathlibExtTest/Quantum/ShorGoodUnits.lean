/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.ShorGoodUnits

import Mathlib.Tactic.NormNum

/-- Boundary check: the counting bound instantiates for
`N = 3 * 5 = 15`. -/
example : (2 : ℝ) * ((Finset.univ.filter (fun a : (ZMod (3 * 5))ˣ =>
      Even (orderOf a) ∧ a ^ (orderOf a / 2) ≠ -1)).card : ℝ) ≥
    ((Finset.univ : Finset (ZMod (3 * 5))ˣ).card : ℝ) := by
  haveI : NeZero (3 * 5) := ⟨by norm_num⟩
  exact shor_good_units (p := 3) (q := 5) (by decide) (by decide)
    (by norm_num) (by norm_num) (by norm_num)
