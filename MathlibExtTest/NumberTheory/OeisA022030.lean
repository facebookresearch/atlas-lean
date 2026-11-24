/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/OEIS/22030.lean` (Formal Conjectures):
Copyright The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors.
Adapted portion: the recurrence statement in the source-faithfulness example.
-/

module

import MathlibExt.NumberTheory.OeisA022030

/-! # OEIS A022030 and Barker's linear recurrence -/

open MathlibExt.NumberTheory.OeisA022030Wanted

-- The first terms, from the alternating ceiling and floor steps.
example : a 0 = 4 ∧ a 1 = 16 ∧ a 2 = 63 ∧ a 3 = 249 ∧ a 4 = 984 ∧ a 5 = 3889 ∧
    a 6 = 15370 := by decide

-- The statement in Formal Conjectures, using the same sequence from the canonical module.
example (n : ℕ) (hn : 4 ≤ n) : a n = 4 * a (n - 1) - a (n - 3) + a (n - 4) :=
  conjecture_holds n hn

-- The first ceiling step is tight: `16 ^ 2 - 4 * 63 = 4 = a 0`, so `a 2 = 63` is the largest
-- integer below `16 ^ 2 / 4 = 64`.
example : a 1 ^ 2 - a 0 * a 2 = a 0 := by decide

-- The first floor step: `16 * 249 - 63 ^ 2 = 15 < a 1`, so `a 3 = 249` is the smallest integer
-- above `63 ^ 2 / 16`.
example : a 1 * a 3 - a 2 ^ 2 = 15 := by decide

-- The smallest instance of the recurrence.
example : a 4 = 4 * a 3 - a 1 + a 0 := conjecture_holds 4 le_rfl

-- An instance far out, and the value of that term computed by the floor and ceiling steps.
example : a 40 = 4 * a 39 - a 37 + a 36 := by
  simpa using conjecture_holds 40 (by decide)

example : a 40 = 3013788160843427209529109 := by decide +kernel

-- The recurrence rewrites a term in terms of four earlier ones.
example : a 10 = 3749901 := by
  rw [conjecture_holds 10 (by decide)]
  decide
