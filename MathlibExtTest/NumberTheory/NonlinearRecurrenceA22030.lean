/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NonlinearRecurrenceA22030

@[expose] public section

/-!
# Tests for `MathlibExt.NumberTheory.NonlinearRecurrenceA22030`

The term tests are the ones carried by `FormalConjectures/OEIS/22030.lean`.
-/

namespace MathlibExtTest.NumberTheory.NonlinearRecurrenceA22030

open OeisA22030

-- Source faithfulness: the Formal Conjectures statement `OeisA22030.conjecture`, verbatim.
example (n : ℕ) (hn : 4 ≤ n) : a n = 4 * a (n - 1) - a (n - 3) + a (n - 4) :=
  conjecture n hn

example : a 0 = 4 := by rfl
example : a 1 = 16 := by rfl
example : a 2 = 63 := by rfl
example : a 3 = 249 := by rfl
example : a 4 = 984 := by rfl
example : a 5 = 3889 := by rfl

-- The linear recurrence, checked numerically at `n = 5`.
example : a 5 = 4 * a 4 - a 2 + a 1 := conjecture 5 (by norm_num)

end MathlibExtTest.NumberTheory.NonlinearRecurrenceA22030
