/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Padics.FactorialQuotient

open Nat MetaMathlibExt

-- An empty product has valuation zero, including when the starting point is arbitrary.
example (m p : ℕ) (hp : p.Prime) : padicValNat p (m ! / m !) = 0 := by
  have h := padicValNat_factorial_div_factorial_le m 0 p hp
  simpa [padicValNat_def] using h

-- The bound is sharp for 8 · 9 · 10: the maximal valuation is 3 and the factorial contributes 1.
example : padicValNat 2 (8 * 9 * 10) = 4 := by
  apply le_antisymm
  · convert padicValNat_factorial_div_factorial_le 7 3 2 prime_two using 1 <;> decide +kernel
  · decide +kernel
