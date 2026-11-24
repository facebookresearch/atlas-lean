/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimitivePrimeDivisorPowSubOne

open IntegerSequence MetaMathlibExt

example : 3 % 2 = 1 := by
  apply primitivePrimeDivisor_pow_sub_one_mod_eq_one (a := 2) (n := 2) (p := 3)
    (ha := by decide) (hn := by decide)
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro s hs hlt
  have h : s = 1 := by omega
  subst s
  decide

example : 5 % 4 = 1 := by
  apply primitivePrimeDivisor_pow_sub_one_mod_eq_one (a := 2) (n := 4) (p := 5)
    (ha := by decide) (hn := by decide)
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro s hs hlt
  have h : s = 1 ∨ s = 2 ∨ s = 3 := by omega
  rcases h with rfl | rfl | rfl <;> decide

-- Divisibility at index four alone is not enough: the prime already occurs at index two.
example : ¬ IsPrimitivePrimeDivisor (fun m => (2 : ℤ) ^ m - 1) 4 3 := by
  intro h
  exact h.not_dvd_of_lt (s := 2) (by decide) (by decide) (by decide)
