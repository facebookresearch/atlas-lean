/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Diophantine.NegativePellGcd

/-! # Tests for `MathlibExt.NumberTheory.Diophantine.NegativePellGcd` -/

namespace MathlibExtTest.NegativePellGcd

open MetaMathlibExt

-- `d = 2`, with the solution `1² - 2 · 1² = -1`: every `f_n` is odd and coprime to `g_n`.
example (n : ℕ) (hn : 0 < n) :
    Int.gcd 2 (negPellF 2 n) = 1 ∧ Int.gcd (negPellF 2 n) (negPellG 2 n) = 1 :=
  negPell_gcd_eq_one 2 (by norm_num) ⟨1, 1, by norm_num⟩ n hn

-- `d = 5`, with the solution `2² - 5 · 1² = -1`: no `f_n` is divisible by `5`.
example (n : ℕ) (hn : 0 < n) : ¬(5 : ℤ) ∣ negPellF 5 n := by
  intro h
  have h1 := (negPell_gcd_eq_one 5 (by norm_num) ⟨2, 1, by norm_num⟩ n hn).1
  have h5 : ((5 : ℕ) : ℤ) ∣ ((Int.gcd ((5 : ℕ) : ℤ) (negPellF 5 n) : ℕ) : ℤ) :=
    Int.dvd_coe_gcd (by exact_mod_cast dvd_rfl) (by exact_mod_cast h)
  rw [h1] at h5
  norm_num at h5

-- `d = 10`, with the solution `3² - 10 · 1² = -1`, read off from an arbitrary integral solution.
example : Int.gcd (negPellF 10 3) (negPellG 10 3) = 1 :=
  (negPell_gcd_eq_one 10 (by norm_num) ⟨-3, -1, by norm_num⟩ 3 (by norm_num)).2

#print axioms negPell_gcd_eq_one

end MathlibExtTest.NegativePellGcd
