/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.SZumkellerTwoDivMinFacSqAddOneLtProd

/-! # Tests for the prime-factor product bound for s-Zumkeller numbers -/

namespace MathlibExtTest.NumberTheory.SZumkellerTwoDivMinFacSqAddOneLtProd

open MetaMathlibExt

-- At sixty the bound applies with least prime factor two.
example : 2 / ((60 : ℕ).minFac : ℚ) ^ 2 + 1 <
    ∏ p ∈ (60 : ℕ).primeFactors, (p : ℚ) ^ 2 / (p ^ 2 - 1) :=
  two_div_minFac_sq_add_one_lt_prod 60 isSZumkeller_sixty

-- The prime-factor product of any s-Zumkeller number exceeds one.
example (n : ℕ) (h : IsSZumkeller n) :
    (1 : ℚ) < ∏ p ∈ n.primeFactors, (p : ℚ) ^ 2 / (p ^ 2 - 1) := by
  have hlt := two_div_minFac_sq_add_one_lt_prod n h
  obtain ⟨_, hA, hneA, _, _⟩ := h
  have hn1 : 1 < n := Nat.nonempty_properDivisors.mp (hneA.mono hA)
  have hprime : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hpos : (0 : ℚ) < 2 / (n.minFac : ℚ) ^ 2 :=
    div_pos (by norm_num) (pow_pos (by exact_mod_cast hprime.pos) 2)
  linarith

end MathlibExtTest.NumberTheory.SZumkellerTwoDivMinFacSqAddOneLtProd
