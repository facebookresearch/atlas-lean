/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.HilbertSymbol.KoenigsmannOneModEight
public import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the Hilbert symbols of Koenigsmann's case $p \equiv 1 \pmod 8$
-/

set_option autoImplicit false

@[expose] public section

namespace KoenigsmannOneModEightTest

local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- $(34, 3)_2 = -1$ and $(-34, 3)_2 = 1$, with $p = 17 = 1 + 8 \cdot 2$ and $q = 3$. -/
example (a a' b : ℚ_[2]ˣ) (ha : (a : ℚ_[2]) = 34) (ha' : (a' : ℚ_[2]) = -34)
    (hb : (b : ℚ_[2]) = 3) :
    padicHilbertSymbol 2 a b = -1 ∧ padicHilbertSymbol 2 a' b = 1 :=
  padicHilbertSymbol.two_mul_left_of_rat_one_three 17 3 ⟨2, by decide, by norm_num⟩
    ⟨0, by decide, by norm_num⟩ a a' b (by rw [ha]; norm_num) (by rw [ha']; norm_num)
    (by rw [hb]; norm_num)

/-- With rationals of odd denominator: $p = 1 + 8/3 = 11/3$ and $q = 3 - 8/5 = 7/5$. -/
example (a a' b : ℚ_[2]ˣ) (ha : (a : ℚ_[2]) = 2 * ((11 / 3 : ℚ) : ℚ_[2]))
    (ha' : (a' : ℚ_[2]) = -2 * ((11 / 3 : ℚ) : ℚ_[2])) (hb : (b : ℚ_[2]) = ((7 / 5 : ℚ) : ℚ_[2])) :
    padicHilbertSymbol 2 a b = -1 ∧ padicHilbertSymbol 2 a' b = 1 :=
  padicHilbertSymbol.two_mul_left_of_rat_one_three _ _
    ⟨3⁻¹, by rw [Rat.inv_ofNat_den]; decide, by norm_num⟩
    ⟨-5⁻¹, by rw [Rat.neg_den, Rat.inv_ofNat_den]; decide, by norm_num⟩ a a' b ha ha' hb

/-- $(-1, 17)_{17} = 1$, as $17 \equiv 1 \pmod 8$. -/
example (b : ℚ_[17]ˣ) (hb : (b : ℚ_[17]) = ((17 : ℚ) : ℚ_[17])) :
    padicHilbertSymbol 17 (-1) b = 1 :=
  padicHilbertSymbol.neg_one_left_eq_one_of_rat (by norm_num) 17 b hb (Or.inl (by norm_num))

/-- $(-1, 9)_3 = 1$, as $v_3(9) = 2$ is even. -/
example (b : ℚ_[3]ˣ) (hb : (b : ℚ_[3]) = ((9 : ℚ) : ℚ_[3])) :
    padicHilbertSymbol 3 (-1) b = 1 := by
  refine padicHilbertSymbol.neg_one_left_eq_one_of_rat (by norm_num) 9 b hb (Or.inr ?_)
  rw [show (9 : ℚ) = ((3 : ℕ) : ℚ) ^ 2 by norm_num, padicValRat.pow,
    padicValRat.self (by norm_num)]
  decide

/-- $(-1, 3)_3 = -1$: here $3 \equiv 3 \pmod 4$ and $v_3(3) = 1$ is odd. -/
example (b : ℚ_[3]ˣ) (hb : (b : ℚ_[3]) = 3) : padicHilbertSymbol 3 (-1) b = -1 := by
  rcases padicHilbertSymbol.eq_one_or_neg_one (-1) b with h | h
  · rw [padicHilbertSymbol.neg_one_left_eq_one_iff (by norm_num), hb] at h
    have hv : (3 : ℚ_[3]).valuation = 1 := by
      have := Padic.valuation_p (p := 3)
      exact_mod_cast this
    rw [hv] at h
    norm_num at h
  · exact h

end KoenigsmannOneModEightTest
