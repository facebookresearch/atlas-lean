/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.ReverseDivisor
import Mathlib.NumberTheory.Divisors
import MathlibExt.NumberTheory.Digits.ReverseDivisorHasPropertyPStarIffDvd

/-!
# Reverse divisors do not have property $P^*$

The classification of the positive integers with property $P^*$ gives a short proof:
every divisor of $99$ is a decimal palindrome, so its reversal cannot be a strictly
larger multiple of itself.

## References

* Mohamed Ayad and Rachid Bouchenna, *Which Integer Divides the Reverse of Any of Its
  Multiples?*, INTEGERS 25 (2025), Article A37, pp. 1–10, Proposition 4 and Theorem 3.
  The proof here uses Theorem 3 rather than the case analysis of Proposition 4.
* R. Webster and G. Williams, *On the trail of reverse divisors: 1089 and all that follow*,
  Mathematical Spectrum 45 (2012/2013), pp. 96–102. This is reference [2] in Ayad and
  Bouchenna, the source of the question answered by Theorem 3 and the reverse-divisor
  classification quoted in their Theorems 1 and 2.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

/-- **No reverse divisor has property $P^*$.** If $n$ is a reverse divisor, then $n$ does not have
the property $P^*$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Proposition 4. -/
theorem not_hasPropertyPStar_of_isReverseDivisor (n : ℕ)
    (h : IsReverseDivisor n) :
    ¬ HasPropertyPStar n := by
  intro hP
  obtain ⟨hn, k, hk, hrev⟩ := (isReverseDivisor_iff n).mp h
  have hdiv : n ∣ 99 := (hasPropertyPStar_iff_dvd n hn).mp hP
  -- The divisors of 99 are 1, 3, 9, 11, 33 and 99, all fixed by decimal reversal.
  have hfix : ∀ d ∈ Nat.divisors 99, Nat.reverseDigits 10 d = d := by decide
  rw [hfix n (Nat.mem_divisors.mpr ⟨hdiv, by decide⟩)] at hrev
  have hlt : 1 * n < k * n := Nat.mul_lt_mul_of_pos_right (by omega) hn
  exact (ne_of_lt (by simpa only [one_mul] using hlt)) hrev

end MathlibExt.NumberTheory.Digits.ReverseDivisorWanted
