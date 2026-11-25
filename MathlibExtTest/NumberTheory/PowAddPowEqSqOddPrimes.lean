/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PowAddPowEqSqOddPrimes
import MathlibExt.NumberTheory.PrimePowAddOneEqSq

namespace MathlibExtTest.NumberTheory.PowAddPowEqSqOddPrimes

open MathlibExt.NumberTheory.ExponentialDiophantineWanted

/-- `p = 5` and `a = 24`, so `p + a = 29`: `5 ^ x + 29 ^ y` is never a square, because the
theorem leaves only `z ^ 2 = 30`. -/
example (x y z : ℕ) : 5 ^ x + 29 ^ y ≠ z ^ 2 := by
  intro h
  obtain ⟨-, -, hz⟩ := pow_add_pow_eq_sq 5 24 x y z (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) h
  have h5 : 5 < z := (Nat.pow_lt_pow_iff_left two_ne_zero).1 (by omega)
  have h6 : z < 6 := (Nat.pow_lt_pow_iff_left two_ne_zero).1 (by omega)
  omega

/-- `p = 7` and `a = 76`, so `p + a = 83`: no solution has a positive power of `7`. -/
example (x y z : ℕ) (hx : 0 < x) : 7 ^ x + 83 ^ y ≠ z ^ 2 := fun h =>
  hx.ne' (pow_add_pow_eq_sq 7 76 x y z (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) h).1

/-- Under the hypotheses the equation has no solution at all: the theorem leaves only
`(p + a) ^ 1 + 1 = z ^ 2`, which forces `p + a = 3`, whereas `a ≥ 4` because `a ≡ 0 (mod 4)` and
`p ∣ a + 1`. The theorem is called with named arguments. -/
example (p a x y z : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpa : (p + a).Prime)
    (ha4 : a % 4 = 0) (hap : p ∣ a + 1) : p ^ x + (p + a) ^ y ≠ z ^ 2 := by
  intro h
  obtain ⟨rfl, rfl, hz⟩ := pow_add_pow_eq_sq (hp := hp) (hp2 := hp2) (hp3 := hp3) (hpa := hpa)
    (ha4 := ha4) (hap := hap) (h := h)
  have ha : a ≠ 0 := by
    rintro rfl
    exact hp.one_lt.ne' (Nat.dvd_one.mp hap)
  have := hp.two_le
  rcases (MetaMathlibExt.prime_pow_add_one_eq_sq_iff hpa 1 z).1 (by rw [pow_one]; omega) with
    h' | h' <;> simp only [Prod.mk.injEq] at h' <;> omega

/-- The hypothesis `p ≠ 3` cannot be dropped: `p = 3` and `a = 8` satisfy all the other
hypotheses, and `3 ^ 1 + 11 ^ 0 = 2 ^ 2` is a solution with `x = 1`. -/
example : (3 + 8).Prime ∧ 8 % 4 = 0 ∧ 3 ∣ 8 + 1 ∧ 3 ^ 1 + (3 + 8) ^ 0 = 2 ^ 2 := by decide

end MathlibExtTest.NumberTheory.PowAddPowEqSqOddPrimes
