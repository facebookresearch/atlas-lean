/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.BinomialPowerRealizability

/-!
# Tests for binomial-power sequences

Value tests for `binomialPowerSeq` at Apéry (`r = s = 2`), central
Delannoy (`r = s = 1`), and Franel (`s = 0`) parameters, plus the
`n = 0` endpoint, `r`/`s` ordering, and zero exponents. We also test the
prime-power congruence for binomial coefficients in four cases.
-/

namespace MetaMathlibExt

-- Apéry numbers: `r = s = 2`.
example : binomialPowerSeq 2 2 0 = 1 := by rfl
example : binomialPowerSeq 2 2 1 = 5 := by rfl
example : binomialPowerSeq 2 2 2 = 73 := by rfl
example : binomialPowerSeq 2 2 3 = 1445 := by rfl

-- Central Delannoy numbers: `r = s = 1`.
example : binomialPowerSeq 1 1 0 = 1 := by rfl
example : binomialPowerSeq 1 1 1 = 3 := by rfl
example : binomialPowerSeq 1 1 2 = 13 := by rfl
example : binomialPowerSeq 1 1 3 = 63 := by rfl

-- Franel numbers of order 2: `r = 2`, `s = 0`.
example : binomialPowerSeq 2 0 0 = 1 := by rfl
example : binomialPowerSeq 2 0 1 = 2 := by rfl
example : binomialPowerSeq 2 0 2 = 6 := by rfl
example : binomialPowerSeq 2 0 3 = 20 := by rfl

-- Franel numbers of order 3: `r = 3`, `s = 0`.
example : binomialPowerSeq 3 0 0 = 1 := by rfl
example : binomialPowerSeq 3 0 1 = 2 := by rfl
example : binomialPowerSeq 3 0 2 = 10 := by rfl
example : binomialPowerSeq 3 0 3 = 56 := by rfl

-- Powers of two: `r = 1`, `s = 0`.
example : binomialPowerSeq 1 0 0 = 1 := by rfl
example : binomialPowerSeq 1 0 1 = 2 := by rfl
example : binomialPowerSeq 1 0 2 = 4 := by rfl
example : binomialPowerSeq 1 0 3 = 8 := by rfl

-- Range endpoint: `n = 0` gives `1` for any `r` and `s`.
example : binomialPowerSeq 0 0 0 = 1 := by rfl
example : binomialPowerSeq 3 7 0 = 1 := by rfl
example : binomialPowerSeq 0 3 0 = 1 := by rfl

-- `r`/`s` ordering matters: swapping gives different values.
example : binomialPowerSeq 1 2 1 = 5 := by rfl
example : binomialPowerSeq 2 1 1 = 3 := by rfl
example : binomialPowerSeq 1 2 2 = 55 := by rfl
example : binomialPowerSeq 2 1 2 = 19 := by rfl

-- Zero exponents.
example : binomialPowerSeq 0 0 2 = 3 := by rfl
example : binomialPowerSeq 0 0 3 = 4 := by rfl
example : binomialPowerSeq 0 1 1 = 3 := by rfl
example : binomialPowerSeq 0 1 2 = 10 := by rfl
example : binomialPowerSeq 0 2 1 = 5 := by rfl

-- The headline theorem applies at Apéry parameters.
example : doldRealizable (fun n => ((binomialPowerSeq 2 2 n : ℕ) : ℤ)) :=
  binomial_power_sequence_dold_realizable 2 2 (by decide)

#print axioms binomial_power_sequence_dold_realizable

private theorem padicValNat_eq_of_pow_dvd {p n e : ℕ} (he : p ^ e ∣ n)
    (hsucc : ¬ p ^ (e + 1) ∣ n) : padicValNat p n = e :=
  Nat.padicValNat_def.trans (multiplicity_eq_of_dvd_of_not_dvd he hsucc)

-- The larger valuation is that of n: the difference of the coefficients is 24.
example : (Nat.choose 8 2 : ℤ) ≡ (Nat.choose 4 1 : ℤ) [ZMOD 8] := by
  have h := choose_mul_prime_modEq_choose_div 8 2 1 (by decide) (by decide) (by decide) (by decide)
  rw [padicValInt, ← Nat.padicValNat_def] at h
  convert h using 1
  change (8 : ℤ) = 2 ^ max (padicValNat 2 8) (padicValNat 2 6)
  rw [show padicValNat 2 8 = 3 from padicValNat_eq_of_pow_dvd (by decide) (by decide),
    show padicValNat 2 6 = 1 from padicValNat_eq_of_pow_dvd (by decide) (by decide)]
  decide

-- The larger valuation is that of n - l * p: the difference of the coefficients is 40.
example : (Nat.choose 10 2 : ℤ) ≡ (Nat.choose 5 1 : ℤ) [ZMOD 8] := by
  have h := choose_mul_prime_modEq_choose_div 10 2 1 (by decide) (by decide) (by decide) (by decide)
  rw [padicValInt, ← Nat.padicValNat_def] at h
  convert h using 1
  change (8 : ℤ) = 2 ^ max (padicValNat 2 10) (padicValNat 2 8)
  rw [show padicValNat 2 10 = 1 from padicValNat_eq_of_pow_dvd (by decide) (by decide),
    show padicValNat 2 8 = 3 from padicValNat_eq_of_pow_dvd (by decide) (by decide)]
  decide

-- The gap is -9; both coefficients vanish because the lower indices exceed the upper indices.
example : (Nat.choose 6 15 : ℤ) ≡ (Nat.choose 2 5 : ℤ) [ZMOD 9] := by
  have h := choose_mul_prime_modEq_choose_div 6 3 5 (by decide) (by decide) (by decide) (by decide)
  rw [padicValInt, ← Nat.padicValNat_def] at h
  convert h using 1
  change (9 : ℤ) = 3 ^ max (padicValNat 3 6) (padicValNat 3 9)
  rw [show padicValNat 3 6 = 1 from padicValNat_eq_of_pow_dvd (by decide) (by decide),
    show padicValNat 3 9 = 2 from padicValNat_eq_of_pow_dvd (by decide) (by decide)]
  decide

-- At l = 0 the valuations are equal and both coefficients are one.
example : (Nat.choose 9 0 : ℤ) ≡ (Nat.choose 3 0 : ℤ) [ZMOD 9] := by
  have h := choose_mul_prime_modEq_choose_div 9 3 0 (by decide) (by decide) (by decide) (by decide)
  rw [padicValInt, ← Nat.padicValNat_def] at h
  convert h using 1
  change (9 : ℤ) = 3 ^ max (padicValNat 3 9) (padicValNat 3 9)
  rw [show padicValNat 3 9 = 2 from padicValNat_eq_of_pow_dvd (by decide) (by decide)]
  decide

#print axioms choose_mul_prime_modEq_choose_div

end MetaMathlibExt
