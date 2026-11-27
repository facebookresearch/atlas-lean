/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeDvdPowAddOfDvdRadicalCoeffsGcd
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Tests for prime divisibility of the radical norm
-/

namespace MetaMathlibExt.PrimeDvdPowAddOfDvdRadicalCoeffsGcdTest

open Polynomial

-- In degree one with u = 2 and v = 4, the sole coefficient at n = 2 is 36.
example : (3 : ℤ) ∣ 6 := by
  have h := prime_dvd_pow_add_of_dvd_radical_coeffs_gcd (N := 1) (u := 2) (v := 4)
    (by simpa using irreducible_X_sub_C (4 : ℚ)) (fun m _ ↦ (6 : ℤ) ^ m)
    (by intro m _; norm_num [Fin.sum_univ_one]) 2 (by decide) 3 Nat.prime_three
    (by apply Finset.dvd_gcd; decide)
  convert h using 1
  norm_num

-- For a square root the signed norm specializes to u² - v.
example {u v p : ℕ} (hp : p.Prime) (hirr : Irreducible (X ^ 2 - C (v : ℚ)))
    (a : ℕ → Fin 2 → ℤ)
    (ha : ∀ m, 1 ≤ m → ((u : ℝ) + Real.sqrt v) ^ m = a m 0 + a m 1 * Real.sqrt v)
    (n : ℕ) (hn : 1 ≤ n) (hpd : (p : ℤ) ∣ Finset.univ.gcd (a n)) :
    (p : ℤ) ∣ (u : ℤ) ^ 2 - v := by
  have h := prime_dvd_pow_add_of_dvd_radical_coeffs_gcd (N := 2) (u := u) (v := v)
    hirr a (fun m hm ↦ by simpa [Fin.sum_univ_succ, Real.sqrt_eq_rpow] using ha m hm)
    n hn p hp hpd
  simpa [sub_eq_add_neg] using h

end MetaMathlibExt.PrimeDvdPowAddOfDvdRadicalCoeffsGcdTest
