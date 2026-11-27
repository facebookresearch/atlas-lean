/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedFermatGCD

/-! # Tests for greatest common divisors of generalized Fermat numbers -/

open MetaMathlibExt

-- At the smallest allowed bases, the initial Fermat number is coprime to every later one.
example {m : ℕ} (hm : 0 < m) : Nat.gcd (2 ^ 2 ^ m + 1) 3 = 1 :=
  (gcd_pow_pow_add_one (a := 2) (b := 2) (by decide) (by decide)).1 hm even_two even_two

-- With odd base 3, the initial term is 4 and the common factor is exactly 2.
example {m : ℕ} (hm : 0 < m) : Nat.gcd (3 ^ 2 ^ m + 1) 4 = 2 :=
  (gcd_pow_pow_add_one (a := 3) (b := 2) (by decide) (by decide)).2.1 hm (by decide) even_two

-- For odd b the earlier term divides the later one, even across a gap of two indices.
example (n : ℕ) : 2 ^ 3 ^ n + 1 ∣ 2 ^ 3 ^ (n + 2) + 1 :=
  Nat.gcd_eq_right_iff_dvd.mp
    ((gcd_pow_pow_add_one (a := 2) (b := 3) (by decide) (by decide)).2.2 (by omega) (by decide))

-- The odd-b clause also includes equal indices.
example (n : ℕ) : Nat.gcd (2 ^ 3 ^ n + 1) (2 ^ 3 ^ n + 1) = 2 ^ 3 ^ n + 1 :=
  (gcd_pow_pow_add_one (a := 2) (b := 3) (by decide) (by decide)).2.2 le_rfl (by decide)
