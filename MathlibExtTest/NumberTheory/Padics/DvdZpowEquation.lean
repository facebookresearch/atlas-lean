/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.DvdZpowEquation

@[expose] public section

-- Consumer with the original binders.
example {p : ℕ} [Fact p.Prime] {i j : ℤ} {y : ℚ_[p]}
    (h : (p : ℚ_[p]) ^ i * (1 + p : ℚ_[p]) ^ j = y ^ p) :
    (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j :=
  Padic.dvd_of_prime_zpow_mul_one_add_prime_zpow_eq_pow h

-- The conclusion is not vacuous: `1 * 1 = 1 ^ p` gives divisibility of `0`.
example {p : ℕ} [Fact p.Prime] : (p : ℤ) ∣ (0 : ℤ) ∧ (p : ℤ) ∣ (0 : ℤ) :=
  Padic.dvd_of_prime_zpow_mul_one_add_prime_zpow_eq_pow
    (p := p) (i := 0) (j := 0) (y := 1) (by simp)
