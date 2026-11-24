/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.ShorGoodUnits

import Mathlib.Tactic.NormNum

/-!
# Tests for the Shor good-unit bound

The examples cover two distinct primes, three distinct primes with a repeated factor,
and the degenerate modulus `1`.
-/

/-- Boundary check: the counting bound instantiates for
`N = 3 * 5 = 15`. -/
example : (2 : ℝ) * ((Finset.univ.filter (fun a : (ZMod (3 * 5))ˣ =>
      Even (orderOf a) ∧ a ^ (orderOf a / 2) ≠ -1)).card : ℝ) ≥
    ((Finset.univ : Finset (ZMod (3 * 5))ˣ).card : ℝ) := by
  have : NeZero (3 * 5) := ⟨by norm_num⟩
  exact shor_good_units (p := 3) (q := 5) (by decide) (by decide)
    (by norm_num) (by norm_num) (by norm_num)

open Cslib.Shor

/-- For `315 = 3 ^ 2 * 5 * 7`, at least three quarters of the units are good. -/
example : (3 / 4 : ℝ) * Fintype.card (ZMod 315)ˣ ≤
    ((Finset.univ.filter fun x : (ZMod 315)ˣ =>
      Even (orderOf x) ∧ x ^ (orderOf x / 2) ≠ -1).card : ℝ) := by
  have hcard : (315 : ℕ).primeFactors.card = 3 := by
    change ((3 ^ 2 * 5 * 7 : ℕ)).primeFactors.card = 3
    rw [(show Nat.Coprime (3 ^ 2 * 5) 7 by decide).primeFactors_mul,
      (show Nat.Coprime (3 ^ 2) 5 by decide).primeFactors_mul,
      Nat.primeFactors_prime_pow (by decide) (show Nat.Prime 3 by decide),
      (show Nat.Prime 5 by decide).primeFactors, (show Nat.Prime 7 by decide).primeFactors]
    decide
  have hcoef : (1 - 1 / (2 : ℝ) ^ ((315 : ℕ).primeFactors.card - 1)) = 3 / 4 := by
    rw [hcard]
    norm_num
  simpa only [hcoef] using card_units_good_for_factoring_ge (n := 315) (by decide)

/-- Modulo `1`, natural subtraction gives a zero lower bound. -/
example : (0 : ℝ) ≤
    ((Finset.univ.filter fun x : (ZMod 1)ˣ =>
      Even (orderOf x) ∧ x ^ (orderOf x / 2) ≠ -1).card : ℝ) := by
  simpa only [Nat.primeFactors_one, Finset.card_empty, Nat.zero_sub, pow_zero, div_one,
    sub_self, zero_mul] using card_units_good_for_factoring_ge (n := 1) (by decide)
