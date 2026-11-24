/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Quantum.Shor.OrderToFactorProbability
import Mathlib.Tactic.NormNum

/-!
# Tests for the Shor good-unit bound

The bound applies to an odd modulus with three prime factors including a repeated factor,
and to the degenerate modulus `1`.
-/

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
