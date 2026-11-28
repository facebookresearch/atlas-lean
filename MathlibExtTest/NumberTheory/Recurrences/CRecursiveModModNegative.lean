/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.CRecursiveModModNegative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.NormNum

/-!
# Tests for double remainders with a negative free term
-/

open MetaMathlibExt Polynomial

-- Apply the public theorem to `2 ^ n`, whose generating function is `1 / (1 - 2X)`.
example (c : ℕ)
    (hrep : ∀ n : ℕ, 1 ≤ n → (2 : ℤ) ^ n =
      ⌊((c : ℚ) ^ (n ^ 2) * (c : ℚ) ^ n) / (((c : ℤ) ^ n - 2 : ℤ) : ℚ)⌋ % (c : ℤ) ^ n) :
    ∃ r : ℕ, ∀ n : ℕ, 1 ≤ n →
      2 * (2 : ℤ) ^ n = ((r : ℤ) ^ (n ^ 2) * (r : ℤ) ^ n) % ((r : ℤ) ^ n - 2) % (r : ℤ) ^ n := by
  let B : Polynomial ℤ := 1 - C 2 * X
  have hd : B.natDegree = 1 := by
    rw [show B = 1 - C 2 * X from rfl, natDegree_sub_eq_right_of_natDegree_lt]
    · simp
    · simp
  have hr : B.reverse = X - C 2 := by
    rw [reverse, hd]
    rw [show B = 1 - C 2 * X from rfl, reflect_sub, reflect_one, reflect_C_mul,
      reflect_one_X, pow_one, mul_one]
  have h1 : (1 : Polynomial ℤ).reverse = 1 := by simp [reverse]
  have hgf : PowerSeries.mk (fun n : ℕ => ((2 ^ n : ℕ) : ℤ)) * (B : PowerSeries ℤ) =
      ((1 : Polynomial ℤ) : PowerSeries ℤ) := by
    have h := congrArg (PowerSeries.rescale (2 : ℤ)) (PowerSeries.mk_one_mul_one_sub_eq_one ℤ)
    simpa only [B, map_mul, map_sub, map_one, PowerSeries.rescale_mk, Pi.one_apply, mul_one,
      PowerSeries.rescale_X, Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_one,
      Polynomial.coe_C, Polynomial.coe_X, Nat.cast_pow, Nat.cast_ofNat] using h
  have hα : B.reverse.coeff 0 < 0 := by norm_num [hr]
  simpa [hd, hr, h1] using
    (exists_mod_mod_representation_of_neg_free_term (fun n => 2 ^ n) 1 B c
      (by simp [B]) (by simp [hd]) one_ne_zero hgf (by simpa [hd, hr, h1] using hrep) hα)

-- At base eight, the two remainders give `2 * t n`, with no additive offset.
example : ((8 : ℤ) ^ (1 ^ 2) * 8 ^ 1) % ((8 : ℤ) ^ 1 - 2) % 8 ^ 1 = 2 * (2 : ℤ) ^ 1 :=
  by decide

example : ((8 : ℤ) ^ (2 ^ 2) * 8 ^ 2) % ((8 : ℤ) ^ 2 - 2) % 8 ^ 2 = 2 * (2 : ℤ) ^ 2 :=
  by decide
