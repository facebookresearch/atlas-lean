/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.WolstenholmePairedBinomialCongruence
import Mathlib.Tactic.NormNum.Prime

/-! # Tests for the paired binomial congruences modulo `p^7` -/

open MetaMathlibExt

private def pairedRemainder : ℚ :=
  let a : ℚ := ((-2 : ℤ) : ℚ) * (11 : ℕ)
  ((Ring.choose (-23 : ℤ) 10 : ℤ) : ℚ) * ((Ring.choose (-12 : ℤ) 10 : ℤ) : ℚ) -
    (1 - a ^ 2 * higherHarmonic 10 2 +
      a ^ 4 / 2 * (higherHarmonic 10 2 ^ 2 - higherHarmonic 10 4))

private def inverseRemainder : ℚ :=
  (Nat.choose 21 10 : ℚ)⁻¹ - (1 + (11 : ℚ) ^ 2 * higherHarmonic 10 2 +
    (11 : ℚ) ^ 4 / 2 * (higherHarmonic 10 2 ^ 2 + higherHarmonic 10 4))

private lemma pairedRemainder_value :
    pairedRemainder = (11 : ℚ) ^ 7 * 1668407306518229 / 1428840000 := by
  unfold pairedRemainder
  rw [Ring.choose_neg, Ring.choose_neg]
  change ((Int.negOnePow 10 • Ring.choose ((32 : ℕ) : ℤ) 10 : ℤ) : ℚ) *
    ((Int.negOnePow 10 • Ring.choose ((21 : ℕ) : ℤ) 10 : ℤ) : ℚ) - _ = _
  simp only [Ring.choose_natCast, Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel
private lemma inverseRemainder_value :
    inverseRemainder = -(11 : ℚ) ^ 7 * 223251197407969 / 169335509091840000 := by
  unfold inverseRemainder
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel
-- At the least admissible prime, both errors are nonzero for α = -2.
example : 7 ≤ padicValRat 11 pairedRemainder ∧ 7 ≤ padicValRat 11 inverseRemainder := by
  have h := ringChoose_mul_prime_sub_one_mul_congr 11 (-2) (by norm_num) (by decide)
  change (pairedRemainder = 0 ∨ 7 ≤ padicValRat 11 pairedRemainder) ∧
    (inverseRemainder = 0 ∨ 7 ≤ padicValRat 11 inverseRemainder) at h
  exact ⟨h.1.resolve_left (by rw [pairedRemainder_value]; norm_num),
    h.2.resolve_left (by rw [inverseRemainder_value]; norm_num)⟩
