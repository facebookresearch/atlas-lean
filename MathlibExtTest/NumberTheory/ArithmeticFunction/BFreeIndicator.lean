/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.BFreeIndicator

open ArithmeticFunction MetaMathlibExt
open scoped ArithmeticFunction.Moebius

namespace MetaMathlibExt.BFreeIndicatorTest

-- The empty prime factorization contributes the unit for every admissible κ.
example {κ : ℕ → ℕ} (hκ : ∀ p : ℕ, p.Prime → 1 ≤ κ p) : (bFreeIndicator κ * μ) 1 = 1 := by
  simp [bFreeIndicator_mul_moebius_apply hκ (n := 1)]

private def κ (p : ℕ) : ℕ := if p = 2 then 2 else 1

private theorem κ_pos (p : ℕ) (_ : p.Prime) : 1 ≤ κ p := by
  unfold κ
  split <;> decide

private theorem exponents_dvd {n : ℕ} (h : 2 ∣ n.factorization 2) :
    ∀ p, κ p ∣ n.factorization p := by
  intro p
  by_cases hp : p = 2
  · subst p
    simpa [κ] using h
  · simp [κ, hp]

-- At the forbidden power of 2 the reduced root is the prime 2.
example : (bFreeIndicator κ * μ) 4 = -1 := by
  rw [bFreeIndicator_mul_moebius_apply κ_pos (by decide : 1 ≤ 4),
    ite_eq_left (exponents_dvd (by decide +kernel))]
  decide +kernel

-- The exponents 2 and 1 in 12 reduce to the squarefree root 6.
example : (bFreeIndicator κ * μ) 12 = 1 := by
  rw [bFreeIndicator_mul_moebius_apply κ_pos (by decide : 1 ≤ 12),
    ite_eq_left (exponents_dvd (by decide +kernel))]
  decide +kernel

-- The exponent of 2 in 6 fails divisibility.
example : (bFreeIndicator κ * μ) 6 = 0 := by
  rw [bFreeIndicator_mul_moebius_apply κ_pos (by decide : 1 ≤ 6)]
  apply ite_eq_right
  intro h
  have hbad : ¬κ 2 ∣ (6 : ℕ).factorization 2 := by
    decide +kernel
  exact hbad (h 2)

-- Divisibility holds for 16, but its root 4 has a repeated prime factor.
example : (bFreeIndicator κ * μ) 16 = 0 := by
  rw [bFreeIndicator_mul_moebius_apply κ_pos (by decide : 1 ≤ 16),
    ite_eq_left (exponents_dvd (by decide +kernel))]
  decide +kernel

end MetaMathlibExt.BFreeIndicatorTest
