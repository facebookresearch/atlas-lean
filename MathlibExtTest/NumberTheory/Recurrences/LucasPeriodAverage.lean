/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasPeriodAverage

/-! # Tests for periods and sums of second-order recurrences -/

namespace MetaMathlibExt.secondOrder_sum_dvd_of_period_dvd

-- The Fibonacci pair returns modulo 4 after six steps. The initial values of w are arbitrary.
example (w : ℕ → ℤ) (hw : ∀ k, w (k + 2) = w (k + 1) + w k) (m : ℕ) :
    (4 : ℤ) ∣ ∑ i ∈ Finset.Icc 1 (6 * m), w i := by
  have h₆ : lucasUPeriod fibonacciLucasParams 4 ∣ 6 :=
    Function.isPeriodicPt_iff_minimalPeriod_dvd.mp (by decide)
  have hcop : IsCoprime (4 : ℤ) (-1) := ⟨0, -1, by decide⟩
  apply (secondOrder_sum_dvd_of_period_dvd fibonacciLucasParams (by decide) 4 (by decide)
    (by simpa [fibonacciLucasParams] using hcop)).2 _ (dvd_mul_of_dvd_left h₆ m)
  simpa [fibonacciLucasParams] using hw

-- Modulo 2 the pair for (P, Q) = (0, 1) returns after two steps and the sum is odd.
-- Here the modulus shares a factor with P - Q - 1.
example : lucasUPeriod ⟨0, 1, by decide⟩ 2 ∣ 2 ∧
    ¬ (2 : ℤ) ∣ ∑ i ∈ Finset.Icc 1 2, lucasU ⟨0, 1, by decide⟩ i :=
  ⟨Function.isPeriodicPt_iff_minimalPeriod_dvd.mp (by decide), by decide⟩

end MetaMathlibExt.secondOrder_sum_dvd_of_period_dvd

namespace MetaMathlibExt.lucasUPeriod_isPeriod_of_secondOrder

-- Modulo 3 the first positive Fibonacci zero is at 4 and the next residue is 2.
-- The restricted shift therefore scales every solution of the Fibonacci recurrence by 2.
example (w : ℕ → ℤ) (hw : ∀ k, w (k + 2) = w (k + 1) + w k) (n : ℕ) :
    w (n + 4) ≡ 2 * w n [ZMOD 3] := by
  have hρ : lucasURestrictedPeriod fibonacciLucasParams 3 = 4 := by
    apply IsLeast.csInf_eq
    constructor
    · exact ⟨by decide, by decide, 2, -3, by decide⟩
    · rintro k ⟨hk, hdvd, -⟩
      by_contra! h
      have : k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases this with rfl | rfl | rfl <;> revert hdvd <;> decide
  have hcop : IsCoprime (3 : ℤ) (-1) := ⟨0, -1, by decide⟩
  have h := (lucasUPeriod_isPeriod_of_secondOrder fibonacciLucasParams 3 (by decide) hcop w
    (by simpa [fibonacciLucasParams] using hw)).2.2.2 n
  rw [hρ] at h
  exact h.trans ((by decide : lucasU fibonacciLucasParams (4 + 1) ≡ 2 [ZMOD 3]).mul_right _)

end MetaMathlibExt.lucasUPeriod_isPeriod_of_secondOrder
