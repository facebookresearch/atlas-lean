/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HyperLeonardo

namespace MetaMathlibExt

open PowerSeries

-- The initial coefficient survives every partial sum.
example (r : ℕ) : hyperLeonardo r 0 = 1 := by
  induction r with
  | zero => rfl
  | succ r ih => simpa [hyperLeonardo_succ] using ih

-- The first recurrence step gives the index-two values from the six initial values.
example : hyperLeonardo 0 2 = 3 ∧ hyperLeonardo 1 2 = 5 ∧ hyperLeonardo 2 2 = 8 := by
  obtain ⟨rec₀, h₀₀, h₀₁, rec₁, h₁₀, h₁₁, rec₂, h₂₀, h₂₁⟩ :=
    hyperLeonardo_recurrence_small_order
  rw [rec₀ 0, rec₁ 0, rec₂ 0, h₀₀, h₀₁, h₁₀, h₁₁, h₂₀, h₂₁]
  decide

-- At degree three the first two iterated sums already have distinct coefficients.
example : coeff 3 (PowerSeries.mk (hyperLeonardo 1)) = 10 ∧
    coeff 3 (PowerSeries.mk (hyperLeonardo 2)) = 18 := by
  simp [hyperLeonardo, coeff_mk, Finset.sum_range_succ, genLeonardo]

example : hyperFibonacci 2 3 = 7 := by
  simp [hyperFibonacci, Finset.sum_range_succ, Nat.fib_add_two]

-- In the factored form of the order-zero identity, the linear coefficient is negative.
example : coeff 1 (PowerSeries.mk (genLeonardo 1) * ((1 - X - X ^ 2) * (1 - X))) = -1 := by
  rw [leonardo_generatingFunction.2]
  simp [two_mul, coeff_X]

-- The numerator of the cleared order-two series has no term of degree three.
example : coeff 3 (PowerSeries.mk (hyperLeonardo 2) *
    ((1 - 2 * X + X ^ 3) * (1 - X) ^ 2)) = 0 := by
  rw [hyperLeonardo_one_two_generatingFunction.2]
  simp [coeff_X]

-- Clearing the denominator kills every coefficient above degree two at every order.
example (r n : ℕ) : coeff (n + 3) (PowerSeries.mk (hyperLeonardo r) *
    ((1 - 2 * X + X ^ 3) * (1 - X) ^ r)) = 0 := by
  rw [hyperLeonardo_generatingFunction]
  simp [coeff_X]

end MetaMathlibExt
