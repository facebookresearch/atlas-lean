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

-- At the first index step, the added term is the lower order's value at index one.
example (r : ℕ) :
    hyperLeonardo (r + 1) 1 = hyperLeonardo (r + 1) 0 + hyperLeonardo r 1 :=
  hyperLeonardo_succ_succ r 0

-- At order two and index two, the lower-order endpoint contributes five.
example : hyperLeonardo 2 2 = 8 := by
  calc
    hyperLeonardo 2 2 = hyperLeonardo 2 1 + hyperLeonardo 1 2 := hyperLeonardo_succ_succ 1 1
    _ = 8 := by simp [hyperLeonardo, Finset.sum_range_succ, genLeonardo]

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
