/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PQRFibonacciPolynomial

/-! # Tests for the first (p,q)-r-Fibonacci recurrence -/

open MetaMathlibExt

-- At n = r the shifted polynomial has index zero.
example {R : Type*} [CommSemiring R] {r : ℕ} (hr : 1 ≤ r) (x y p q : R) (m : ℕ) :
    pqRFibonacci r x y p q m (r + 1) = p * x * pqRFibonacci r (p * x) (q * y) p q m r := by
  simpa only [Nat.sub_self, pqRFibonacci_zero, mul_zero, add_zero] using
    pqRFibonacci_succ_eq_left hr (Nat.le_refl r) x y p q m

-- Both recurrence terms contribute when p = 2 and q = 3.
example : pqRFibonacci 1 (1 : ℕ) 1 2 3 0 4 = 94 := by
  rw [pqRFibonacci_succ_eq_left (r := 1) (n := 3) (by decide) (by decide)]
  decide

-- At p = 0 only the top y-degree survives, and its exponent depends on m.
example : pqRFibonacci 1 (1 : ℕ) 1 0 2 2 5 = 32 := by
  rw [pqRFibonacci_succ_eq_left (r := 1) (n := 4) (by decide) (by decide)]
  decide
