/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.CalzadoTotientsNearSqrt

/-!
# Tests for reciprocal totients of primes near the square root
-/

open Filter

/-- At exponent one the lower endpoint is the square root divided by the logarithm. -/
example : ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
    ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ ↦
        p.Prime ∧ Real.sqrt x / Real.log x < (p : ℝ) ∧ (p : ℝ) ≤ Real.sqrt x),
      1 / (Nat.totient p : ℝ) ≤ C * Real.log (Real.log x) / Real.log x := by
  simpa only [Real.sqrt_eq_rpow, Real.rpow_neg_one, div_eq_mul_inv] using
    MetaMathlibExt.calzado_sum_inv_totient_near_sqrt_isBigO (B := 1) (hB := zero_lt_one)
