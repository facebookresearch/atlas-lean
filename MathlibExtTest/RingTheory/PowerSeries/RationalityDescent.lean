/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.PowerSeries.RationalityDescent
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # Tests for descent of rational power series -/

/-- A denominator with zero constant term and a transcendental leading coefficient. -/
example :
    ∃ P Q : Polynomial ℚ, Q ≠ 0 ∧ (PowerSeries.X : PowerSeries ℚ) * (Q : PowerSeries ℚ) = P := by
  let t : RatFunc ℚ := RatFunc.X
  let p := Polynomial.monomial 2 t
  let q := Polynomial.monomial 1 t
  have hq : q ≠ 0 := by
    simpa [q, t] using (RatFunc.X_ne_zero (K := ℚ))
  refine MetaMathlibExt.exists_polynomial_quotient_of_extension PowerSeries.X p q hq ?_
  rw [PowerSeries.map_X, ← Polynomial.coe_X, ← Polynomial.coe_mul]
  simp [p, q]
