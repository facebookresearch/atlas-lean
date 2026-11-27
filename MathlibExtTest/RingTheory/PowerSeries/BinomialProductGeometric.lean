/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.PowerSeries.BinomialProductGeometric

namespace MetaMathlibExt

open PowerSeries

/-- With both shifts zero, the product adds the two geometric parameters. -/
example (α β : ℚ) :
    binomialProduct (1 - C α * X)⁻¹ (1 - C β * X)⁻¹ = (1 - C (α + β) * X)⁻¹ := by
  simpa using binomialProduct_X_pow_mul_inv_pow 0 0 α β

/-- Opposite parameters cancel the denominator, leaving a monomial with coefficient three. -/
example (α : ℚ) :
    binomialProduct (X * ((1 - C α * X)⁻¹) ^ 2) (X ^ 2 * ((1 - C (-α) * X)⁻¹) ^ 3) =
      3 * X ^ 3 := by
  simpa [Nat.choose] using binomialProduct_X_pow_mul_inv_pow 1 2 α (-α)

/-- The zero geometric parameter makes the right input the binomial product identity. -/
example (A : PowerSeries ℚ) : binomialProduct A 1 = A := by
  simpa using binomialProduct_inv_one_sub A (0 : ℚ)

/-- A nonzero geometric parameter acts by substitution on both terms of a polynomial. -/
example :
    let G : PowerSeries ℚ := (1 - C 2 * X)⁻¹
    binomialProduct (C 3 + X ^ 2) G = G * (C 3 + (X * G) ^ 2) := by
  intro G
  have h : HasSubst (X * G) := .of_constantCoeff_zero' (by simp)
  change binomialProduct (C 3 + X ^ 2) G = G * (C 3 + (X * G) ^ 2)
  rw [binomialProduct_inv_one_sub (C 3 + X ^ 2) (2 : ℚ)]
  change G * subst (X * G) (C 3 + X ^ 2) = G * (C 3 + (X * G) ^ 2)
  rw [subst_add h, subst_C, subst_pow h, subst_X h]
  rfl

end MetaMathlibExt
