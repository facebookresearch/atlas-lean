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

end MetaMathlibExt
