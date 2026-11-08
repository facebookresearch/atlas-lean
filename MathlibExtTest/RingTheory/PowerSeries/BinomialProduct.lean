/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.PowerSeries.BinomialProduct

namespace MetaMathlibExt

/-- Coefficient API: the `n`-th coefficient is the binomial convolution. -/
example (A B : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (binomialProduct A B) = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℚ) * PowerSeries.coeff k A * PowerSeries.coeff (n - k) B :=
  coeff_binomialProduct A B n

/-- Constant coefficients multiply. -/
example (A B : PowerSeries ℤ) :
    PowerSeries.coeff 0 (binomialProduct A B) = PowerSeries.coeff 0 A * PowerSeries.coeff 0 B :=
  constantCoeff_binomialProduct A B

/-- `x ⊙ x = 2x²`: the coefficient of `x²` is `binom(2, 1) = 2` (not `1`, as for the Cauchy
product). -/
example :
    PowerSeries.coeff 2 (binomialProduct (PowerSeries.X : PowerSeries ℚ) PowerSeries.X) = 2 := by
  norm_num [coeff_binomialProduct, Finset.sum_range_succ, PowerSeries.coeff_X]

end MetaMathlibExt
