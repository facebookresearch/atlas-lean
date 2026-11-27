/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BernoulliDerivativeDenominatorBernoulliDerivativeIntegralIff

/-! # Tests for `BernoulliDerivativeDenominatorBernoulliDerivativeIntegralIff` -/

namespace MathlibExtTest.NumberTheory.BernoulliDerivativeDenominatorBernoulliDerivativeIntegralIff

open MetaMathlibExt

example : bernoulliDiffDenominatorCoprimePart 1 = 1 :=
  (bernoulli_derivative_integral_iff 1 le_rfl).1.mp
    one_mem_bernoulliIntegralDerivativeIndices_one

example : (1 + 1 : ℕ).Prime :=
  (bernoulli_derivative_integral_iff 1 le_rfl).2.2
    one_mem_bernoulliIntegralDerivativeIndices_one

example : polynomialDenominator (Polynomial.bernoulli 0) =
    UniqueFactorizationMonoid.radical 1 :=
  (bernoulli_derivative_integral_iff 1 le_rfl).2.1.mp (by decide +kernel)

-- `n = 2`: `𝔻^⊥₂ = 1`, so `B₂'(x) = 2x - 1` is integral and the denominator of `B₁(x)` is
-- `rad 2 = 2`.
example : 2 ∈ bernoulliIntegralDerivativeIndices 1 :=
  (bernoulli_derivative_integral_iff 2 (by decide)).1.mpr (by decide)

example : polynomialDenominator (Polynomial.bernoulli 1) =
    UniqueFactorizationMonoid.radical 2 :=
  (bernoulli_derivative_integral_iff 2 (by decide)).2.1.mp (by decide)

-- `n = 3`: `𝔻^⊥₃ = 2`, so `B₃'(x) = 3x² - 3x + 1/2` is not integral and the denominator of
-- `B₂(x)` (which is 6) is not `rad 3 = 3`.
example : 3 ∉ bernoulliIntegralDerivativeIndices 1 := fun h =>
  absurd ((bernoulli_derivative_integral_iff 3 (by decide)).1.mp h) (by decide)

example : polynomialDenominator (Polynomial.bernoulli 2) ≠
    UniqueFactorizationMonoid.radical 3 := fun h =>
  absurd ((bernoulli_derivative_integral_iff 3 (by decide)).2.1.mpr h) (by decide)

end MathlibExtTest.NumberTheory.BernoulliDerivativeDenominatorBernoulliDerivativeIntegralIff
