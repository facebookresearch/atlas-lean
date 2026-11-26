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

end MathlibExtTest.NumberTheory.BernoulliDerivativeDenominatorBernoulliDerivativeIntegralIff
