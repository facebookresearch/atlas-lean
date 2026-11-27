/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Bernoulli.DerivativeDenominator

open MetaMathlibExt

-- At the lower endpoint both products are empty.
example : bernoulliDiffDenominatorLargePart 1 = 1 ∧ bernoulliDiffDenominatorCoprimePart 1 = 1 := by
  decide

-- At 21 the large-prime factors are 5 and 11. The base-7 digits of 21 sum to 3.
-- The coprime product also includes 2.
example : bernoulliDiffDenominatorLargePart 21 = 55 ∧
    bernoulliDiffDenominatorCoprimePart 21 = 110 := by
  decide

-- Since `B₁'(x) = 1` is integral, the denominator of `B₀(x)` divides `1`.
example : polynomialDenominator (Polynomial.bernoulli 0) ∣ 0 + 1 :=
  (succ_mem_bernoulliIntegralDerivativeIndices_one_iff 0).mp
    one_mem_bernoulliIntegralDerivativeIndices_one
