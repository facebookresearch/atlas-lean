/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedFermatFactorCount

/-! # Tests for prime factor counts of generalized Fermat numbers -/

-- The terms at indices zero and one are 3 and 9.
example : ArithmeticFunction.cardFactors (2 ^ 3 ^ (0 : ℕ) + 1) ≤
    ArithmeticFunction.cardFactors (2 ^ 3 ^ (1 : ℕ) + 1) :=
  MetaMathlibExt.monotone_cardFactors_pow_pow_add_one (a := 2) (b := 3)
    (ha := by decide) (hb := by decide) (hbo := by decide) (by decide)
