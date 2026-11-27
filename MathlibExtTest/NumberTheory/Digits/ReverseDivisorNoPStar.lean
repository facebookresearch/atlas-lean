/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.ReverseDivisorNoPStar

/-! # Tests for the obstruction to property $P^*$ for reverse divisors -/

open MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

-- A reverse divisor with quotient 9.
example : ¬ HasPropertyPStar 1089 :=
  not_hasPropertyPStar_of_isReverseDivisor 1089
    ((isReverseDivisor_iff 1089).mpr ⟨by decide, 9, by decide, by decide⟩)

-- A reverse divisor with quotient 4.
example : ¬ HasPropertyPStar 2178 :=
  not_hasPropertyPStar_of_isReverseDivisor 2178
    ((isReverseDivisor_iff 2178).mpr ⟨by decide, 4, by decide, by decide⟩)
