/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.ReverseDivisorBasicNineNoPStar

/-! # Tests for basic quotient-nine reverse divisors and property $P^*$ -/

open MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

example : ¬ HasPropertyPStar 1089 :=
  not_hasPropertyPStar_basic_nine 2 (by decide)

example : ¬ HasPropertyPStar 10989 :=
  not_hasPropertyPStar_basic_nine 3 (by decide)

-- At k = 1 the expression is 99, which does have the property.
example : HasPropertyPStar (11 * (10 ^ 1 - 1)) :=
  (hasPropertyPStar_iff_dvd 99 (by decide)).mpr (by decide)
