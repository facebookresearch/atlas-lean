/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedTauCoprime

open MetaMathlibExt

-- A proper divisor of the exponent gives a composite modulus.
example : generalizedTau 12 23 ≡ 0 [ZMOD 6] :=
  generalizedTau_modEq_zero_of_coprime (m := 1) (k := 12) (hk := by decide)
    (d := 2) (hd := by decide) (hdk := by decide) (r := 5) (hr := by decide)

-- Negative exponents use the same congruence, including at m = 0.
example : generalizedTau (-12) 9 ≡ 0 [ZMOD 3] :=
  generalizedTau_modEq_zero_of_coprime (m := 0) (k := -12) (hk := by decide)
    (d := 4) (hd := by decide) (hdk := by decide) (r := 2) (hr := by decide)
