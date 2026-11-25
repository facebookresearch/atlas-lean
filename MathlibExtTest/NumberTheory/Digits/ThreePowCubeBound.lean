/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.ThreePowCubeBound

/-! # Boundary cases for the power of three dividing a cube plus one -/

-- When both exponents are zero, the hypothesis and conclusion concern the number two.
example : ¬ 9 ∣ 2 :=
  MetaMathlibExt.three_pow_not_dvd_two_pow_add_one_cube 0 0 (by decide)

-- Tripling the exponent from three to nine raises the multiplicity from two to three.
example : 27 ∣ 2 ^ 9 + 1 ∧ ¬ 81 ∣ 2 ^ 9 + 1 :=
  ⟨by decide, MetaMathlibExt.three_pow_not_dvd_two_pow_add_one_cube 2 3 (by decide)⟩
