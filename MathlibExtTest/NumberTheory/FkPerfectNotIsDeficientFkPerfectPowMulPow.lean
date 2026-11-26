/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FkPerfectNotIsDeficientFkPerfectPowMulPow
namespace MathlibExtTest.NumberTheory.FkPerfect

open MathlibExt.NumberTheory.FkPerfectWanted

-- `3 ^ 1 * 5 ^ 2` is not deficient `F₂`-perfect: `1 + 2` is odd.
example : ¬ IsDeficientFkPerfect 2 (3 ^ 1 * 5 ^ 2) :=
  not_isDeficientFkPerfect_pow_mul_pow 2 3 5 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))

-- `3 ^ 1 * 5 ^ 1` is not deficient `F₃`-perfect: both exponents are odd.
example : ¬ IsDeficientFkPerfect 3 (3 ^ 1 * 5 ^ 1) :=
  not_isDeficientFkPerfect_pow_mul_pow 3 3 5 1 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (Or.inr ⟨by decide, by decide⟩)

end MathlibExtTest.NumberTheory.FkPerfect
