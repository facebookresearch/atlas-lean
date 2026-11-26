/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FkPerfect

namespace MathlibExtTest.NumberTheory.FkPerfect

-- `3 * 5` is not near `F₂`-perfect: both exponents are odd.
example : ¬ MathlibExt.NumberTheory.FkPerfectWanted.IsNearFkPerfect 2 (3 * 5) := by
  have h := MathlibExt.NumberTheory.FkPerfectWanted.not_isNearFkPerfect_pow_mul_pow
    2 3 5 1 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    le_rfl le_rfl (Or.inr ⟨by decide, by decide⟩)
  simpa using h

-- `3 * 5 ^ 2` is not near `F₂`-perfect: the exponent sum is odd.
example : ¬ MathlibExt.NumberTheory.FkPerfectWanted.IsNearFkPerfect 2 (3 * 5 ^ 2) :=
  MathlibExt.NumberTheory.FkPerfectWanted.not_isNearFkPerfect_pow_mul_pow
    2 3 5 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    le_rfl (by decide) (Or.inl (by decide))

end MathlibExtTest.NumberTheory.FkPerfect
