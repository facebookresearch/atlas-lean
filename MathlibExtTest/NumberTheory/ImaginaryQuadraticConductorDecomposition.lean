/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ImaginaryQuadraticConductorDecomposition
import Mathlib.Data.Nat.Squarefree

set_option autoImplicit false

/-! # Tests for `MathlibExt.NumberTheory.ImaginaryQuadraticConductorDecomposition` -/

namespace MathlibExtTest.ImaginaryQuadraticConductorDecomposition

open ImaginaryQuadraticDiscriminant

/-- `-3` is a fundamental imaginary quadratic discriminant. -/
theorem fundamental_neg_three : IsFundamentalImaginaryQuadraticDiscriminant (-3) :=
  ⟨by norm_num, Or.inl ⟨Int.squarefree_natAbs.mp Nat.prime_three.prime.squarefree, by decide⟩⟩

/-- `-4 = 4 * (-1)` is a fundamental imaginary quadratic discriminant. -/
theorem fundamental_neg_four : IsFundamentalImaginaryQuadraticDiscriminant (-4) :=
  ⟨by norm_num, Or.inr ⟨-1, by norm_num, isUnit_one.neg.squarefree, by decide⟩⟩

/-- `-12 = 2 ^ 2 * (-3)`. -/
example : ImaginaryQuadraticDiscriminantDecomposition (-12) :=
  .ofFundamental 2 (-3) (by norm_num) fundamental_neg_three (by norm_num)

/-- `-16 = 2 ^ 2 * (-4)`. -/
example : ImaginaryQuadraticDiscriminantDecomposition (-16) :=
  .ofFundamental 2 (-4) (by norm_num) fundamental_neg_four (by norm_num)

-- The theorem applies to the non-fundamental discriminants `-12`, `-16`, `-27` and `-63`.
example : Nonempty (ImaginaryQuadraticDiscriminantDecomposition (-12)) :=
  exists_conductor_decomposition (isImaginaryQuadraticDiscriminant_of_mod_zero (by norm_num)
    (by norm_num))

example : Nonempty (ImaginaryQuadraticDiscriminantDecomposition (-16)) :=
  exists_conductor_decomposition (isImaginaryQuadraticDiscriminant_of_mod_zero (by norm_num)
    (by norm_num))

example : Nonempty (ImaginaryQuadraticDiscriminantDecomposition (-27)) :=
  exists_conductor_decomposition (isImaginaryQuadraticDiscriminant_of_mod_one (by norm_num)
    (by norm_num))

example : Nonempty (ImaginaryQuadraticDiscriminantDecomposition (-63)) :=
  exists_conductor_decomposition (isImaginaryQuadraticDiscriminant_of_mod_one (by norm_num)
    (by norm_num))

/-- Every decomposition of `-3` has conductor `1`: `u ^ 2 ∣ 3` with `u ≥ 1` forces `u = 1`. -/
example (h : ImaginaryQuadraticDiscriminantDecomposition (-3)) : h.u = 1 := by
  have hu := h.hu
  have hD := h.hD
  have hK := h.hD_K.1
  nlinarith

end MathlibExtTest.ImaginaryQuadraticConductorDecomposition
