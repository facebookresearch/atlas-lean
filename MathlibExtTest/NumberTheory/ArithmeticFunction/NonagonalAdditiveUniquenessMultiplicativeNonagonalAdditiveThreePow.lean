/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import MathlibExt.NumberTheory.ArithmeticFunction.NonagonalAdditiveUniquenessMultiplicativeNonagonalAdditiveThreePow

/-!
# Tests for the nonagonal power-of-three step

The natural inclusion into the complex numbers realizes the hypotheses at `r = 2`.
-/

open ArithmeticFunction MetaMathlibExt

namespace MathlibExtTest.NumberTheory.ArithmeticFunction.NonagonalAdditiveUniquenessMultiplicativeNonagonalAdditiveThreePow

example : (ArithmeticFunction.id : ArithmeticFunction ℂ) (3 ^ 2) = ((3 ^ 2 : ℕ) : ℂ) :=
  multiplicative_nonagonal_additive_three_pow _ isMultiplicative_id.natCast
    (fun a b _ _ _ _ ↦ Nat.cast_add a b) 2 (fun _ _ ↦ rfl)

end MathlibExtTest.NumberTheory.ArithmeticFunction.NonagonalAdditiveUniquenessMultiplicativeNonagonalAdditiveThreePow
