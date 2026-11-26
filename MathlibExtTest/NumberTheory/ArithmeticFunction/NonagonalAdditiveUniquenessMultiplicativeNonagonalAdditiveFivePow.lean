/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import MathlibExt.NumberTheory.ArithmeticFunction.NonagonalAdditiveUniquenessMultiplicativeNonagonalAdditiveFivePow

/-!
# Tests for nonagonal additive uniqueness: the step at powers of 5

The natural inclusion into the complex numbers realizes both hypotheses.
-/

open ArithmeticFunction MetaMathlibExt

namespace MathlibExtTest.NumberTheory.ArithmeticFunction.NonagonalAdditiveUniquenessMultiplicativeNonagonalAdditiveFivePow

example : (ArithmeticFunction.id : ArithmeticFunction ℂ) (5 ^ 3) = ((5 ^ 3 : ℕ) : ℂ) :=
  multiplicative_nonagonal_additive_five_pow _ isMultiplicative_id.natCast
    (fun a b _ _ _ _ ↦ Nat.cast_add a b) (by decide) (fun _ _ ↦ rfl)

example : (ArithmeticFunction.id : ArithmeticFunction ℂ) (5 ^ 4) = ((5 ^ 4 : ℕ) : ℂ) :=
  multiplicative_nonagonal_additive_five_pow _ isMultiplicative_id.natCast
    (fun a b _ _ _ _ ↦ Nat.cast_add a b) (by decide) (fun _ _ ↦ rfl)

end MathlibExtTest.NumberTheory.ArithmeticFunction.NonagonalAdditiveUniquenessMultiplicativeNonagonalAdditiveFivePow
