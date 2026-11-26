/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import MathlibExt.NumberTheory.ArithmeticFunction.NonagonalAdditiveUniquenessMultiplicativeNonagonalAdditiveSevenPow

/-!
# Tests for the step at powers of 7

The identity function satisfies the prefix hypothesis definitionally, and at `49` the theorem
gives the value from the values below.
-/

namespace MathlibExtTest.NumberTheory.ArithmeticFunction.NonagonalAdditiveUniquenessMultiplicativeNonagonalAdditiveSevenPow

open _root_.ArithmeticFunction MetaMathlibExt

example (r : ℕ) : (ArithmeticFunction.id : ArithmeticFunction ℂ) (7 ^ r) = (7 ^ r : ℕ) :=
  multiplicative_nonagonal_additive_seven_pow _ isMultiplicative_id.natCast
    (fun a b _ _ _ _ ↦ Nat.cast_add a b) r (fun _ _ ↦ rfl)

example (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, 0 < a → 0 < b →
      (∃ m : ℤ, 2 * (a : ℤ) = m * (7 * m - 5)) → (∃ m : ℤ, 2 * (b : ℤ) = m * (7 * m - 5)) →
        f (a + b) = f a + f b)
    (hind : ∀ n : ℕ, n < 49 → f n = n) : f 49 = 49 := by
  have h := multiplicative_nonagonal_additive_seven_pow f hf hadd 2 (by simpa using hind)
  simpa using h

end MathlibExtTest.NumberTheory.ArithmeticFunction.NonagonalAdditiveUniquenessMultiplicativeNonagonalAdditiveSevenPow
