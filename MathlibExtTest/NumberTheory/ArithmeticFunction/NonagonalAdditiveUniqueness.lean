/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import MathlibExt.NumberTheory.ArithmeticFunction.NonagonalAdditiveUniqueness

/-!
# Tests for nonagonal additive uniqueness

The natural inclusion into the complex numbers realizes both hypotheses.
-/

open ArithmeticFunction MetaMathlibExt

example (n : ℕ) (hn : 1 ≤ n) (hle : n ≤ 11) :
    (ArithmeticFunction.id : ArithmeticFunction ℂ) n = n :=
  multiplicative_nonagonal_additive_eq_self_of_le_eleven _ isMultiplicative_id.natCast
    (fun a b _ _ _ _ ↦ Nat.cast_add a b) n hn hle

-- The same witness gives the unrestricted identity, including the zero argument.
example : ∀ n : ℕ, (ArithmeticFunction.id : ArithmeticFunction ℂ) n = n :=
  multiplicative_nonagonal_additive_eq_id _ isMultiplicative_id.natCast
    (fun a b _ _ _ _ ↦ Nat.cast_add a b)

-- Exponent zero: the public induction hypothesis only asks for the value at zero.
example (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ a b : ℕ, 0 < a → 0 < b →
      (∃ m : ℤ, 2 * (a : ℤ) = m * (7 * m - 5)) → (∃ m : ℤ, 2 * (b : ℤ) = m * (7 * m - 5)) →
        f (a + b) = f a + f b) : f 1 = 1 := by
  simpa using multiplicative_nonagonal_additive_two_pow f hf hadd 0 (by
    intro n hn
    have hn0 : n = 0 := by omega
    simp [hn0])

-- The natural inclusion meets the hypotheses at the power 2 ^ 4 = 16.
example : (ArithmeticFunction.id : ArithmeticFunction ℂ) 16 = 16 :=
  multiplicative_nonagonal_additive_two_pow _ isMultiplicative_id.natCast
    (fun a b _ _ _ _ ↦ Nat.cast_add a b) 4 (fun _ _ ↦ rfl)
