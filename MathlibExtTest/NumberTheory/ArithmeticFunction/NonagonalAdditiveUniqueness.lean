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
