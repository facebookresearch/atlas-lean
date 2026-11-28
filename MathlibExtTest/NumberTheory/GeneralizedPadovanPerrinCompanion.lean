/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedPadovanPerrinCompanion

/-! # Tests for the powers of the Padovan–Perrin companion matrix -/

open MetaMathlibExt

-- At exponent zero the reversed initial values give both entries of each identity column.
example (k₁ k₂ : ℤ) (i j : Fin 2) :
    (if i = j then (1 : ℤ) else 0) = padovanPerrinFundamental k₁ k₂ 1 1 (2 - j) (1 - i) := by
  simpa only [pow_zero, Matrix.one_apply, Nat.zero_add] using
    padovanPerrin_companion_pow_apply k₁ k₂ 1 1 one_pos one_pos 0 i j

-- Row 1 of column 2 of the fifth power gives term 6 of the first fundamental sequence.
example : padovanPerrinFundamental (2 : ℤ) (-3) 1 2 1 6 = 9 := by
  have h := padovanPerrin_companion_pow_apply (2 : ℤ) (-3) 1 2 one_pos two_pos 5 1 2
  exact h.symm.trans (by decide)
