/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.MultiplicativeAdditivePairedSquaresRigidity
import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace MetaMathlibExt

open ArithmeticFunction

-- At k = 5, the three witnesses exercise respectively 1² + 1², the offset 11,
-- and the inclusive lower endpoint 2k + 14.
example (β : ℕ) (hβ : β ∈ ({2, 21, 24} : Finset ℕ)) (n : ℕ) (hn : 0 < n) :
    (ArithmeticFunction.id : ArithmeticFunction ℂ) n = n := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hβ
  apply multiplicative_additive_paired_squares_eq_id_of_ne_zero 5 (by decide) _
    isMultiplicative_id.natCast _ β _ _ n hn
  · intro x y _ _
    simp
  · rcases hβ with rfl | rfl | rfl
    · exact Or.inl ⟨1, 1, by decide, by decide, rfl⟩
    · exact Or.inr (Or.inl ⟨11, by decide, rfl⟩)
    · exact Or.inr (Or.inr (by decide))
  · rcases hβ with rfl | rfl | rfl <;> norm_num

end MetaMathlibExt
