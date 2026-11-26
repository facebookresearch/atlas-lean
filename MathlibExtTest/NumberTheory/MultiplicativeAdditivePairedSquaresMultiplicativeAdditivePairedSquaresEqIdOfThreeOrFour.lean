/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.MultiplicativeAdditivePairedSquaresMultiplicativeAdditivePairedSquaresEqIdOfThreeOrFour
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! # Tests for the six-or-eight paired-squares identity theorem -/

namespace MathlibExtTest.NumberTheory.MultiplicativeAdditivePairedSquaresMultiplicativeAdditivePairedSquaresEqIdOfThreeOrFour

open ArithmeticFunction MetaMathlibExt

-- The identity arithmetic function realizes all the hypotheses for `k = 3`.
example (n : ℕ) (hn : 0 < n) :
    (ArithmeticFunction.id : ArithmeticFunction ℂ) n = n := by
  apply multiplicative_additive_paired_squares_eq_id_of_three_or_four 3 (Or.inl rfl) _
    isMultiplicative_id.natCast _ _ n hn
  · intro x y _ _
    simp
  · norm_num

-- The Dirichlet convolution unit is additive on three paired squares but vanishes at two.
example :
    let f := (1 : ArithmeticFunction ℂ)
    f.IsMultiplicative ∧
      (∀ x y : Fin 3 → ℕ, (∀ j, 0 < x j) → (∀ j, 0 < y j) →
        f (∑ j, (x j ^ 2 + y j ^ 2)) = ∑ j, f (x j ^ 2 + y j ^ 2)) ∧ f 2 = 0 := by
  refine ⟨isMultiplicative_one, ?_, one_apply_ne (by decide)⟩
  intro x y hx hy
  have hw (j : Fin 3) : 1 < x j ^ 2 + y j ^ 2 := by
    have := pow_pos (hx j) 2
    have := pow_pos (hy j) 2
    omega
  have hsum : 1 < ∑ j, (x j ^ 2 + y j ^ 2) :=
    (hw 0).trans_le
      (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (x j ^ 2 + y j ^ 2))
        (Finset.mem_univ 0))
  simp [hsum.ne', fun j ↦ (hw j).ne']

end MathlibExtTest.NumberTheory.MultiplicativeAdditivePairedSquaresMultiplicativeAdditivePairedSquaresEqIdOfThreeOrFour
