/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.MultiplicativeAdditivePairedSquares
import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace MetaMathlibExt

open ArithmeticFunction

-- The identity arithmetic function realizes all three hypotheses.
example (n : ℕ) (hn : n ∈ ({2, 3, 4, 5, 6, 7, 8, 10} : Finset ℕ)) :
    (ArithmeticFunction.id : ArithmeticFunction ℂ) n = n := by
  apply multiplicative_four_additive_two_squares_base _ isMultiplicative_id.natCast _ _ n hn
  · intro A _
    simp
  · norm_num

-- The Dirichlet convolution unit is four-additive on these sums but vanishes at two.
example :
    let f := (1 : ArithmeticFunction ℂ)
    f.IsMultiplicative ∧
      (∀ A : Fin 4 → ℕ, (∀ i, ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ A i = a ^ 2 + b ^ 2) →
        f (∑ i, A i) = ∑ i, f (A i)) ∧ f 2 = 0 := by
  refine ⟨isMultiplicative_one, ?_, one_apply_ne (by decide)⟩
  intro A hA
  have hlt (i : Fin 4) : 1 < A i := by
    obtain ⟨a, b, ha, hb, hab⟩ := hA i
    have := pow_pos ha 2
    have := pow_pos hb 2
    omega
  have hsum : 1 < ∑ i, A i :=
    (hlt 0).trans_le (Finset.single_le_sum (fun i _ ↦ Nat.zero_le (A i)) (Finset.mem_univ 0))
  simp [one_apply, hsum.ne', fun i ↦ (hlt i).ne']

end MetaMathlibExt
