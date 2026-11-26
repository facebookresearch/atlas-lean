/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SecondOrderGenFunIntegerValuesExistsSmallSecondOrderMValueOfNeg
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for a small value of `M` with negative invariant

The example applies the small-value theorem to the family with initial terms `3, 7` and
coefficient `2`, for `a = 0` and `b = 2`. Oddness proves that every term is nonzero.

Source: Luu Ba Thang and Nguyen Duy Nguyen, *Integer Values of Generating Functions for a
Type of Second-Order Linear Recurrence Sequence*, Journal of Integer Sequences 28 (2025),
Article 25.8.3, Lemma 9 (`jis-2025-25.8.3-lem-9`).
-/

namespace MathlibExtTest.NumberTheory
namespace SecondOrderGenFunIntegerValuesExistsSmallSecondOrderMValueOfNeg

open MetaMathlibExt

private theorem odd_secondOrderBiSeq_of_even {p r s : ℤ} (hp : Even p) (hr : Odd r)
    (hs : Odd s) (n : ℤ) :
    Odd (secondOrderBiSeq p r s n) ∧ Odd (secondOrderBiSeq p r s (n + 1)) := by
  refine Int.inductionOn' n 0 ⟨hr, hs⟩ ?_ ?_
  · rintro k - ⟨h₀, h₁⟩
    refine ⟨h₁, ?_⟩
    rw [add_assoc, one_add_one_eq_two, secondOrderBiSeq_add_two]
    exact (hp.mul_right _).add_odd h₀
  · rintro k - ⟨h₀, h₁⟩
    rw [sub_add_cancel]
    refine ⟨?_, h₀⟩
    have h := secondOrderBiSeq_add_two p r s (k - 1)
    have heq : k - 1 + 2 = k + 1 := by ring
    rw [heq, sub_add_cancel] at h
    have hprev : secondOrderBiSeq p r s (k - 1) =
        secondOrderBiSeq p r s (k + 1) - p * secondOrderBiSeq p r s k := by linarith
    rw [hprev]
    exact h₁.sub_even (hp.mul_right _)

example : ∃ n : ℤ, |(secondOrderMValue 0 2 2 (secondOrderBiSeq 2 3 7 n)
    (secondOrderBiSeq 2 3 7 (n + 1)) : ℝ)| ≤ 2 := by
  have hodd (n : ℤ) : Odd (secondOrderBiSeq 2 3 7 n) :=
    (odd_secondOrderBiSeq_of_even (by decide) (by decide) (by decide) n).1
  have h := exists_small_secondOrderMValue_of_neg 0 2 2 (by norm_num) (by norm_num) 3 7
    (by norm_num) (by decide) ⟨-21, by norm_num [secondOrderGenValue]⟩
    fun n hn => Int.not_odd_zero (hn ▸ hodd n)
  have hsqrt : √(4 : ℝ) = 2 := by
    have heq : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [heq, Real.sqrt_sq (by norm_num)]
  simpa [hsqrt] using h

end SecondOrderGenFunIntegerValuesExistsSmallSecondOrderMValueOfNeg
end MathlibExtTest.NumberTheory
