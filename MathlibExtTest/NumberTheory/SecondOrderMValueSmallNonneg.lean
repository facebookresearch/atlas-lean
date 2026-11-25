/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SecondOrderMValueSmallNonneg
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

-- For an even coefficient and odd initial values every term is odd, so no term vanishes.
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
    rw [show k - 1 + 2 = k + 1 by ring, sub_add_cancel] at h
    rw [show secondOrderBiSeq p r s (k - 1) =
      secondOrderBiSeq p r s (k + 1) - p * secondOrderBiSeq p r s k by linarith]
    exact h₁.sub_even (hp.mul_right _)

-- With `(a, b, p) = (1, 1, 2)` the bound is `√(8 / 8) = 1`. At `3 / 7` the generating function
-- takes the value `-14` and `M(3, 7) = -41`, but some member of the family has `|M| ≤ 1`.
example : ∃ n : ℤ, |(secondOrderMValue 1 1 2 (secondOrderBiSeq 2 3 7 n)
    (secondOrderBiSeq 2 3 7 (n + 1)) : ℝ)| ≤ 1 := by
  have hodd (n : ℤ) : Odd (secondOrderBiSeq 2 3 7 n) :=
    (odd_secondOrderBiSeq_of_even (by decide) (by decide) (by decide) n).1
  have h := exists_small_secondOrderMValue_of_nonneg 1 1 2 (by norm_num) (by norm_num) 3 7
    (by norm_num) (by decide) ⟨-14, by norm_num [secondOrderGenValue]⟩
    fun n hn => Int.not_odd_zero (hn ▸ hodd n)
  norm_num at h
  exact h

example : secondOrderMValue 1 1 2 3 7 = -41 := by
  norm_num [secondOrderMValue]

-- The bound is attained: at `1 / 1` the generating function vanishes and `M(1, 1) = -1`.
example : secondOrderGenValue 1 1 2 1 = 0 ∧ secondOrderMValue 1 1 2 1 1 = -1 ∧
    √(((1 * 1 * 2 ^ 3 + (1 ^ 2 - 1 ^ 2) * 2 ^ 2 : ℤ) : ℝ) / (2 ^ 2 + 4)) = 1 := by
  norm_num [secondOrderGenValue, secondOrderMValue]

end MetaMathlibExt
