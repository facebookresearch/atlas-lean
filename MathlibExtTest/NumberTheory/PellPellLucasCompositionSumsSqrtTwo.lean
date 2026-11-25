/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PellPellLucasCompositionSumsSqrtTwo
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

open scoped BigOperators

/-- The even case `n = 2` of the first composition sum: the sum is `1`. -/
example :
    (∑ c : Composition 2, ∏ i : Fin c.length,
        ((c.blocksFun i : ℝ) - 1) * Real.sqrt 2 ^ (c.blocksFun i - 2)) = 1 := by
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h := (pell_pellLucas_composition_sums_sqrt_two 2 (by decide)).1
  norm_num [pellNumber, pellLucas, hsq] at h ⊢
  exact h

/-- The even case `n = 2` of the second composition sum: the sum is `7 / 2`. -/
example :
    (∑ c : Composition 2, ∏ i : Fin c.length,
        ((c.blocksFun i : ℝ) + 1) / Real.sqrt 2 ^ c.blocksFun i) = 7 / 2 := by
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h := (pell_pellLucas_composition_sums_sqrt_two 2 (by decide)).2
  norm_num [pellNumber, pellLucas, hsq] at h ⊢
  exact h

/-- The odd case `n = 3` of the first composition sum: the sum is `2 * √2`. -/
example :
    (∑ c : Composition 3, ∏ i : Fin c.length,
        ((c.blocksFun i : ℝ) - 1) * Real.sqrt 2 ^ (c.blocksFun i - 2)) =
      2 * Real.sqrt 2 := by
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h := (pell_pellLucas_composition_sums_sqrt_two 3 (by decide)).1
  norm_num [pellNumber, pellLucas, hsq] at h ⊢
  have hodd : Odd (3 : ℕ) := by decide
  simp only [hodd, ite_true] at h
  exact h.trans (by ring)

/-- The odd case `n = 3` of the second composition sum: the sum is `6 * √2`. -/
example :
    (∑ c : Composition 3, ∏ i : Fin c.length,
        ((c.blocksFun i : ℝ) + 1) / Real.sqrt 2 ^ c.blocksFun i) =
      6 * Real.sqrt 2 := by
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  have h := (pell_pellLucas_composition_sums_sqrt_two 3 (by decide)).2
  norm_num [pellNumber, pellLucas, hsq] at h ⊢
  have hodd : Odd (3 : ℕ) := by decide
  simp only [hodd, ite_true] at h
  refine h.trans ?_
  rw [div_eq_iff hne]
  have h6 : (6 : ℝ) * Real.sqrt 2 * Real.sqrt 2 = 6 * (Real.sqrt 2) ^ 2 := by ring
  rw [h6, hsq]
  norm_num

end MetaMathlibExt
