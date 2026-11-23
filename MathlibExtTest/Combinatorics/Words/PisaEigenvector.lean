/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Words.PisaEigenvector

/-! # Tests for integer matrices with a Pisa eigenvector -/

namespace MetaMathlibExt.pisa_eigenvector_iff

private theorem not_isSquare_five : ¬ IsSquare (1 ^ 2 + 4 * 1 : ℕ) := by
  rintro ⟨r, hr⟩
  have hr3 : r < 3 := by nlinarith
  interval_cases r <;> omega

/-- For `j = m = 1`, `τ` is the golden ratio. -/
private theorem tau_one_one :
    (((1 : ℕ) : ℝ) + √(((1 : ℕ) : ℝ) ^ 2 + 4 * ((1 : ℕ) : ℝ))) / 2 = (1 + √5) / 2 := by
  norm_num

/-- For `j = 1` and `m = 2`, `j ^ 2 + 4 * m = 3 ^ 2` and `τ = 2`. -/
private theorem tau_one_two :
    (((1 : ℕ) : ℝ) + √(((1 : ℕ) : ℝ) ^ 2 + 4 * ((2 : ℕ) : ℝ))) / 2 = 2 := by
  rw [show ((1 : ℕ) : ℝ) ^ 2 + 4 * ((2 : ℕ) : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

-- Part (a), `j = m = 1`, `s = 1`, `t = 0`: the golden ratio vector is an eigenvector of the
-- Fibonacci matrix.
example : ∃ c : ℝ, ((!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ)).mulVec
    ![(1 + √5) / 2, 1] = c • ![(1 + √5) / 2, 1] := by
  have h := ((pisa_eigenvector_iff 1 1 le_rfl le_rfl !![1, 1; 1, 0]).1 not_isSquare_five).2
    ⟨1, 0, by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
  simpa only [tau_one_one] using h

-- Part (a), only if: a diagonal matrix with distinct diagonal entries does not have the golden
-- ratio vector as an eigenvector, since its rows are not of the form `(t + s, s)`, `(s, t)`.
example : ¬ ∃ c : ℝ, ((!![1, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ)).mulVec
    ![(1 + √5) / 2, 1] = c • ![(1 + √5) / 2, 1] := by
  have h := (pisa_eigenvector_iff 1 1 le_rfl le_rfl !![1, 0; 0, 2]).1 not_isSquare_five
  simp only [tau_one_one] at h
  rw [h]
  rintro ⟨s, t, hst⟩
  have h00 := congrFun (congrFun hst 0) 0
  have h10 := congrFun (congrFun hst 1) 0
  have h11 := congrFun (congrFun hst 1) 1
  simp at h00 h10 h11
  omega

-- Part (b), `j = 1`, `m = 2`, `r = 3`: `τ = 2`, and `1 * 4 ^ 2 + 2 * (0 - 1) * 4 - 4 * 2 = 0`.
example : ∃ c : ℝ, ((!![1, 2; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ)).mulVec
    ![2, 1] = c • ![2, 1] := by
  have h := (pisa_eigenvector_iff 1 2 le_rfl (by norm_num) !![1, 2; 1, 0]).2 3 (by norm_num)
  simp only [tau_one_two] at h
  exact h.2 ⟨1, 2, 1, 0, by norm_num, rfl⟩

-- Part (b) uses the nonnegative root `r = 3`. The matrix with rows `(0, 0)` and `(1, 1)` satisfies
-- the condition for the negative root `r = -3`, but not for `r = 3`, and `(2, 1)` is not one of
-- its eigenvectors.
example : ¬ ∃ c : ℝ, ((!![0, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ)).mulVec
    ![2, 1] = c • ![2, 1] := by
  have h := (pisa_eigenvector_iff 1 2 le_rfl (by norm_num) !![0, 0; 1, 1]).2 3 (by norm_num)
  simp only [tau_one_two] at h
  rw [h]
  rintro ⟨s, t, u, v, hc, hM⟩
  have h00 := congrFun (congrFun hM 0) 0
  have h01 := congrFun (congrFun hM 0) 1
  have h10 := congrFun (congrFun hM 1) 0
  have h11 := congrFun (congrFun hM 1) 1
  simp at h00 h01 h10 h11
  subst h00 h01 h10 h11
  norm_num at hc

end MetaMathlibExt.pisa_eigenvector_iff
