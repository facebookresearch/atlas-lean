/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime
import MathlibExt.NumberTheory.Recurrences.LucasSequenceDivisibilityIsLucasFrobeniusPseudoprimeOfIsEulerLucasPseudoprime

/-! # Tests for from Euler–Lucas to Frobenius pseudoprimes -/

namespace MathlibExtTest.NumberTheory.Recurrences.LucasSequenceDivisibilityIsLucasFrobeniusPseudoprimeOfIsEulerLucasPseudoprime

open MetaMathlibExt

-- The pair `(P, Q) = (4, -1)` is nondegenerate: for `α + β = 4` and `αβ = -1`,
-- `‖α / β‖ = 1` would force `‖α‖ = ‖β‖ = 1`, contradicting `‖α + β‖ = 4`.
private theorem nondegenerate_four_neg_one : IsNondegenerateLucasPair 4 (-1) := by
  refine ⟨by norm_num, fun α β hsum hprod hfin => ?_⟩
  have hnorm := hfin.norm_eq_one
  have hprod_norm : ‖α‖ * ‖β‖ = 1 := by
    have h := congrArg norm hprod
    rw [norm_mul] at h
    norm_num at h
    exact h
  have hβ0 : ‖β‖ ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hprod_norm
    norm_num at hprod_norm
  have hαβ : ‖α‖ = ‖β‖ := by
    rw [norm_div] at hnorm
    exact (div_eq_one_iff_eq hβ0).mp hnorm
  have hβ1 : ‖β‖ = 1 := by
    have hsq : ‖β‖ ^ 2 = 1 := by
      rw [hαβ] at hprod_norm
      linear_combination hprod_norm
    rcases sq_eq_one_iff.mp hsq with h | h
    · exact h
    · exfalso
      have hnn := norm_nonneg β
      rw [h] at hnn
      norm_num at hnn
  have hα1 : ‖α‖ = 1 := hαβ.trans hβ1
  have hsum_norm : ‖α + β‖ = 4 := by
    rw [hsum]
    norm_num
  have htri := norm_add_le α β
  rw [hsum_norm, hα1, hβ1] at htri
  norm_num at htri

-- For `(P, Q) = (4, -1)`, the number `9` is an Euler–Lucas pseudoprime (here
-- `(D/9) = (Q/9) = 1` and `U_4 = 72`) and an Euler pseudoprime to the base `Q`,
-- hence a Frobenius pseudoprime by the main theorem.
private theorem frobenius_nine :
    IsLucasFrobeniusPseudoprime ⟨4, -1, by decide⟩ 9 := by
  refine isLucasFrobeniusPseudoprime_of_isEulerLucasPseudoprime _
    nondegenerate_four_neg_one 9 ?_ ?_ ?_
  · have hj : jacobiSym ((4 : ℤ) ^ 2 - 4 * (-1)) 9 = 1 := by norm_num
    have hq : jacobiSym (-1 : ℤ) 9 = 1 := by norm_num
    refine ⟨by decide, by norm_num, by norm_num, by decide, fun _ => ?_, fun h => ?_⟩
    · simp only [lucasPseudoprimeIndex, hj]
      decide
    · simp only [hq] at h
      norm_num at h
  · have hj : jacobiSym (-1 : ℤ) 9 = 1 := by norm_num
    refine ⟨by decide, by norm_num, by norm_num, by decide, ?_⟩
    simp only [hj]
    decide
  · decide

-- A Frobenius pseudoprime is in particular a Lucas pseudoprime.
example : IsLucasPseudoprime ⟨4, -1, by decide⟩ 9 := by
  obtain ⟨-, h, -, -, -⟩ := frobenius_nine
  exact h

-- A Frobenius pseudoprime is in particular a Dickson pseudoprime.
example : IsDicksonPseudoprime ⟨4, -1, by decide⟩ 9 := by
  obtain ⟨-, -, -, h, -⟩ := frobenius_nine
  exact h

end MathlibExtTest.NumberTheory.Recurrences.LucasSequenceDivisibilityIsLucasFrobeniusPseudoprimeOfIsEulerLucasPseudoprime
