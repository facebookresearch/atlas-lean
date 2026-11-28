/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TothOddZeta

namespace MathlibExtTest.NumberTheory.TothOddZeta

open MetaMathlibExt MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry10bEuleriansymmetry
open MathlibExt.Combinatorics.ReducedComplexitiesWanted (paperfoldingSeq)

private lemma euler_one : chapter5EulerEven 1 = -1 := by
  rw [chapter5EulerEven_step 1 (by decide)]
  simp [chapter5EulerEven_zero]

private lemma euler_two : chapter5EulerEven 2 = 5 := by
  rw [chapter5EulerEven_step 2 (by decide)]
  norm_num [Fin.sum_univ_two, chapter5EulerEven_zero, euler_one, Nat.choose]

example : HurwitzZeta.hurwitzZeta ((3 / 4 : ℝ) : UnitAddCircle) 3 =
    28 * riemannZeta 3 - (Real.pi : ℂ) ^ 3 := by
  have h := hurwitzZeta_three_quarters_two_mul_add_one 1 (by decide)
  norm_num [euler_one, Nat.factorial] at h
  linear_combination h

example : HurwitzZeta.hurwitzZeta ((3 / 4 : ℝ) : UnitAddCircle) 5 =
    496 * riemannZeta 5 - 5 / 3 * (Real.pi : ℂ) ^ 5 := by
  have h := hurwitzZeta_three_quarters_two_mul_add_one 2 (by decide)
  norm_num [euler_two, Nat.factorial] at h
  linear_combination h

-- The signs on denominators 1, 2 and 3 also check the shift from zero-based indices.
example : paperfoldingSeq 0 = false ∧ paperfoldingSeq 1 = false ∧ paperfoldingSeq 2 = true := by
  norm_num [paperfoldingSeq, Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3)]

example : (∑' n : ℕ, (-1 : ℝ) ^ (paperfoldingSeq n).toNat / ((n : ℝ) + 1) ^ 3) =
    Real.pi ^ 3 / 28 := by
  have h := tsum_neg_one_pow_paperfolding 1 (by decide)
  norm_num [euler_one, Nat.factorial] at h
  exact h

example : (∑' n : ℕ, (-1 : ℝ) ^ (paperfoldingSeq n).toNat / ((n : ℝ) + 1) ^ 5) =
    Real.pi ^ 5 * 5 / 1488 := by
  have h := tsum_neg_one_pow_paperfolding 2 (by decide)
  norm_num [euler_two, Nat.factorial] at h
  exact h

end MathlibExtTest.NumberTheory.TothOddZeta
