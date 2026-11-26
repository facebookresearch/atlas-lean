/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TothOddZetaTsumPaperfoldingTwoMulAddOne

namespace MathlibExtTest.NumberTheory.TothOddZetaTsumPaperfoldingTwoMulAddOne

open MetaMathlibExt MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry10bEuleriansymmetry
open MathlibExt.Combinatorics.ReducedComplexitiesWanted (paperfoldingSeq)

private lemma euler_one : chapter5EulerEven 1 = -1 := by
  rw [chapter5EulerEven_step 1 (by decide)]
  simp [chapter5EulerEven_zero]

example : (28 : ℝ) *
    ∑' n : ℕ, (2 * ((paperfoldingSeq n).toNat : ℝ) - 1) / ((n + 1 : ℕ) : ℝ) ^ 3 =
    -(Real.pi ^ 3) := by
  have h := tsum_paperfolding_two_mul_add_one 1 (by decide)
  norm_num [euler_one, Nat.factorial] at h ⊢
  linear_combination h

example : (496 : ℝ) *
    ∑' n : ℕ, (2 * ((paperfoldingSeq n).toNat : ℝ) - 1) / ((n + 1 : ℕ) : ℝ) ^ 5 =
    -(5 / 3 * Real.pi ^ 5) := by
  have hE : chapter5EulerEven 2 = 5 := by
    rw [chapter5EulerEven_step 2 (by decide)]
    norm_num [Fin.sum_univ_two, chapter5EulerEven_zero, euler_one, Nat.choose]
  have h := tsum_paperfolding_two_mul_add_one 2 (by decide)
  norm_num [hE, Nat.factorial] at h ⊢
  linear_combination h

end MathlibExtTest.NumberTheory.TothOddZetaTsumPaperfoldingTwoMulAddOne
