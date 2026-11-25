/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.ClusterAlgebra.RankTwo
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.NormNum

/-!
# Tests for rank-two cluster algebras
-/

namespace MathlibExtTest.RingTheory.ClusterAlgebra.RankTwo

open MathlibExt.RingTheory.ClusterAlgebra

/-- The nonvanishing hypothesis is satisfiable: positive initial values. -/
example (k : ℕ) : rankTwoSeq 1 1 (1 : ℚ) 1 k ≠ 0 := (rankTwoSeq_pos 1 1 one_pos one_pos k).ne'

/-- Type `A₂` at `x = y = 1`: `1, 1, 2, 3, 2, 1, 1`. -/
example : rankTwoSeq 1 1 (1 : ℚ) 1 2 = 2 ∧ rankTwoSeq 1 1 (1 : ℚ) 1 3 = 3 ∧
    rankTwoSeq 1 1 (1 : ℚ) 1 4 = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [rankTwoSeq]

example (k : ℕ) : rankTwoSeq 1 1 (1 : ℚ) 1 (k + 5) = rankTwoSeq 1 1 (1 : ℚ) 1 k :=
  rankTwoSeq_one_one_periodic (fun j => (rankTwoSeq_pos 1 1 one_pos one_pos j).ne') k

example (k : ℕ) : rankTwoSeq 1 2 (2 : ℚ) 3 (k + 6) = rankTwoSeq 1 2 (2 : ℚ) 3 k :=
  rankTwoSeq_one_two_periodic (fun j => (rankTwoSeq_pos 1 2 (by norm_num) (by norm_num) j).ne') k

example (k : ℕ) : rankTwoSeq 1 3 (2 : ℚ) 5 (k + 8) = rankTwoSeq 1 3 (2 : ℚ) 5 k :=
  rankTwoSeq_one_three_periodic (fun j => (rankTwoSeq_pos 1 3 (by norm_num) (by norm_num) j).ne') k

/-- Type `G₂` is not 5- or 6-periodic: at `x = y = 1` the terms are `1, 1, 2, 3, 14, 5, 9, 2`. -/
example : rankTwoSeq 1 3 (1 : ℚ) 1 4 = 14 ∧ rankTwoSeq 1 3 (1 : ℚ) 1 5 = 5 ∧
    rankTwoSeq 1 3 (1 : ℚ) 1 6 = 9 ∧ rankTwoSeq 1 3 (1 : ℚ) 1 7 = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [rankTwoSeq]

/-- The affine type `A(1, 4)` at `x = y = 1` starts `2, 3, 41, 14` (Fomin, Williams and
Zelevinsky, arXiv:1608.05735v5, Example 3.2.10). -/
example : rankTwoSeq 1 4 (1 : ℚ) 1 2 = 2 ∧ rankTwoSeq 1 4 (1 : ℚ) 1 3 = 3 ∧
    rankTwoSeq 1 4 (1 : ℚ) 1 4 = 41 ∧ rankTwoSeq 1 4 (1 : ℚ) 1 5 = 14 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [rankTwoSeq]

/-- Two rounds of alternating seed mutations of `A(1, 1)` from `(1, 1)` give the cluster
`(z 4, z 5) = (2, 1)`. -/
example : (mutateSeq ((List.replicate 2 [(0 : Fin 2), 1]).flatten)
    (![(1 : ℚ), 1], rankTwoMatrix 1 1)).1 0 = 2 := by
  rw [mutateSeq_rankTwoMatrix]
  norm_num [rankTwoSeq]

example : IsSkewSymmetrizable (rankTwoMatrix 1 4) :=
  isSkewSymmetrizable_rankTwoMatrix one_pos (by norm_num)

example : IsSkewSymmetrizable (matrixMutation 0 (rankTwoMatrix 2 3)) :=
  (isSkewSymmetrizable_rankTwoMatrix (by norm_num) (by norm_num)).matrixMutation 0

end MathlibExtTest.RingTheory.ClusterAlgebra.RankTwo
