/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Boundary tests for the PageRank Google matrix: the one-node case, a
two-node case with a dangling column, and the teleport limit shape.
-/

module

public import CSLibExt.InformationRetrieval.PageRank

@[expose] public section

open scoped BigOperators
open Finset Matrix Cslib.InformationRetrieval.PageRank

namespace CSLibExtTest.InformationRetrieval.PageRank

/-- One node: the only stochastic matrix is `1`, the Google matrix is `1`,
and the unique stationary vector is `1`. -/
theorem pagerank_fin_one :
    googleMatrix (1 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => 1) (1 / 2 : ℝ) = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [googleMatrix]

/-- One node: `fun _ => 1` is a probability vector. -/
theorem probVec_fin_one : IsProbVec (fun _ : Fin 1 => (1 : ℝ)) := by
  constructor
  · intro i
    exact zero_le_one
  · simp

/-- Two nodes with a dangling second column: dangling replacement by the
uniform vector gives the column-stochastic matrix whose second column is
`(1/2, 1/2)`. Concretely, entry `(0, 1)` of the replaced matrix is `1 / 2`. -/
theorem dangling_entry :
    danglingReplace (Matrix.of fun i j : Fin 2 => if j = 0 ∧ i = 0 then 1 else 0)
        (fun _ => (1 : ℝ) / 2) 0 1 = 1 / 2 := by
  unfold danglingReplace
  simp only [Matrix.of_apply]
  simp

/-- The `ℓ¹` norm of a probability vector is `1`. -/
theorem l1Norm_of_probVec {S : Type*} [Fintype S] {x : S → ℝ}
    (hx : IsProbVec x) : l1Norm x = 1 := by
  unfold l1Norm
  have h : ∀ i, |x i| = x i := fun i => abs_of_nonneg (hx.1 i)
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  exact hx.2

/-- Non-vacuity of the contraction hypothesis shape: in the two-node
swap example the difference of the two basis probability vectors is
zero-sum with `ℓ¹` norm `2`. -/
theorem zeroSum_example :
    l1Norm ((fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)
      - (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0)) = 2 := by
  unfold l1Norm
  simp only [Pi.sub_apply]
  rw [Fin.sum_univ_two]
  norm_num

end CSLibExtTest.InformationRetrieval.PageRank
