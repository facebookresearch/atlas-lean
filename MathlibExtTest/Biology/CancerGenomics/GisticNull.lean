/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.CancerGenomics.GisticNull
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-! Tests for the GISTIC permutation null: the empty cohort, a two-sample instance of the
convolution step, the marker independence of the null, and a GeneGISTIC window minimum. -/

namespace MathlibExtTest.Biology.CancerGenomics.GisticNull

open MathlibExt.Biology.CancerGenomics.GisticNull

/-- With no samples the score is `0` with probability one. -/
example (x : Fin 0 → Fin 3 → ℝ) : permutationNull x 1 0 = 1 := by
  rw [permutationNull_zero]; simp

/-- Two samples on three markers: adding the second sample convolves with its empirical law. -/
example (x : Fin 2 → Fin 3 → ℝ) (g : ℝ) :
    permutationNull x 0 g = ∑ v : Fin 3, (1 / (3 : ℝ)) *
      permutationNull (fun j => x j.castSucc) 0 (g - x (Fin.last 1) v) :=
  permutationNull_succ x 0 g

/-- The null does not depend on the marker. -/
example (x : Fin 2 → Fin 3 → ℝ) (g : ℝ) : permutationNull x 0 g = permutationNull x 2 g := by
  rw [permutationNull_eq_count, permutationNull_eq_count]

/-- A gene of two markers on a genome of three: the window minima of `(3, 1, 2)` are `1, 1`. -/
example : windowMin (W := 2) (n := 1) ![3, 1, 2] 0 = 1 := by
  apply le_antisymm
  · exact (Finset.inf'_le _ (Finset.mem_univ (1 : Fin 2))).trans_eq (by simp)
  · exact Finset.le_inf' _ _ fun k _ => by fin_cases k <;> simp

end MathlibExtTest.Biology.CancerGenomics.GisticNull
