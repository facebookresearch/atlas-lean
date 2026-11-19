/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.FidelityDataProcessing
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for data processing of the classical fidelity

* Concrete evaluations: the point masses `![1, 0]` and `![0, 1]` on `Fin 2` have Bhattacharyya
  coefficient `0`, and the many-to-one map `mergeMap`, which sends both inputs to the single
  output, sends each of them to the point mass `![1]`, so their coefficient becomes `1`.
* Merging therefore strictly increases the coefficient, and
  `bhattacharyyaCoeff_le_bhattacharyyaCoeff_vecMul` applies to `mergeMap`.
-/

@[expose] public section

namespace MathlibExtTest.Quantum.FidelityDataProcessing

open MathlibExt.Quantum.ClassicalFuchsVanDeGraaf MathlibExt.Quantum.FidelityDataProcessing
open Matrix

/-- The stochastic map from `Fin 2` to `Fin 1` that merges both inputs into the single
output. -/
def mergeMap : Matrix (Fin 2) (Fin 1) ℝ := fun _ _ => 1

/-- Each row of `mergeMap` sums to `1`. -/
theorem mergeMap_row_sum (i : Fin 2) : ∑ j, mergeMap i j = 1 := by
  simp [mergeMap]

/-- Point masses with disjoint supports have Bhattacharyya coefficient `0`. -/
theorem bhattacharyyaCoeff_disjoint_pointMasses :
    bhattacharyyaCoeff ![(1 : ℝ), 0] ![0, 1] = 0 := by
  simp [bhattacharyyaCoeff, Fin.sum_univ_two]

/-- Merging sends the point mass on input `0` to the point mass on the output. -/
theorem vecMul_mergeMap_left : ![(1 : ℝ), 0] ᵥ* mergeMap = ![1] := by
  ext j
  fin_cases j
  simp [mergeMap, vecMul_apply_eq_sum, Fin.sum_univ_two]

/-- Merging sends the point mass on input `1` to the point mass on the output. -/
theorem vecMul_mergeMap_right : ![(0 : ℝ), 1] ᵥ* mergeMap = ![1] := by
  ext j
  fin_cases j
  simp [mergeMap, vecMul_apply_eq_sum, Fin.sum_univ_two]

/-- After merging, both vectors are the same point mass: coefficient `1`. -/
theorem bhattacharyyaCoeff_vecMul_mergeMap :
    bhattacharyyaCoeff (![(1 : ℝ), 0] ᵥ* mergeMap) (![0, 1] ᵥ* mergeMap) = 1 := by
  rw [vecMul_mergeMap_left, vecMul_mergeMap_right]
  simp [bhattacharyyaCoeff]

/-- Merging strictly increases the coefficient, from `0` to `1`. -/
example : bhattacharyyaCoeff ![(1 : ℝ), 0] ![0, 1] <
    bhattacharyyaCoeff (![(1 : ℝ), 0] ᵥ* mergeMap) (![0, 1] ᵥ* mergeMap) := by
  rw [bhattacharyyaCoeff_disjoint_pointMasses, bhattacharyyaCoeff_vecMul_mergeMap]
  norm_num

/-- The data-processing inequality applies to the many-to-one map `mergeMap`. -/
example : bhattacharyyaCoeff ![(1 : ℝ), 0] ![0, 1] ≤
    bhattacharyyaCoeff (![(1 : ℝ), 0] ᵥ* mergeMap) (![0, 1] ᵥ* mergeMap) :=
  bhattacharyyaCoeff_le_bhattacharyyaCoeff_vecMul mergeMap (fun _ _ => zero_le_one)
    mergeMap_row_sum _ _ (by simp [Fin.forall_fin_two]) (by simp [Fin.forall_fin_two])

end MathlibExtTest.Quantum.FidelityDataProcessing

end
