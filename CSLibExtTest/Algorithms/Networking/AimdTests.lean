/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tests for AIMD convergence to fairness (Chiu--Jain)
-/
module

public import CSLibExt.Algorithms.Networking.Aimd
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace Cslib.Algorithms.Networking.Aimd

example : fairness ![1, 2] = 9 / 10 := by
  unfold fairness
  norm_num [Fin.sum_univ_two]

example : fairness ![3, 3] = 1 := by
  unfold fairness
  norm_num [Fin.sum_univ_two]

example : aimdStep 1 (1 / 2) 10 ![1, 2] = ![2, 3] := by
  have htot : total (![1, 2] : Fin 2 → ℝ) = 3 := by unfold total; norm_num [Fin.sum_univ_two]
  have hcond : ¬ (10 : ℝ) < total (![1, 2] : Fin 2 → ℝ) := by rw [htot]; norm_num
  unfold aimdStep; simp [hcond]
  funext i
  fin_cases i <;> simp <;> norm_num

example : aimdStep 1 (1 / 2) 2 ![2, 4] = ![1, 2] := by
  have htot : total (![2, 4] : Fin 2 → ℝ) = 6 := by unfold total; norm_num [Fin.sum_univ_two]
  have hcond : (2 : ℝ) < total (![2, 4] : Fin 2 → ℝ) := by rw [htot]; norm_num
  unfold aimdStep; simp [hcond]
  funext i
  fin_cases i <;> simp; norm_num

example : aiadStep 1 (-1) 4 ![1, 2] = ![2, 3] := by
  have htot : total (![1, 2] : Fin 2 → ℝ) = 3 := by unfold total; norm_num [Fin.sum_univ_two]
  have hcond : ¬ (4 : ℝ) < total (![1, 2] : Fin 2 → ℝ) := by rw [htot]; norm_num
  unfold aiadStep; simp [hcond]
  funext i
  fin_cases i <;> simp <;> norm_num

example : total ![1, 2, 3] = 6 := by
  unfold total
  norm_num [Fin.sum_univ_three]

example : linearStep 1 1 0 (1 / 2) 2 ![2, 4] = ![1, 2] := by
  have htot : total (![2, 4] : Fin 2 → ℝ) = 6 := by unfold total; norm_num [Fin.sum_univ_two]
  have hcond : (2 : ℝ) < total (![2, 4] : Fin 2 → ℝ) := by rw [htot]; norm_num
  unfold linearStep; simp [hcond]
  funext i
  fin_cases i <;> simp; norm_num

end Cslib.Algorithms.Networking.Aimd
