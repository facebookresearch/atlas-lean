/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Function.LpCharacterizationPartitionAverages
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.NormNum

open MeasureTheory Set
open scoped BigOperators
open MathlibExt.MeasureTheory.LpCharacterizationPartitionAveragesWanted

-- All partitions see the same mass for the constant of magnitude two, even when their cells
-- have unequal lengths. In particular the square averages give a concrete bound for the converse.
private theorem negative_constant_sum {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : IsPartition01 t) :
    partitionAverageSum (fun _ => -2) 2 t = 4 := by
  have htel : ∑ i : Fin n, (t i.succ - t i.castSucc) = 1 := by
    have h := (Fin.sum_univ_succ t).symm.trans (Fin.sum_univ_castSucc t)
    rw [ht.1, ht.2.1, zero_add] at h
    rw [Finset.sum_sub_distrib, h, add_sub_cancel_left]
  unfold partitionAverageSum
  calc
    _ = ∑ i : Fin n, (t i.succ - t i.castSucc) * 4 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi : 0 < t i.succ - t i.castSucc := sub_pos.mpr (ht.2.2 Fin.castSucc_lt_succ)
      simp only [abs_neg, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)), setIntegral_const,
        Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal hi.le, smul_eq_mul]
      have havg : (1 / (t i.succ - t i.castSucc)) * ((t i.succ - t i.castSucc) * 2) = 2 := by
        rw [← mul_assoc, one_div, inv_mul_cancel₀ hi.ne', one_mul]
      rw [havg]
      norm_num
    _ = 4 := by rw [← Finset.sum_mul, htel, one_mul]

example : MemLp (fun _ : ℝ => (-2 : ℝ)) 2 (volume.restrict (Icc (0 : ℝ) 1)) := by
  let : IsFiniteMeasure ((volume : Measure ℝ).restrict (Icc 0 1)) :=
    isFiniteMeasure_restrict.2 isCompact_Icc.measure_lt_top.ne
  have h := (memLp_iff_bddAbove_partitionAverageSum (fun _ => (-2 : ℝ)) 2
    (by norm_num) (memLp_const (-2))).mpr ⟨4, fun _ _ ht => (negative_constant_sum ht).le⟩
  simpa using h
