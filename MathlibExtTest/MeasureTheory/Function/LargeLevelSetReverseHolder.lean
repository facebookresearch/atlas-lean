/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Function.LargeLevelSetReverseHolder
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open Filter MeasureTheory Set
open MathlibExt.MeasureTheory.LargeLevelSetReverseHolderWanted
open scoped ENNReal Topology

-- The first function vanishes, but the sequence of L¹ norms still tends to infinity.
example : ∃ y : ℕ → ℝ, Tendsto y atTop atTop ∧
    0 < sInf (range fun n : ℕ => μIcc01 {_x : ℝ | |(n : ℝ)| ≥ y n}) := by
  have hmass : μIcc01 univ = 1 := by
    rw [μIcc01, Measure.restrict_apply_univ, Real.volume_Icc]
    norm_num
  let : IsProbabilityMeasure μIcc01 := ⟨hmass⟩
  have hμ : μIcc01 ≠ 0 := by
    intro hz
    simp [hz] at hmass
  have hnorm (n : ℕ) {p : ℝ≥0∞} (hp : p ≠ 0) :
      eLpNorm (fun _ : ℝ => (n : ℝ)) p μIcc01 = n := by
    rw [eLpNorm_const _ hp hμ, hmass, ENNReal.one_rpow, mul_one, ← ofReal_norm,
      Real.norm_eq_abs, abs_of_nonneg (by positivity), ENNReal.ofReal_natCast]
  apply exists_tendsto_atTop_inf_measure_levelSet_pos (fun n _ => (n : ℝ))
  · intro n
    exact memLp_const (n : ℝ)
  · intro n
    rw [hnorm n (by norm_num : (2 : ℝ≥0∞) ≠ 0), hnorm n one_ne_zero]
    calc
      (n : ℝ≥0∞) = 1 * (n : ℝ≥0∞) := (one_mul _).symm
      _ ≤ _ := mul_le_mul' (by norm_num) le_rfl
  · simp only [hnorm _ one_ne_zero]
    refine ENNReal.tendsto_nhds_top fun k => (eventually_ge_atTop (k + 1)).mono fun n hn => ?_
    exact_mod_cast (Nat.lt_of_succ_le hn)
