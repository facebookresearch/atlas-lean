/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.BooleanFunctions.KKL.KKLPBiasedInequality
import CSLibExtTest.Complexity.BooleanFunctions.KKL.KKLInequality

/-!
# Tests for KKL on biased Boolean cubes

At bias `1/3`, the two-bit AND function gives an inequality with a positive logarithmic
factor. A constant Boolean function tests the zero-influence case at every interior bias.
-/

namespace StatMechTest.BooleanFunctions.KKLPBiasedInequality

open MathlibExt.Complexity.BooleanFunctions.KKLPBiasedWanted
open StatMech StatMech.OSSS StatMech.Probability

example : ∃ c : ℝ, 0 < c ∧ 0 < c * (8 / 81) * Real.log 3 ∧
    c * (8 / 81) * Real.log 3 ≤ 2 / 3 := by
  obtain ⟨c, hc, hKKL⟩ := kkl_pbiased (1 / 3) (by norm_num) (by norm_num)
  have hvar : var (bernoulliWeight (1 / 3)) andInd = 8 / 81 := by
    norm_num [var, cov, expect, weight, sum_configSpace_bool, andFun, bernoulliWeight]
  have hinfl (e : Bool) : infl (bernoulliWeight (1 / 3)) andInd e = 1 / 3 := by
    cases e <;>
      norm_num [infl, expect, weight, sum_configSpace_bool, andInd, andFun, bernoulliWeight,
        setOpen, setClosed]
  have hmax : maxInfl (bernoulliWeight (1 / 3)) andInd = 1 / 3 := by
    unfold maxInfl
    simp only [show infl (bernoulliWeight (1 / 3)) andInd = (fun _ => 1 / 3) from funext hinfl,
      Finset.sup'_const]
  have htotal : totalInfl (bernoulliWeight (1 / 3)) andInd = 2 / 3 := by
    rw [totalInfl, Fintype.sum_bool, hinfl, hinfl]
    norm_num
  have h := kkl_inequality_total hKKL andFun
  change c * var (bernoulliWeight (1 / 3)) andInd *
    Real.log (1 / maxInfl (bernoulliWeight (1 / 3)) andInd) ≤
    totalInfl (bernoulliWeight (1 / 3)) andInd at h
  rw [hvar, hmax, htotal, show (1 : ℝ) / (1 / 3) = 3 by norm_num] at h
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  exact ⟨c, hc, by positivity, h⟩

example (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ c : ℝ, 0 < c ∧ c * var (bernoulliWeight p) (fun _ : ConfigSpace Bool => 1) *
      Real.log (1 / maxInfl (bernoulliWeight p) (fun _ : ConfigSpace Bool => 1)) ≤ 0 := by
  obtain ⟨c, hc, hKKL⟩ := kkl_pbiased p hp0 hp1
  refine ⟨c, hc, ?_⟩
  have h := kkl_inequality_total hKKL (fun _ : ConfigSpace Bool => true)
  simpa [totalInfl, infl, expect] using h

end StatMechTest.BooleanFunctions.KKLPBiasedInequality
