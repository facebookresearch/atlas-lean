/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.MontgomeryTaylorWindow
import MathlibExt.NumberTheory.LSeries.ZeroCounts
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Tactic.NormNum

namespace ComplexZeroCounts

example (f : ℂ → ℂ) (S : Set ℂ) (a : ℝ) : windowZeros f S a a = ∅ := by
  ext z
  simp only [windowZeros, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
  exact ⟨fun h => (not_lt_of_ge h.2.2.2) h.2.2.1, False.elim⟩

example : (3 + Complex.I : ℂ) ∈ windowZeros (fun _ => 0) Set.univ 0 1 := by
  norm_num [windowZeros, Complex.add_im]

example : (3 + Complex.I : ℂ) ∉ windowZeros (fun _ => 0) openCriticalStrip 0 1 := by
  norm_num [windowZeros, openCriticalStrip, Complex.add_re]

example : countWithMultiplicity (fun z : ℂ => z ^ 2) ({0} : Set ℂ) = 2 := by
  rw [countWithMultiplicity, finsum_mem_singleton]
  have h : AnalyticAt ℂ (id : ℂ → ℂ) 0 := analyticAt_id
  change (analyticOrderAt ((id : ℂ → ℂ) ^ 2) 0).toNat = 2
  rw [analyticOrderAt_pow h]
  simp

example (f : ℂ → ℂ) (z : ℂ) (h : ¬ AnalyticAt ℂ f z) :
    countWithMultiplicity f {z} = 0 := by
  rw [countWithMultiplicity, finsum_mem_singleton, analyticOrderAt_of_not_analyticAt h]
  rfl

example : countSimpleOnLine (fun z : ℂ => z - 1 / 2) ({1 / 2} : Set ℂ) = 1 := by
  have hline : (1 / 2 : ℂ) ∈ {z : ℂ | z.re = 1 / 2} := by
    norm_num [Complex.div_re]
  unfold countSimpleOnLine
  rw [Set.singleton_inter_of_mem hline, Set.singleton_inter_of_mem]
  · exact Set.ncard_singleton _
  · simp

example : countSimpleOnLine (fun z : ℂ => (z - 1 / 2) ^ 2) ({1 / 2} : Set ℂ) = 0 := by
  have hline : (1 / 2 : ℂ) ∈ {z : ℂ | z.re = 1 / 2} := by
    norm_num [Complex.div_re]
  unfold countSimpleOnLine
  rw [Set.singleton_inter_of_mem hline, Set.singleton_inter_of_notMem]
  · exact Set.ncard_empty ℂ
  · change (analyticOrderAt ((· - (1 / 2 : ℂ)) ^ (2 : ℕ)) (1 / 2)).toNat ≠ 1
    rw [analyticOrderAt_centeredMonomial]
    decide

example : 0 < montgomeryTaylorWindowConstant ∧
    montgomeryTaylorWindowConstant⁻¹ = 1 / 2 + 1 / Real.sqrt 2 * Real.cot (1 / Real.sqrt 2) := by
  set r := Real.sqrt 2
  set x : ℝ := 1 / r
  have hr : 0 < r := Real.sqrt_pos.2 (by norm_num)
  have hr_sq : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr_one : 1 < r := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hx : 0 < x := one_div_pos.mpr hr
  have hx_one : x < 1 := by
    simpa [x] using one_div_lt_one_div_of_lt zero_lt_one hr_one
  have hx_pi : x < Real.pi / 2 := hx_one.trans_le Real.one_le_pi_div_two
  have ht := Real.tan_pos_of_pos_of_lt_pi_div_two hx hx_pi
  have hcot : Real.cot x = (Real.tan x)⁻¹ := by
    rw [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, inv_div]
  have hhalf : x / r = 1 / 2 := by
    dsimp only [x]
    rw [div_div, ← pow_two, hr_sq]
  change 0 < r * Real.tan x / (1 + x * Real.tan x) ∧
    (r * Real.tan x / (1 + x * Real.tan x))⁻¹ = 1 / 2 + x * Real.cot x
  refine ⟨div_pos (mul_pos hr ht) (add_pos zero_lt_one (mul_pos hx ht)), ?_⟩
  have hcancel : x * Real.tan x / (r * Real.tan x) = x / r :=
    mul_div_mul_right _ _ ht.ne'
  have hrecip : 1 / (r * Real.tan x) = x * (Real.tan x)⁻¹ := by
    simp [x, one_div, mul_inv_rev, mul_comm]
  rw [inv_div, add_div, hcancel, hrecip, hhalf, hcot, add_comm]

end ComplexZeroCounts
