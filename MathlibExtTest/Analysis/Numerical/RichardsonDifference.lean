/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MathlibExt.Analysis.Numerical.RichardsonDifference

open MetaMathlibExt Set

-- The cubic term cancels in one step, preserving the nonzero linear term.
example (h : ℝ) (hh : h ≠ 0) : richardsonDifference (fun y ↦ y + y ^ 3) 0 h = 1 := by
  rw [richardsonDifference_eq_fourPoint, div_eq_iff (mul_ne_zero (by norm_num) hh)]
  ring

-- The quintic error survives the first extrapolation with coefficient −4.
example (h : ℝ) (hh : h ≠ 0) :
    richardsonDifference (fun y ↦ 2 * y + y ^ 3 + y ^ 5) 0 h = 2 - 4 * h ^ 4 := by
  unfold richardsonDifference centeredDifference
  simp only [zero_add, zero_sub]
  field_simp
  ring

-- The second extrapolation cancels the quintic term as well as the cubic term.
example (h : ℝ) (hh : h ≠ 0) :
    (16 * richardsonDifference (fun y ↦ 2 * y + y ^ 3 + y ^ 5) 0 h -
      richardsonDifference (fun y ↦ 2 * y + y ^ 3 + y ^ 5) 0 (2 * h)) / 15 = 2 := by
  simp only [richardsonDifference_eq_fourPoint, zero_add, zero_sub]
  field_simp
  ring

-- For the seventh power the centered quotient is h^6, so S(h) is −20 h^6 and the
-- twice-extrapolated value is 64 h^6. At h = h₀/2 = 1 the error is exactly 64.
private theorem seventhPower_endpoint_error :
    |deriv (fun y : ℝ ↦ y ^ 7) 0 -
      (16 * richardsonDifference (fun y ↦ y ^ 7) 0 1 -
        richardsonDifference (fun y ↦ y ^ 7) 0 2) / 15| = 64 := by
  norm_num [deriv_pow_field, richardsonDifference, centeredDifference]

-- Both outermost samples are available exactly up to the upper step endpoint.
example {x h₀ h : ℝ} (hh : 0 < h) :
    (x - 4 * h ∈ Icc (x - 2 * h₀) (x + 2 * h₀) ∧
      x + 4 * h ∈ Icc (x - 2 * h₀) (x + 2 * h₀)) ↔ h ≤ h₀ / 2 := by
  simp only [mem_Icc]
  constructor
  · intro hp
    linarith [hp.2.2]
  · intro hp
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

-- The error theorem applies at equality, not just to strictly smaller steps.
example : ∃ C ≥ 64, ∀ h, 0 < h → h ≤ 1 →
    |deriv (fun y : ℝ ↦ y ^ 7) 0 -
      (16 * richardsonDifference (fun y ↦ y ^ 7) 0 h -
        richardsonDifference (fun y ↦ y ^ 7) 0 (2 * h)) / 15| ≤ C * h ^ 6 := by
  have hf : ContDiffOn ℝ 7 (fun y : ℝ ↦ y ^ 7) (Icc (0 - 2 * 2) (0 + 2 * 2)) :=
    (contDiff_id.pow 7).contDiffOn
  obtain ⟨C, _, h⟩ := exists_abs_deriv_sub_richardsonDifference_twice_le
    (x := 0) (h₀ := 2) (by norm_num) hf
  have hb := h 1 (by norm_num) (by norm_num)
  simp only [mul_one, one_pow, seventhPower_endpoint_error] at hb
  exact ⟨C, hb, fun t ht ht' ↦ h t ht (by linarith)⟩
