/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Numerical.PeriodicYeeResidual
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section

open MathlibExt.Analysis.Numerical.PeriodicLeapfrogStencil
open MathlibExt.Analysis.Numerical.PeriodicYeeEnergy
open MathlibExt.Analysis.Numerical.PeriodicYeeResidual

namespace MathlibExtTest.Analysis.Numerical.PeriodicYeeResidual

/-- Squared weighted norm of a nonconstant three-cell vector at weight `1 / 2`. -/
example : weightedNormSq (1 / 2) ![1, 2, 4] = 21 / 2 := by
  unfold weightedNormSq weightedInner
  simp only [Fin.sum_univ_three]
  norm_num

/-- The weighted norm of `![3, 4]` at unit weight is `5`. -/
example : weightedNorm 1 ![3, 4] = 5 := by
  unfold weightedNorm weightedNormSq weightedInner
  simp only [Fin.sum_univ_two]
  norm_num
  rw [show (25 : ℝ) = 5 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- The bound at `L = 4, dt = 1, c = 1, Mt = 3, Mx = 5, h = 2` is `23 / 12`. -/
example : consistencyEta 4 1 1 3 5 2 = 23 / 12 := by
  unfold consistencyEta
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- The zero pair is an admissible solution with zero derivative bounds. -/
private theorem zero_isSmoothPeriodicSolution (L c : ℝ) :
    isSmoothPeriodicSolution L c 0 0 (fun _ _ => 0) (fun _ _ => 0) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩ <;> intros <;>
    simp [contDiff_const]

/-- Zero solution on `N = 3`, `h = 1 / 2`: the `u` residual bound forces norm `0`. -/
example (n : ℕ) :
    weightedNorm (1 / 2)
      (uUpdateResidual (N := 3) (fun _ _ => 0) (fun _ _ => 0) (1 / 2) 2 (1 / 4) n) ≤ 0 := by
  have h := uUpdateResidual_weightedNorm_le (N := 3) (by norm_num) (1 / 2) (1 / 4) 2 (3 / 2)
    0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl le_rfl _ _
    (zero_isSmoothPeriodicSolution _ _) n
  simpa [consistencyEta] using h

/-- Zero solution on `N = 5`, `h = 1`: the `v` residual bound forces norm `0`. -/
example (n : ℕ) :
    weightedNorm 1
      (vUpdateResidual (N := 5) (fun _ _ => 0) (fun _ _ => 0) 1 3 (1 / 2) n) ≤ 0 := by
  have h := vUpdateResidual_weightedNorm_le (N := 5) (by norm_num) 1 (1 / 2) 3 5
    0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl le_rfl _ _
    (zero_isSmoothPeriodicSolution _ _) n
  simpa [consistencyEta] using h

/-- Travelling sine at `c = 2` on `N = 4`, `h = π / 2`, `dt = 1 / 10`: both residual
norms are at most `1 / 10`. -/
example (n : ℕ) :
    weightedNorm (Real.pi / 2)
        (uUpdateResidual (N := 4) (travellingSineU 2) (travellingSineV 2)
          (Real.pi / 2) 2 (1 / 10) n) ≤ 1 / 10 ∧
      weightedNorm (Real.pi / 2)
        (vUpdateResidual (N := 4) (travellingSineU 2) (travellingSineV 2)
          (Real.pi / 2) 2 (1 / 10) n) ≤ 1 / 10 := by
  have hL : 2 * Real.pi = ((4 : ℕ) : ℝ) * (Real.pi / 2) := by push_cast; ring
  obtain ⟨hu, hv⟩ := travellingSine_staggeredResiduals_bounded (N := 4) (by norm_num)
    (Real.pi / 2) (1 / 10) 2 (by positivity) (by norm_num) (by norm_num) hL n
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hs : Real.sqrt (2 * Real.pi) ≤ 3 :=
    calc Real.sqrt (2 * Real.pi) ≤ Real.sqrt (3 ^ 2) := Real.sqrt_le_sqrt (by linarith)
      _ = 3 := Real.sqrt_sq (by norm_num)
  have hA : (2 : ℝ) ^ 3 * (1 / 10) ^ 2 + 2 * 1 * (Real.pi / 2) ^ 2 ≤ 6 := by nlinarith
  have hA0 : 0 ≤ (2 : ℝ) ^ 3 * (1 / 10) ^ 2 + 2 * 1 * (Real.pi / 2) ^ 2 := by positivity
  have hprod := mul_le_mul hs hA hA0 (by norm_num)
  have heta : consistencyEta (2 * Real.pi) (1 / 10) 2 (2 ^ 3) 1 (Real.pi / 2) ≤ 1 / 10 := by
    unfold consistencyEta
    nlinarith [hprod]
  exact ⟨hu.trans heta, hv.trans heta⟩

end MathlibExtTest.Analysis.Numerical.PeriodicYeeResidual
