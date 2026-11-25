/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.ScaledBuckAveraging
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

open MathlibExt.Analysis.ODE.PWMPrimitiveBound PhyslibExt.Circuits.ScaledBuckAveraging
open Matrix
open scoped NNReal

namespace PhyslibExtTest.Circuits.ScaledBuckAveraging

/-! Fixture: `L = C = R = Iref = Vref = 1`, `Vin = 2`, switching-cycle length
`ε = 1/10`, horizon `T = 1`, duty `1`. -/

/-- At duty one the state `(i, v) = (2, 2)` is an equilibrium of the
two-state laws: both right-hand sides vanish. -/
example : buckMatrix 1 1 1 *ᵥ ![2, 2] + (1 : ℝ) • buckInput 1 2 = 0 := by
  rw [buckMatrix_mulVec_add_smul_buckInput]
  ext j
  fin_cases j <;> norm_num

/-- The duty-one equilibrium meets every hypothesis of the headline
bound (switched and averaged states both constant `2`), and the bound
then holds at every `t ∈ [0, 1]`. -/
example (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |(2 : ℝ) - 2| ≤ 1 * scaledBuckErrorBound 1 1 1 2 1 1 1 (1 / 10) 0 (2 - 2) (2 - 2) ∧
      |(2 : ℝ) - 2| ≤ 1 * scaledBuckErrorBound 1 1 1 2 1 1 1 (1 / 10) 0 (2 - 2) (2 - 2) := by
  have hs : ∀ u : ℝ, pwmSignal (1 / 10) (fun _ => 1) u = 1 := fun u =>
    pwmSignal_one _ u (by norm_num)
  have h := buck_switched_averaged_error_le 1 1 1 2 1 1 one_pos one_pos one_pos one_pos one_pos
    1 (1 / 10) 0 (fun _ => 1) zero_le_one (by norm_num) (fun _ _ => ⟨zero_le_one, le_rfl⟩)
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith (fun _ => 2) (fun _ => 2) (fun _ => 2)
    (fun _ => 2) 2 2 2 2 continuousOn_const continuousOn_const continuousOn_const
    continuousOn_const (fun _ _ => by simp only [hs]; simp) (fun _ _ => by simp)
    (fun _ _ => by norm_num) (fun _ _ => by simp) t ht
  simpa using h

/-- At the fixture the error bound is `exp 2 / 5`: zero initial
mismatch, ripple `|Vin| / (L Iref) * ε = 1/5`, growth rate `2`. -/
example : scaledBuckErrorBound 1 1 1 2 1 1 1 (1 / 10) 0 0 0 = Real.exp 2 / 5 := by
  norm_num [scaledBuckErrorBound, scaledBuckGrowthRate]
  ring

/-- At the endpoint duty `D = 0` the sharp constant-duty bound has no
switching contribution: any switched and averaged trajectories with
the same initial state coincide on `[0, 1]`. -/
example (i v iAvg vAvg : ℝ → ℝ) (i₀ v₀ : ℝ)
    (hi_cont : ContinuousOn i (Set.Icc 0 1)) (hv_cont : ContinuousOn v (Set.Icc 0 1))
    (hiAvg_cont : ContinuousOn iAvg (Set.Icc 0 1))
    (hvAvg_cont : ContinuousOn vAvg (Set.Icc 0 1))
    (hi : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      i t = i₀ + ∫ u in (0 : ℝ)..t, (pwmSignal (1 / 10) (fun _ => 0) u * 2 - v u) / 1)
    (hv : ∀ t ∈ Set.Icc (0 : ℝ) 1, v t = v₀ + ∫ u in (0 : ℝ)..t, (i u - v u / 1) / 1)
    (hiAvg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      iAvg t = i₀ + ∫ u in (0 : ℝ)..t, (0 * 2 - vAvg u) / 1)
    (hvAvg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      vAvg t = v₀ + ∫ u in (0 : ℝ)..t, (iAvg u - vAvg u / 1) / 1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    i t = iAvg t ∧ v t = vAvg t := by
  have h := buck_switched_averaged_error_le_of_constDuty 1 1 1 2 1 1 one_pos one_pos one_pos
    one_pos one_pos 1 (1 / 10) 0 zero_le_one (by norm_num) ⟨le_rfl, zero_le_one⟩
    i v iAvg vAvg i₀ v₀ i₀ v₀ hi_cont hv_cont hiAvg_cont hvAvg_cont hi hv hiAvg hvAvg t ht
  simp only [sub_self, abs_zero, zero_div, max_self, zero_mul, mul_zero, zero_add,
    abs_nonpos_iff, sub_eq_zero] at h
  exact h

/-- At unit parameters the sup-norm operator norm of the scaled buck
matrix equals the growth rate `κ = 2`: `‖Ã‖ ≤ κ` from the module and
`2 ≤ ‖Ã‖` from the vector `(1, -1)`. -/
example : ‖scaledBuckOperator 1 1 1 1 1‖ = 2 := by
  have hκ : scaledBuckGrowthRate 1 1 1 1 1 = 2 := by norm_num [scaledBuckGrowthRate]
  refine le_antisymm (hκ ▸ norm_scaledBuckOperator_le 1 1 1 1 1 one_pos one_pos one_pos
    one_pos one_pos) ?_
  set x : Fin 2 → ℝ := ![1, -1]
  have hx : ‖x‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun j => ?_
    fin_cases j <;> simp [x]
  have happly : scaledBuckOperator 1 1 1 1 1 x = ![1, 2] := by
    rw [scaledBuckOperator_apply]
    ext j
    fin_cases j <;>
      norm_num [scaledBuckMatrix, x, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h2 : (2 : ℝ) ≤ ‖scaledBuckOperator 1 1 1 1 1 x‖ := by
    rw [happly]
    simpa using norm_le_pi_norm (![1, 2] : Fin 2 → ℝ) 1
  calc (2 : ℝ) ≤ ‖scaledBuckOperator 1 1 1 1 1 x‖ := h2
    _ ≤ ‖scaledBuckOperator 1 1 1 1 1‖ * ‖x‖ := (scaledBuckOperator 1 1 1 1 1).le_opNorm x
    _ ≤ ‖scaledBuckOperator 1 1 1 1 1‖ := by
        simpa using mul_le_mul_of_nonneg_left hx (norm_nonneg (scaledBuckOperator 1 1 1 1 1))

end PhyslibExtTest.Circuits.ScaledBuckAveraging
