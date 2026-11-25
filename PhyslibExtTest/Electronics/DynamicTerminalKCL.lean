/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electronics.DynamicTerminalKCL
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

open PhyslibExt.Electronics.DynamicTerminalKCL

namespace PhyslibExtTest.Electronics.DynamicTerminalKCL

/-- Terminal `0` of the capacitor driven by `s ↦ (s, 0)` carries displacement current `1`. -/
example : displacementCurrent 2 (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 1 - w 0])
    (fun s : ℝ => ![s, 0]) 4 0 = 1 :=
  displacementCurrent_capacitor_zero 4

/-- Terminal `1` carries displacement current `-1`. -/
example : displacementCurrent 2 (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 1 - w 0])
    (fun s : ℝ => ![s, 0]) 4 1 = -1 :=
  displacementCurrent_capacitor_one 4

/-- With a conductance `2` in parallel, the dynamic current into terminal `0` at time `3`
is `2 * (3 - 0) + 1 = 7`. -/
example : dynamicTerminalCurrent 2 (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 1 - w 0])
    (fun w : Fin 2 → ℝ => ![2 * (w 0 - w 1), 2 * (w 1 - w 0)])
    (fun s : ℝ => ![s, 0]) 3 0 = 7 := by
  rw [dynamicTerminalCurrent, displacementCurrent_capacitor_zero]
  norm_num

/-- The same parallel conductance-capacitor pair satisfies the dynamic KCL at time `3`,
through the general law on the whole voltage space. -/
example : ∑ i, dynamicTerminalCurrent 2 (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 1 - w 0])
    (fun w : Fin 2 → ℝ => ![2 * (w 0 - w 1), 2 * (w 1 - w 0)])
    (fun s : ℝ => ![s, 0]) 3 i = 0 := by
  refine sum_dynamicTerminalCurrent_eq_zero 2 Set.univ isOpen_univ _ ?_ ?_ _ ?_ _ ?_
    (fun _ => Set.mem_univ _) 3
  · intro i
    fin_cases i
    · exact ((differentiable_apply 0).sub (differentiable_apply 1)).differentiableOn
    · exact ((differentiable_apply 1).sub (differentiable_apply 0)).differentiableOn
  · intro w _
    simp [Fin.sum_univ_two]
  · intro w _
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  · refine differentiable_pi.mpr fun i => ?_
    fin_cases i
    · exact differentiable_id
    · exact differentiable_const 0

/-- Displacement currents alone sum to zero along the trajectory `s ↦ (s, 0)`. -/
example : ∑ i, displacementCurrent 2 (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 1 - w 0])
    (fun s : ℝ => ![s, 0]) 5 i = 0 := by
  rw [Fin.sum_univ_two, displacementCurrent_capacitor_zero, displacementCurrent_capacitor_one]
  norm_num

/-- A static current leaking `1` from each terminal leaves a summed dynamic current of `2`. -/
example : ∑ i, dynamicTerminalCurrent 2 (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 1 - w 0])
    (fun _ => ![1, 1]) (fun s : ℝ => ![s, 0]) 3 i = 2 := by
  rw [Fin.sum_univ_two, dynamicTerminalCurrent, dynamicTerminalCurrent,
    displacementCurrent_capacitor_zero, displacementCurrent_capacitor_one]
  norm_num

/-- The pairwise example is nonvacuous at every time. -/
example : displacementCurrent 2 (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 1 - w 0])
    (fun s : ℝ => ![s, (0 : ℝ)]) 2 0 ≠ 0 :=
  (sum_dynamic_pairwise_example 2).2

end PhyslibExtTest.Electronics.DynamicTerminalKCL
