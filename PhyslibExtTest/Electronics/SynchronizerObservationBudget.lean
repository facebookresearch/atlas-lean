/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electronics.SynchronizerObservationBudget
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PhyslibExt.Electronics.LogicObservationBands
open PhyslibExt.Electronics.SynchronizerObservationBudget

namespace PhyslibExtTest.Electronics.SynchronizerObservationBudget

/-- A mid-band voltage is invalid: `observe 1 2 (3 / 2) = none`. -/
example : observe 1 2 (3 / 2 : ℝ) = none :=
  invalidObservation_one_two_three_halves

example : invalidObservation 1 2 (3 / 2 : ℝ) :=
  invalidObservation_one_two_three_halves

/-- Valid-band voltages: a low voltage at `1 / 2` and a high voltage
at `3`, for thresholds `1` and `2`. -/
example : observe 1 2 (1 / 2 : ℝ) = some false :=
  observe_eq_false_of_le (by norm_num) _
example : observe 1 2 (3 : ℝ) = some true :=
  observe_eq_true_of_le (by norm_num) (by norm_num)

/-- Noise-shifted valid values: a promised low output at `0` shifted
by `1 / 2`, and a promised high output at `3` shifted by `1 / 4`,
both below the unit noise margins for `Vol = 0` and `Voh = 3`. -/
example : observe 1 2 ((0 : ℝ) + 1 / 2) = some false :=
  observe_noisy_low (Vol := 0) (y := 0) (e := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num)
example : observe 1 2 ((3 : ℝ) + 1 / 4) = some true :=
  observe_noisy_high (Voh := 3) (y := 3) (e := 1 / 4) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- Within budget, a concrete settling model with expected bit
`false`, ideal voltage `0`, noise `1 / 4` and observed voltage
`1 / 4` is observed as `false`. -/
example :
    observe 1 2 ((fun _ : Fin 1 => fun _ : Unit => (1 / 4 : ℝ)) 0 ()) = some false := by
  have hmodel : settlingGuarantee 1 2 0 3
      (fun _ : Fin 1 => fun _ : Unit => (0 : ℝ)) (fun _ : Fin 1 => (1 : ℝ))
      (fun _ : Fin 1 => fun _ : Unit => (0 : ℝ))
      (fun _ : Fin 1 => fun _ : Unit => (1 / 4 : ℝ))
      (fun _ : Fin 1 => fun _ : Unit => (1 / 4 : ℝ))
      (fun _ : Fin 1 => fun _ : Unit => false) := by
    refine ⟨fun _ _ => by norm_num, fun _ _ _ => Or.inl ⟨rfl, le_refl 0⟩, fun _ _ _ => ?_⟩
    norm_num
  have h := observe_observedVoltage_eq_some_of_le 1 2 0 3 (by norm_num) (by norm_num)
    (by norm_num) (fun _ : Fin 1 => fun _ : Unit => (0 : ℝ)) (fun _ : Fin 1 => (1 : ℝ))
    (fun _ : Fin 1 => fun _ : Unit => (0 : ℝ))
    (fun _ : Fin 1 => fun _ : Unit => (1 / 4 : ℝ))
    (fun _ : Fin 1 => fun _ : Unit => (1 / 4 : ℝ))
    (fun _ : Fin 1 => fun _ : Unit => false) hmodel 0 () (by norm_num)
  exact h

/-- The two-observation equal-budget sum over `Fin 2`:
`sum (Fin 2) (c * exp (-b / tau)) = 2 * (c * exp (-b / tau))`. -/
example (c b tau : ℝ) :
    ∑ _i : Fin 2, (c * Real.exp (-b / tau)) = 2 * (c * Real.exp (-b / tau)) := by
  rw [Fin.sum_univ_two]
  ring

end PhyslibExtTest.Electronics.SynchronizerObservationBudget
