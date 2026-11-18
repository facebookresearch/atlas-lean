/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.IdealBuckEnergy
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Circuits.IdealBuckEnergy

namespace PhyslibExtTest.Circuits.IdealBuckEnergy

/-- Concrete stored-energy state: `L = 2`, `C = 3`, current `4` and
voltage `5` give `2 * 4^2 / 2 + 3 * 5^2 / 2 = 107 / 2`, through the
public characterization. -/
example : buckStoredEnergy 2 3 (fun _ => 4) (fun _ => 5) 0 = 107 / 2 := by
  rw [buckStoredEnergy_eq]
  norm_num

/-- The same concrete state has nonnegative stored energy, through
the public nonnegativity lemma. -/
example : 0 ≤ buckStoredEnergy 2 3 (fun _ => 4) (fun _ => 5) 0 :=
  buckStoredEnergy_nonneg 2 3 (by norm_num) (by norm_num) (fun _ => 4)
    (fun _ => 5) 0

/-- A zero-length integral is zero, for the supplied-minus-loss
integrand shape at concrete values. -/
example (a : ℝ) (f : ℝ → ℝ) : (∫ t in a..a, f t) = 0 :=
  intervalIntegral.integral_same

example : (∫ t in (0:ℝ)..0, (fun _ : ℝ => (1:ℝ) * 2 * 3 - (4:ℝ)^2 / 5) t) = 0 :=
  intervalIntegral.integral_same

/-- Concrete output-node balance: constant voltage `10` with
`C = 2`, `R = 5` and inductor current `2` satisfies the capacitor
law `2 * 0 = 2 - 10 / 5`, and the public balance gives
`2 * 0 + 10 / 5 = 2`. -/
example : (2:ℝ) * deriv (fun _ : ℝ => (10:ℝ)) (0:ℝ) + (10:ℝ) / 5 = 2 := by
  have hClaw : (2:ℝ) * deriv (fun _ : ℝ => (10:ℝ)) (0:ℝ) = 2 - 10 / 5 := by
    rw [deriv_const]
    norm_num
  exact outputNode_current_balance_of_capacitorLaw 2 5 (fun _ => 2)
    (fun _ => 10) 0 hClaw

/-- The four-branch embedding at the same concrete values: branch
currents are `[-2, 2, 0, 2]`, so the output-node sum `0 + 2` equals
the inductor current `2` and the input-node sum `-2 + 2` is zero,
through the public embedding balance. -/
example : buckBranchCurrent 5 2 2 (deriv (fun _ : ℝ => (10:ℝ)) (0:ℝ)) 10 2 +
      buckBranchCurrent 5 2 2 (deriv (fun _ : ℝ => (10:ℝ)) (0:ℝ)) 10 3 =
      buckBranchCurrent 5 2 2 (deriv (fun _ : ℝ => (10:ℝ)) (0:ℝ)) 10 1 ∧
    buckBranchCurrent 5 2 2 (deriv (fun _ : ℝ => (10:ℝ)) (0:ℝ)) 10 0 +
      buckBranchCurrent 5 2 2 (deriv (fun _ : ℝ => (10:ℝ)) (0:ℝ)) 10 1 = 0 := by
  have hClaw : (2:ℝ) * deriv (fun _ : ℝ => (10:ℝ)) (0:ℝ) = 2 - 10 / 5 := by
    rw [deriv_const]
    norm_num
  exact buckEmbedding_current_balance 5 2 (fun _ => 2) (fun _ => 10) 0 hClaw

/-- Concrete branch voltages at switch value `1`, input `12` and
output `5`: source `12`, inductor drop `7`, capacitor `5`, resistor
`5`, evaluated componentwise through the public definition. -/
example : buckBranchVoltage 1 12 5 = ![12, 7, 5, 5] := by
  ext i
  fin_cases i <;> norm_num [buckBranchVoltage]

end PhyslibExtTest.Circuits.IdealBuckEnergy
