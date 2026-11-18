/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import PhyslibExt.Biophysics.EnergyStores
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-! Tests for the exercise-efficiency bound (perfect efficiency,
vanishing mechanical power, constant powers over a unit window) and
the energy-budget identity at constant net flux. -/

namespace PhyslibExtTest.Biophysics.EnergyStores

open PhyslibExt.Biophysics.EnergyStores

/-- Perfect efficiency `eta = 1`: metabolic power is baseline plus
mechanical power. -/
example {Pbase Pmech : ℝ} (hbase : 0 ≤ Pbase) (hmech : 0 ≤ Pmech) :
    Pmech ≤ Pbase + Pmech / 1 :=
  exercise_efficiency_bound hbase hmech one_pos (le_refl 1)

/-- Vanishing mechanical power: the bound is the nonnegative baseline. -/
example {Pbase eta : ℝ} (hbase : 0 ≤ Pbase) (heta0 : 0 < eta) (heta1 : eta ≤ 1) :
    (0 : ℝ) ≤ Pbase + 0 / eta :=
  exercise_efficiency_bound hbase (le_refl 0) heta0 heta1

/-- Constant powers over `[0, 1]`: mechanical work `2` is at most the
metabolic cost `1 + 2 / (1/2) = 5`. -/
example : (∫ _t in (0:ℝ)..1, (2:ℝ)) ≤ ∫ _t in (0:ℝ)..1, ((1:ℝ) + 2 / (1/2)) := by
  have h := exercise_efficiency_integral (Pbase := fun _ => (1:ℝ)) (Pmech := fun _ => (2:ℝ))
    (eta := 1/2) (a := 0) (b := 1) (by norm_num : (0:ℝ) ≤ 1) (by norm_num) (by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num)
    intervalIntegrable_const intervalIntegrable_const
  exact h

/-- Constant net flux: `F = fun s => s`, `L = 0`, densities `2, 3`,
`qF = 2`, `qL = 0`, intake `5`, expenditure `3` over `[0, 2]`:
stored energy grows by `2 * 2 = 4`. -/
example : ((2:ℝ) * 2 + 3 * 0) - (2 * 0 + 3 * 0) =
    ∫ _s in (0:ℝ)..2, ((5:ℝ) - 3) := by
  have h := energy_budget (rhoF := 2) (rhoL := 3) (F := fun s => s) (L := fun _ => (0:ℝ))
    (qF := fun _ => (2:ℝ)) (qL := fun _ => (0:ℝ)) (intake := fun _ => (5:ℝ))
    (expenditure := fun _ => (3:ℝ)) (t := 2) (by norm_num) (by norm_num) (by norm_num)
    (fun s _ => by
      have hid : HasDerivAt (fun u : ℝ => u) 1 s := hasDerivAt_id s
      have h1 := hid.const_mul (2 : ℝ)
      simpa using h1)
    (fun s _ => by simpa using (hasDerivAt_const s (0 : ℝ)))
    (fun _ _ => by norm_num)
    intervalIntegrable_const
  exact h
/-- Densities `2, 1` and shift `s = 1/2` from `(1, 2)` reach
`(3/2, 1)`: same energy, mass drops from `3` to `5/2`. -/
example : (2:ℝ) * (1 + 1 * (1/2)) + 1 * (2 - 2 * (1/2)) = 2 * 1 + 1 * 2 ∧
    ((1 + 1 * (1/2)) + (2 - 2 * (1/2))) - (1 + 2) = ((1:ℝ) - 2) * (1/2) :=
  energy_composition_perturbation

/-- The witness energies and masses. -/
example : (2 : ℝ) * 1 + 1 * 2 = 4 ∧ (2 : ℝ) * (3 / 2) + 1 * 1 = 4 ∧
    (3 : ℝ) ≠ 5 / 2 := by
  have h := energy_composition_witness
  exact ⟨h.1, h.2.1, h.2.2.2.2⟩

end PhyslibExtTest.Biophysics.EnergyStores
