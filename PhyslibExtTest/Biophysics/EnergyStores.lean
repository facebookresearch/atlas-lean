/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import PhyslibExt.Biophysics.EnergyStores

/-! Tests for the exercise-efficiency bound: perfect efficiency,
vanishing mechanical power, and constant powers over a unit window. -/

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

end PhyslibExtTest.Biophysics.EnergyStores
