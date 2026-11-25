/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Engineering.HumidityRatio
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Humidity-ratio checks

Concrete consumers of `PhyslibExt.Engineering.HumidityRatio`:
reversible conversion at numbers, the total-ratio update on a
two-node inventory, and the changing-dry-air control showing
the constant-denominator premise is essential.

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Conversion values
- B. Total-ratio update and the changing-dry-air control

## iv. References

- `PhyslibExt.Engineering.HumidityRatio`
-/

open Matrix
open Engineering.HumidityRatio
open MathlibExt.Combinatorics.Graph.ArcNetwork

namespace PhyslibExtTest.Engineering.HumidityRatio

/-! ## A. Conversion values -/

/-- 5 kg vapor over 100 kg dry air is ratio 1/20, and back. -/
example : humidityRatio 5 100 = 1 / 20 := by
  norm_num [humidityRatio]

example : (5 : ℝ) = humidityRatio 5 100 * 100 :=
  vaporMass_eq_humidityRatio_mul (by norm_num)

example : humidityRatio ((1 / 20) * 100) 100 = 1 / 20 :=
  humidityRatio_mul_dryAir (by norm_num)

example : humidityRatio 0 100 = 0 :=
  humidityRatio_zero_vapor (by norm_num)

example : 0 ≤ humidityRatio 5 100 :=
  humidityRatio_nonneg (by norm_num) (by norm_num)

/-- At zero dry air the forward conversion fails: the ratio
collapses to `0` and cannot recover the vapor mass. -/
example : ¬ ((5 : ℝ) = humidityRatio 5 0 * 0) := by
  norm_num [humidityRatio]

/-! ## B. Total-ratio update and the changing-dry-air control -/

/-- Two-node inventory, no transfers, one addition: the total
ratio moves by the addition over constant dry air. -/
example : humidityRatio
      (∑ v, (![4, 1] : Fin 2 → ℝ) v) 100
    = humidityRatio (∑ v, (![3, 1] : Fin 2 → ℝ) v) 100
      + ((∑ v, (![1, 0] : Fin 2 → ℝ) v)
        - (∑ v, (0 : Fin 2 → ℝ) v)) / 100 :=
  totalHumidityRatio_update (![0] : Fin 1 → Fin 2) ![1] ![0]
    (m := ![3, 1]) (s := ![1, 0]) (r := 0)
    (by funext v; fin_cases v <;>
      simp [incidence_mulVec]; norm_num)
    (by norm_num)

/-- Changing dry air is not the constant shortcut: vapor and
dry air both double, so the ratio stays `1`, while the
constant-denominator update would predict `2`. -/
example : humidityRatio 2 2 = 1
    ∧ humidityRatio 1 1 + (2 - 1) / 1 = 2
    ∧ humidityRatio 2 2 ≠ humidityRatio 1 1 + (2 - 1) / 1 := by
  norm_num [humidityRatio]

#print axioms Engineering.HumidityRatio.vaporMass_eq_humidityRatio_mul
#print axioms Engineering.HumidityRatio.humidityRatio_mul_dryAir
#print axioms Engineering.HumidityRatio.totalHumidityRatio_update

end PhyslibExtTest.Engineering.HumidityRatio
