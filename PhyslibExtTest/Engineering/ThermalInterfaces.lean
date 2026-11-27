/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.Engineering.ThermalInterfaces

/-!
# Thermal interface checks

Focused checks for `PhyslibExt.Engineering.ThermalInterfaces`:
one layer with unit area, inside and outside film
coefficients `10` and `20`, layer thickness `1 / 5`, unit
conductivity, inside and outside temperatures `20` and `13`.
The total resistance is `7 / 20`, the heat rate is `20`, the
two interface temperatures are `18` and `14`, and the
reconstruction ends at `13`.

These are elaboration and non-vacuity checks, not new results.
-/

open Engineering.ThermalInterfaces

/-- The interface after the inside film is `18`. -/
example : thermalInterfaceTemp 1 10 20 20
      (fun _ => 1 / 5) (fun _ => 1) 0 = 18 := by
  norm_num [thermalInterfaceTemp]

/-- The interface after the single layer is `14`, a layer
drop of `4`. -/
example : thermalInterfaceTemp 1 10 20 20
        (fun _ => 1 / 5) (fun _ => 1) 0
      - thermalInterfaceTemp 1 10 20 20
        (fun _ => 1 / 5) (fun _ => 1) 1 = 4 := by
  have h := thermalInterfaceTemp_succ_sub (m := 0)
    1 10 20 20 (fun _ => 1 / 5) (fun _ => 1)
  norm_num at h ⊢
  exact h

/-- End matching: the last interface minus the outside film
drop is the outside temperature `13`. -/
example : thermalInterfaceTemp 1 10 20
        ((20 - 13)
          / thermalTotalResistance (n := 1) 1 10 20
            (fun _ => 1 / 5) (fun _ => 1))
        (fun _ => 1 / 5) (fun _ => 1) 1
      - ((20 - 13)
          / thermalTotalResistance (n := 1) 1 10 20
            (fun _ => 1 / 5) (fun _ => 1))
        * (1 / ((20 : ℝ) * 1))
    = 13 :=
  thermalInterfaceTemp_last_sub_film (n := 1)
    (A := 1) (hin := 10) (hout := 20) (Tin := 20) (Tout := 13)
    (fun _ => 1 / 5) (fun _ => 1)
    (by norm_num [thermalTotalResistance, Finset.sum_range_one])

/-- The same end matching through the physical
positive-domain form, without a separate nonzero-resistance
proof. -/
example : thermalInterfaceTemp 1 10 20
        ((20 - 13)
          / thermalTotalResistance (n := 1) 1 10 20
            (fun _ => 1 / 5) (fun _ => 1))
        (fun _ => 1 / 5) (fun _ => 1) 1
      - ((20 - 13)
          / thermalTotalResistance (n := 1) 1 10 20
            (fun _ => 1 / 5) (fun _ => 1))
        * (1 / ((20 : ℝ) * 1))
    = 13 :=
  thermalInterfaceTemp_last_sub_film_of_pos (n := 1)
    (A := 1) (hin := 10) (hout := 20) (Tin := 20) (Tout := 13)
    (by norm_num) (by norm_num) (by norm_num)
    (fun _ => 1 / 5) (fun _ => 1)
    (by intro i _; norm_num) (by intro i _; norm_num)
