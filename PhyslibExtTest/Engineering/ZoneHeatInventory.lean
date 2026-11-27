/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.Engineering.ZoneHeatInventory

/-!
# Zone heat-inventory checks

Focused checks for `PhyslibExt.Engineering.ZoneHeatInventory`: two
zones on `Fin 2` with capacities `1, 2`, reciprocal conductance
`3/2`, constant temperatures `3, 5`, and boundary inputs chosen to
satisfy the zone equations, through the public theorem.

These are elaboration and non-vacuity checks, not new results.
-/

open ZoneHeatInventory

/-- Two-zone application of the public theorem. -/
example (t : ℝ) : HasDerivAt
    (fun s => ∑ i : Fin 2, (![1, 2] i) * ((fun i _ => ![3, 5] i) i s))
    (∑ i : Fin 2, ((fun i _ => -(∑ j : Fin 2,
        (fun i j => if i = j then (0:ℝ) else 3 / 2) i j
          * (![3, 5] j - ![3, 5] i))) i t + 0)) t :=
  heat_inventory_deriv ![1, 2] (fun i j => if i = j then 0 else 3 / 2)
    (fun i _ => ![3, 5] i) (fun _ _ => 0)
    (fun i _ => -(∑ j : Fin 2,
      (fun i j => if i = j then (0:ℝ) else 3 / 2) i j
        * (![3, 5] j - ![3, 5] i)))
    (fun _ _ => 0)
    (by intro i j; fin_cases i <;> fin_cases j <;> simp)
    (by intro i s; exact hasDerivAt_const s _)
    (by intro i s; dsimp only; ring) t
