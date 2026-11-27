/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.Engineering.VaporSeries

/-!
# Vapor-series checks

Focused checks for `PhyslibExt.Engineering.VaporSeries`: three
nonuniform resistances `2, 3, 5` between pressures `1000` and
`400` give flux `60` and interface pressures `1000, 880, 700,
400`, with drops `120, 180, 300`.

These are elaboration and non-vacuity checks, not new results.
-/

open Engineering.VaporSeries

/-- Nonuniform three-layer flux and interfaces. -/
example : vaporSeriesFlux (n := 3) (fun i => if i = 0 then (2 : ℝ)
        else if i = 1 then 3 else 5) 1000 400 = 60
    ∧ vaporInterfacePressure (n := 3) (fun i => if i = 0 then (2 : ℝ)
        else if i = 1 then 3 else 5) 1000 400 1 = 880
    ∧ vaporInterfacePressure (n := 3) (fun i => if i = 0 then (2 : ℝ)
        else if i = 1 then 3 else 5) 1000 400 2 = 700 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [vaporSeriesFlux, vaporInterfacePressure,
      Finset.sum_range_succ]

/-- The final interface is the outer pressure at this witness. -/
example : vaporInterfacePressure (n := 3) (fun i => if i = 0 then (2 : ℝ)
      else if i = 1 then 3 else 5) 1000 400 3 = 400 :=
  vaporInterfacePressure_last _ _ _
    (by norm_num [Finset.sum_range_succ])

/-- The first layer drop is the flux times its resistance. -/
example : vaporInterfacePressure (n := 3) (fun i => if i = 0 then (2 : ℝ)
        else if i = 1 then 3 else 5) 1000 400 0
      - vaporInterfacePressure (n := 3) (fun i => if i = 0 then (2 : ℝ)
        else if i = 1 then 3 else 5) 1000 400 1
    = vaporSeriesFlux (n := 3) (fun i => if i = 0 then (2 : ℝ)
        else if i = 1 then 3 else 5) 1000 400 * 2 :=
  vaporInterfacePressure_succ_sub _ _ _ (by norm_num)
