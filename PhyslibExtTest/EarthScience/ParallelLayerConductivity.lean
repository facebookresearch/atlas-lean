/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.ParallelLayerConductivity

/-!
# Parallel-layer conductivity checks

Focused checks for
`PhyslibExt.EarthScience.ParallelLayerConductivity`: two
equal-thickness layers with conductivities `1` and `3` have
parallel effective conductivity `2` and series effective
conductivity `3 / 2`, and the comparison theorem applies to
that family. Equal conductivities give the common value in
both directions.

These are elaboration and non-vacuity checks, not new results.
-/

open EarthScience

/-- Parallel value `2` for conductivities `1` and `3`. -/
example : parallelEffectiveConductivity (n := 2) (fun _ => 1)
      (fun i => if i = 0 then 1 else 3) = 2 := by
  norm_num [parallelEffectiveConductivity, Finset.sum_range_succ]

/-- Series value `3 / 2` for conductivities `1` and `3`. -/
example : seriesEffectiveConductivity (n := 2) (fun _ => 1)
      (fun i => if i = 0 then 1 else 3) = 3 / 2 := by
  norm_num [seriesEffectiveConductivity, Finset.sum_range_succ]

/-- The comparison at the same two-layer family. -/
example : seriesEffectiveConductivity (n := 2) (fun _ => 1)
      (fun i => if i = 0 then 1 else 3)
    ≤ parallelEffectiveConductivity (n := 2) (fun _ => 1)
      (fun i => if i = 0 then 1 else 3) :=
  series_le_parallel (n := 2) (by norm_num) (fun _ => 1)
    (fun i => if i = 0 then 1 else 3)
    (fun i _ => by norm_num)
    (fun i hi => by interval_cases i <;> norm_num)

/-- Equal conductivities: both directions give `5`. -/
example : parallelEffectiveConductivity (n := 2) (fun _ => 1)
        (fun _ => 5) = 5
      ∧ seriesEffectiveConductivity (n := 2) (fun _ => 1)
        (fun _ => 5) = 5 := by
  constructor <;>
    norm_num [parallelEffectiveConductivity,
      seriesEffectiveConductivity, Finset.sum_range_succ]
