/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.LayeredDarcy

/-!
# Layered Darcy checks

Focused checks for `PhyslibExt.EarthScience.LayeredDarcy`: two
unit-thickness layers with conductivities `1` and `3` have
effective conductivity `3 / 2` (the harmonic, not arithmetic,
mean), a one-layer drop law recovers the flux, and two
boundary examples document where the totalized quotient has
no physical reading.

These are elaboration and non-vacuity checks, not new results.
-/

open EarthScience

/-- Two-layer harmonic effective conductivity. -/
example : layeredEffectiveConductivity (n := 2) (fun _ => 1)
    (fun i => if i = 0 then (1 : ℝ) else 3) = 3 / 2 := by
  norm_num [layeredEffectiveConductivity, Finset.sum_range_succ]

/-- One-layer flux recovery: heads `3` to `1` over one layer of
thickness `2` and conductivity `4` give flux `4`. -/
example : (4 : ℝ) = (3 - 1) / ((2 : ℝ) / 4) := by
  have h := layeredDarcyFlux_of_drops (n := 1) (by norm_num)
    (L := fun _ => (2 : ℝ)) (K := fun _ => (4 : ℝ))
    (head := fun i => if i = 0 then (3 : ℝ) else 1) (q := 4)
    (by intro i _; norm_num) (by intro i _; norm_num)
    (by intro i hi; interval_cases i <;> norm_num)
  simpa [Finset.sum_range_one] using h

/-- Boundary documentation of the totalization: the empty
system evaluates to `0` by Lean's division convention; this is
not a physical conductivity claim (the physical results all
require at least one positive layer). -/
example : layeredEffectiveConductivity (n := 0) (fun _ => (1 : ℝ))
    (fun _ => 1) = 0 := by
  norm_num [layeredEffectiveConductivity]

/-- Boundary documentation of the totalization at a
zero-conductivity layer: the raw quotient evaluates to `2`
because Lean totalizes `1 / 0` to `0`. This is not a physical
effective conductivity (an impermeable series layer is
outside the positive-conductivity domain of the formula). -/
example : layeredEffectiveConductivity (n := 2) (fun _ => (1 : ℝ))
    (fun i => if i = 0 then (0 : ℝ) else 1) = 2 := by
  norm_num [layeredEffectiveConductivity, Finset.sum_range_succ]
