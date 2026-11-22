/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.UnitHydrograph

/-!
# Unit hydrograph checks

Focused checks for `PhyslibExt.EarthScience.UnitHydrograph`: a unit
pulse of rainfall through the two-step response `(1, 1)` gives total
response `2`, and with normalization `dt * 2 = A` the volume is `A`.

These are elaboration and non-vacuity checks, not new results.
-/

open EarthScience

/-- Total response for a pulse input, through the public theorem. -/
example : ∑ k ∈ Finset.range (1 + 2),
      discreteConvolution (fun i => if i = 0 then (1 : ℝ) else 0)
        (fun j => if j < 2 then (1 : ℝ) else 0) k = 2 := by
  have h := discreteConvolution_sum_eq (p := fun i => if i = 0 then (1 : ℝ) else 0)
    (u := fun j => if j < 2 then (1 : ℝ) else 0) (n := 1) (m := 2)
    (by intro i hi; simp [show i ≠ 0 by omega])
    (by intro j hj; simp [show ¬ j < 2 by omega])
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- Runoff volume under the normalization `dt * ∑ u = A`, through the
public volume theorem. -/
example : (1 : ℝ) * ∑ k ∈ Finset.range (1 + 2),
      discreteConvolution (fun i => if i = 0 then (1 : ℝ) else 0)
        (fun j => if j < 2 then (1 : ℝ) else 0) k
    = 2 * ∑ i ∈ Finset.range 1, (fun i => if i = 0 then (1 : ℝ) else 0) i :=
  discreteConvolution_volume_eq
    (by intro i hi; simp [show i ≠ 0 by omega])
    (by intro j hj; simp [show ¬ j < 2 by omega])
    (by simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num)

/-- The same total for the canonical `sumConv`. -/
example : ∑ k ∈ Finset.range (1 + 2),
      AdditiveCombinatorics.sumConv (fun i => if i = 0 then (1 : ℝ) else 0)
        (fun j => if j < 2 then (1 : ℝ) else 0) k = 2 := by
  have h := AdditiveCombinatorics.sum_range_sumConv (R := ℝ)
    (f := fun i => if i = 0 then (1 : ℝ) else 0)
    (g := fun j => if j < 2 then (1 : ℝ) else 0) (n := 1) (m := 2)
    (by intro i hi; simp [show i ≠ 0 by omega])
    (by intro j hj; simp [show ¬ j < 2 by omega])
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
