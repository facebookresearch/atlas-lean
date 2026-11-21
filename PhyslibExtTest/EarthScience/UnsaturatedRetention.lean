/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.UnsaturatedRetention
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Van Genuchten effective saturation checks

Consumers of `PhyslibExt.EarthScience.UnsaturatedRetention`: a nonzero
value strictly inside the range, the public shapes of the range and
source-bridge results, and endpoint or excluded-parameter controls for
`n = 1 / 2`, `n = 0`, `α = 0`, `α < 0`, and `n < 0`.

## i. Overview

These are elaboration, non-vacuity, and boundary checks, not new results.
The negative-`α` control uses Mathlib's negative-base real-power branch;
it is a counterexample outside the physical domain `α > 0`, not a claim
about the retention model there.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Non-vacuity and public shapes
- B. Endpoint and excluded-parameter controls

## iv. References

- `PhyslibExt.EarthScience.UnsaturatedRetention`
-/

/-- Non-vacuity value: at `α = 1`, `n = 2`, `h = -1`, the saturation is
`2^(-1 / 2)`, strictly inside `(0, 1)`. -/
example : EarthScience.vanGenuchtenSe 1 2 (-1) = (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  norm_num [EarthScience.vanGenuchtenSe]

/-- The same point is positive and strictly unsaturated, through the
public range and strict-bound results. -/
example : 0 < EarthScience.vanGenuchtenSe 1 2 (-1) ∧
    EarthScience.vanGenuchtenSe 1 2 (-1) < 1 :=
  ⟨(EarthScience.vanGenuchtenSe_pos_and_le_one
      (by norm_num) (by norm_num) (by norm_num)).1,
    EarthScience.vanGenuchtenSe_lt_one (by norm_num) (by norm_num) (by norm_num)⟩

/-- The public statement shape of the saturation range. -/
example {α n h : ℝ} (hα : 0 < α) (hn : 1 < n) (hh : h ≤ 0) :
    0 < EarthScience.vanGenuchtenSe α n h ∧
      EarthScience.vanGenuchtenSe α n h ≤ 1 :=
  EarthScience.vanGenuchtenSe_pos_and_le_one hα hn hh

/-- The public statement shape of the source bridge. -/
example {α n h : ℝ} (hα : 0 < α) (hh : h ≤ 0) :
    EarthScience.vanGenuchtenSe α n h =
      (1 / (1 + (α * -h) ^ n)) ^ (1 - 1 / n) :=
  EarthScience.vanGenuchtenSe_eq_source hα hh

/-- Excluded exponent `n = 1 / 2`: the value is `2`, outside the range. -/
example : EarthScience.vanGenuchtenSe 1 (1 / 2) (-1) = 2 := by
  norm_num [EarthScience.vanGenuchtenSe]

/-- Totalized control at `n = 0`, `h = 0`: the closed form evaluates to
`1 / 2`, which is why the zero-head result needs `n > 1`. -/
example : EarthScience.vanGenuchtenSe 1 0 0 = 1 / 2 := by
  norm_num [EarthScience.vanGenuchtenSe]

/-- Excluded parameter `α = 0`: the closed form is identically `1`, so the
strict unsaturated bound needs `α > 0`. -/
example (h : ℝ) : EarthScience.vanGenuchtenSe 0 2 h = 1 := by
  simp [EarthScience.vanGenuchtenSe]

/-- Excluded parameter `α < 0`: with Mathlib's negative-base real power,
the upper bound fails at `α = -1`, `n = 5 / 4`, `h = -1`. -/
example : 1 < EarthScience.vanGenuchtenSe (-1) (5 / 4) (-1) := by
  unfold EarthScience.vanGenuchtenSe
  have hc : ((-1 : ℝ) * |(-1 : ℝ)|) ^ (5 / 4 : ℝ) = -(Real.sqrt 2 / 2) := by
    rw [show (-1 : ℝ) * |(-1 : ℝ)| = -1 by norm_num,
      Real.rpow_def_of_neg (by norm_num), Real.log_neg_eq_log, Real.log_one, zero_mul,
      Real.exp_zero, one_mul]
    have hpi : (5 / 4 : ℝ) * Real.pi = Real.pi / 4 + Real.pi := by ring
    rw [hpi, Real.cos_add_pi, Real.cos_pi_div_four]
  rw [hc]
  have h2 : Real.sqrt 2 < 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h0 : 0 < Real.sqrt 2 := by positivity
  refine Real.one_lt_rpow_of_pos_of_lt_one_of_neg (by linarith) (by linarith) (by norm_num)

/-- Excluded exponent `n = -1` at `h = -1`: the value is `1 / 4`. -/
example : EarthScience.vanGenuchtenSe 1 (-1) (-1) = 1 / 4 := by
  norm_num [EarthScience.vanGenuchtenSe]

/-- Excluded exponent `n = -1` at `h = -10`: the value is `100 / 121`. -/
example : EarthScience.vanGenuchtenSe 1 (-1) (-10) = 100 / 121 := by
  norm_num [EarthScience.vanGenuchtenSe]

/-- For `n = -1`, increasing `|h|` increases the value, reversing the
physical monotonicity; this branch is excluded by the premise `n > 1`. -/
example : EarthScience.vanGenuchtenSe 1 (-1) (-1) <
    EarthScience.vanGenuchtenSe 1 (-1) (-10) := by
  norm_num [EarthScience.vanGenuchtenSe]
