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
source-bridge results, endpoint or excluded-parameter controls for
`n = 1 / 2`, `n = 0`, `α = 0`, `α < 0`, and `n < 0`, and water-content
checks: public shapes, the saturated head, finite-head non-attainment
of the residual content, and premise controls.

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
- C. Volumetric water content

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
example {α n h : ℝ} (hα : 0 < α) (hn : 1 < n) (hh : h ≤ 0) :
    EarthScience.vanGenuchtenSe α n h =
      (1 / (1 + (α * -h) ^ n)) ^ (1 - 1 / n) :=
  EarthScience.vanGenuchtenSe_eq_source hα hn hh

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

/-! ## C. Volumetric water content -/

/-- The public statement shape of the Eq. [2] bridge. -/
example {θr θs θ α n h : ℝ} (hθ : θr < θs) :
    (θ - θr) / (θs - θr) = EarthScience.vanGenuchtenSe α n h ↔
      θ = θr + (θs - θr) * EarthScience.vanGenuchtenSe α n h :=
  EarthScience.vanGenuchtenSe_eq_div_iff_waterContent hθ

/-- The public statement shape of the water-content bounds. -/
example {θr θs α n h : ℝ} (hθ : θr < θs) (hα : 0 < α) (hn : 1 < n)
    (hh : h ≤ 0) :
    θr + (θs - θr) * EarthScience.vanGenuchtenSe α n h ∈ Set.Ioc θr θs :=
  EarthScience.vanGenuchten_waterContent_mem_Ioc hθ hα hn hh

/-- The public statement shape of the `θs ≤ θr` control. -/
example {θr θs α n h : ℝ} (hθ : θs ≤ θr) (hα : 0 < α) (hn : 1 < n)
    (hh : h ≤ 0) :
    θr + (θs - θr) * EarthScience.vanGenuchtenSe α n h ≤ θr :=
  EarthScience.vanGenuchten_waterContent_le_residual_of_le hθ hα hn hh

/-- Saturated head: at `h = 0` the water content is `θs`. -/
example {θr θs α n : ℝ} (hn : 1 < n) :
    θr + (θs - θr) * EarthScience.vanGenuchtenSe α n 0 = θs := by
  rw [EarthScience.vanGenuchtenSe_zero_head hn]
  ring

/-- Finite-head non-attainment: the residual content `θr` is not reached
at any finite unsaturated head. -/
example {θr θs α n : ℝ} (hθ : θr < θs) (hα : 0 < α) (hn : 1 < n)
    (h : ℝ) (hh : h ≤ 0) :
    θr + (θs - θr) * EarthScience.vanGenuchtenSe α n h ≠ θr := by
  intro he
  have hlt := (EarthScience.vanGenuchten_waterContent_mem_Ioc hθ hα hn hh).1
  linarith

/-- Excluded exponent `n = 1 / 2`: the water content overshoots `θs`. -/
example {θr θs : ℝ} (hθ : θr < θs) :
    θs < θr + (θs - θr) * EarthScience.vanGenuchtenSe 1 (1 / 2) (-1) := by
  have h2 : EarthScience.vanGenuchtenSe 1 (1 / 2) (-1) = 2 := by
    norm_num [EarthScience.vanGenuchtenSe]
  rw [h2]
  linarith

/-- Interior witness: `θr = 1/20`, `θs = 9/20` at `α = 1`, `n = 2`,
`h = -1` puts the water content strictly inside `(θr, θs)`. -/
example :
    (1 / 20 : ℝ) < 1 / 20 + (9 / 20 - 1 / 20) * EarthScience.vanGenuchtenSe 1 2 (-1) ∧
      1 / 20 + (9 / 20 - 1 / 20) * EarthScience.vanGenuchtenSe 1 2 (-1) < 9 / 20 := by
  have h := EarthScience.vanGenuchten_waterContent_mem_Ioc (θr := 1 / 20)
    (θs := 9 / 20) (α := 1) (n := 2) (h := -1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hlt := EarthScience.vanGenuchtenSe_lt_one (α := 1) (n := 2) (h := -1)
    (by norm_num) (by norm_num) (by norm_num)
  have hmul : (9 / 20 - 1 / 20 : ℝ) * EarthScience.vanGenuchtenSe 1 2 (-1) <
      (9 / 20 - 1 / 20 : ℝ) * 1 :=
    mul_lt_mul_of_pos_left hlt (by norm_num)
  constructor <;> linarith [h.1, hmul]

/-- The upper end is sharp: `θs` is attained at the finite head `h = 0`. -/
example {θr θs α n : ℝ} (hn : 1 < n) :
    ∃ h : ℝ, h ≤ 0 ∧ θr + (θs - θr) * EarthScience.vanGenuchtenSe α n h = θs :=
  ⟨0, le_refl 0, by rw [EarthScience.vanGenuchtenSe_zero_head hn]; ring⟩

/-- Excluded parameter `α = -1`, `n = 3`: the totalized saturation is `0`
at `h = -1`, so the residual content is attained at a finite head and
`α > 0` cannot be dropped. -/
example {θr θs : ℝ} :
    θr + (θs - θr) * EarthScience.vanGenuchtenSe (-1) 3 (-1) = θr := by
  have h0 : EarthScience.vanGenuchtenSe (-1) 3 (-1) = 0 := by
    norm_num [EarthScience.vanGenuchtenSe]
  rw [h0]
  simp

/-- Degenerate contents `θs = θr`: the excess over `θr` is zero. -/
example {θr α n h : ℝ} :
    θr + (θr - θr) * EarthScience.vanGenuchtenSe α n h - θr = 0 := by ring

/-- Equal endpoints break the Eq. [2] bridge: at `θr = θs = θ = 0` its
right side holds while the left side is the false `0 = S_e > 0`. (The
bridge theorem is stated under the physical order `θr < θs`; algebraically
its proof uses only `θs - θr ≠ 0`.) -/
example : ¬ (((0 : ℝ) - 0) / (0 - 0) = EarthScience.vanGenuchtenSe 1 2 (-1) ↔
    (0 : ℝ) = 0 + (0 - 0) * EarthScience.vanGenuchtenSe 1 2 (-1)) := by
  intro hiff
  have hpos := (EarthScience.vanGenuchtenSe_pos_and_le_one (α := 1) (n := 2)
    (h := -1) (by norm_num) (by norm_num) (by norm_num)).1
  have hl := hiff.mpr (by simp)
  have hz : EarthScience.vanGenuchtenSe 1 2 (-1) = 0 := by simpa using hl.symm
  linarith

/-- Eq. [21] form: the water content through the source-form saturation. -/
example {θr θs α n h : ℝ} (hα : 0 < α) (hn : 1 < n) (hh : h ≤ 0) :
    θr + (θs - θr) * EarthScience.vanGenuchtenSe α n h =
      θr + (θs - θr) * (1 / (1 + (α * -h) ^ n)) ^ (1 - 1 / n) := by
  rw [EarthScience.vanGenuchtenSe_eq_source hα hn hh]
