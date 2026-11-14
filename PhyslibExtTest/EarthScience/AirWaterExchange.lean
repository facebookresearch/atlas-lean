/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.AirWaterExchange
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Air-water exchange checks

Concrete consumers of `PhyslibExt.EarthScience.AirWaterExchange`:
conservation for a linear exchange, the disequilibrium equation at all-ones
coefficients, the equilibrium boundary case, and a concrete relaxing
solution that satisfies the hypotheses of the forward-time decay theorem.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With all
coefficients `1`, the rate is `2`; at equilibrium (`J = 0`) both stocks
are constant; `ng t = 1 + exp (-2 * t)`, `nw t = 1 - exp (-2 * t)` solves
the all-ones exchange equations, and its disequilibrium tends to `0`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Conservation and the equation at unit coefficients
- B. Equilibrium and forward-time decay
-/

/-! ## A. Conservation and the equation at unit coefficients -/

/-- The public shape of total-inventory conservation. -/
example (Vg Vw R T H k A : ℝ) (ng nw : ℝ → ℝ) (t : ℝ)
    (hng : HasDerivAt ng (-(k * A * (H * (ng t * R * T / Vg) - nw t / Vw))) t)
    (hnw : HasDerivAt nw (k * A * (H * (ng t * R * T / Vg) - nw t / Vw)) t) :
    HasDerivAt (fun t => ng t + nw t) 0 t :=
  EarthScience.air_water_total_conserved Vg Vw R T H k A ng nw t hng hnw

/-- All-ones coefficients: the disequilibrium `ng - nw` satisfies
`d' = -2 * d`, so the rate is `2`. -/
example (ng nw : ℝ → ℝ) (t : ℝ)
    (hng : HasDerivAt ng (-(ng t - nw t)) t)
    (hnw : HasDerivAt nw (ng t - nw t) t) :
    HasDerivAt (fun t => ng t - nw t) (-2 * (ng t - nw t)) t := by
  have h := EarthScience.air_water_difference_ode 1 1 1 1 1 1 1 one_pos one_pos ng nw t
    (by simpa using hng) (by simpa using hnw)
  norm_num at h
  simpa [neg_mul] using h

/-! ## B. Equilibrium and forward-time decay -/

/-- Equilibrium boundary: equal stocks give zero flux, constant stocks,
conserved total. -/
example (t : ℝ) :
    HasDerivAt (fun _ => (5 : ℝ) + 5) 0 t := by
  have hng : HasDerivAt (fun _ : ℝ => (5 : ℝ))
      (-(1 * 1 * (1 * ((5 : ℝ) * 1 * 1 / 1) - 5 / 1))) t := by
    have h : -(1 * 1 * (1 * ((5 : ℝ) * 1 * 1 / 1) - 5 / 1)) = 0 := by norm_num
    rw [h]
    exact hasDerivAt_const t (5 : ℝ)
  have hnw : HasDerivAt (fun _ : ℝ => (5 : ℝ))
      (1 * 1 * (1 * ((5 : ℝ) * 1 * 1 / 1) - 5 / 1)) t := by
    have h : (1 * 1 * (1 * ((5 : ℝ) * 1 * 1 / 1) - 5 / 1)) = 0 := by norm_num
    rw [h]
    exact hasDerivAt_const t (5 : ℝ)
  have htot := EarthScience.air_water_total_conserved 1 1 1 1 1 1 1
    (fun _ => (5 : ℝ)) (fun _ => (5 : ℝ)) t hng hnw
  simpa using htot

/-- A concrete relaxing solution satisfies the hypotheses of the decay
theorem: with all coefficients `1`, `ng t = 1 + exp (-2 * t)` and
`nw t = 1 - exp (-2 * t)` solve the exchange equations, and their
disequilibrium `2 * exp (-2 * t)` tends to `0`. -/
example : Filter.Tendsto
    (fun t : ℝ => 1 * ((1 + Real.exp (-2 * t)) * 1 * 1 / 1) - (1 - Real.exp (-2 * t)) / 1)
    Filter.atTop (nhds 0) := by
  have hng : ∀ t : ℝ, HasDerivAt (fun t => 1 + Real.exp (-2 * t))
      (-(1 * 1 * (1 * ((1 + Real.exp (-2 * t)) * 1 * 1 / 1) -
        (1 - Real.exp (-2 * t)) / 1))) t := fun t =>
    (((hasDerivAt_id' t).const_mul (-2 : ℝ)).exp.const_add 1).congr_deriv (by ring)
  have hnw : ∀ t : ℝ, HasDerivAt (fun t => 1 - Real.exp (-2 * t))
      (1 * 1 * (1 * ((1 + Real.exp (-2 * t)) * 1 * 1 / 1) -
        (1 - Real.exp (-2 * t)) / 1)) t := fun t =>
    (((hasDerivAt_id' t).const_mul (-2 : ℝ)).exp.const_sub 1).congr_deriv (by ring)
  exact EarthScience.air_water_difference_tendsto_zero 1 1 1 1 1 1 1 one_pos one_pos
    one_pos one_pos one_pos one_pos one_pos _ _ hng hnw
