/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.AirWaterExchange

/-!
# Air-water exchange checks

Concrete consumers of `PhyslibExt.EarthScience.AirWaterExchange`:
conservation for a linear exchange, the decay equation at all-ones
coefficients, exponential decay of a concrete disequilibrium, and the
equilibrium boundary case.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With all
coefficients `1`, the decay rate is `2`; at equilibrium (`J = 0`) both
stocks are constant.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Conservation and decay at unit coefficients
- B. Exponential decay and equilibrium
-/

/-- The public shape of total-inventory conservation. -/
example (Vg Vw R T H k A : ℝ) (ng nw : ℝ → ℝ) (t : ℝ)
    (hng : HasDerivAt ng (-(k * A * (H * (ng t * R * T / Vg) - nw t / Vw))) t)
    (hnw : HasDerivAt nw (k * A * (H * (ng t * R * T / Vg) - nw t / Vw)) t) :
    HasDerivAt (fun t => ng t + nw t) 0 t :=
  EarthScience.air_water_total_conserved Vg Vw R T H k A ng nw t hng hnw

/-- All-ones coefficients: the disequilibrium decay rate is `2`. -/
example (ng nw : ℝ → ℝ) (t : ℝ)
    (hng : HasDerivAt ng (-(1 * 1 * (1 * (ng t * 1 * 1 / 1) - nw t / 1))) t)
    (hnw : HasDerivAt nw (1 * 1 * (1 * (ng t * 1 * 1 / 1) - nw t / 1)) t) :
    HasDerivAt (fun t => 1 * (ng t * 1 * 1 / 1) - nw t / 1)
      (-(1 * 1 * (1 * 1 * 1 / 1 + 1 / 1)) *
        (1 * (ng t * 1 * 1 / 1) - nw t / 1)) t :=
  EarthScience.air_water_difference_ode 1 1 1 1 1 1 1 (by norm_num)
    (by norm_num) ng nw t hng hnw

/-- A concrete decaying disequilibrium: `d(t) = 3 * exp (-2 * t)`. -/
example (t : ℝ) :
    (fun t => 3 * Real.exp (-2 * t)) t =
      (fun t => 3 * Real.exp (-2 * t)) 0 * Real.exp (-2 * t) := by
  have hd : ∀ s, HasDerivAt (fun t => 3 * Real.exp (-2 * t))
      (-2 * (3 * Real.exp (-2 * s))) s := by
    intro s
    have h : HasDerivAt (fun t => Real.exp (-2 * t))
        (Real.exp (-2 * s) * (-2)) s := by
      simpa using ((hasDerivAt_id' s).const_mul (-2 : ℝ)).exp
    have h2 := h.const_mul (3 : ℝ)
    convert h2 using 1
    ring
  exact EarthScience.exp_decay_of_linear_ode _ 2 hd t

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
