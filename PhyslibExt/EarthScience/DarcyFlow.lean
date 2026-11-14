/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Darcy flow through a linear-head porous column

For the one-dimensional saturated homogeneous column with the linear
hydraulic-head profile `h(x) = h0 + (hL - h0) * x / L`, Darcy's law
`q = -K * h'` gives the constant specific discharge
`q = -K * (hL - h0) / L`, and the pore (average linear) velocity is
`v = q / φ = -K * (hL - h0) / (L * φ)`.

## i. Overview

`L` is the column length, `K` the hydraulic conductivity, `h0` and `hL`
the fixed heads at the two ends, and `φ` the effective porosity. The head
gradient is the constant slope `(hL - h0) / L`, so the Darcy flux is
constant along the column. Equal boundary heads give zero flux; a
reversed gradient reverses the flux sign. Hydraulic conductivity `K`
(length/time) is distinct from intrinsic permeability. The module is
self-contained from Mathlib primitives.

## ii. Key results

- `EarthScience.linear_head_profile_endpoints`: head values at `x = 0` and `x = L`.
- `EarthScience.linear_head_profile_hasDerivAt`: the head gradient is the constant slope.
- `EarthScience.darcy_flux_linear_head`: Darcy flux is the constant `-K * (hL - h0) / L`.
- `EarthScience.pore_velocity_linear_head`: pore velocity is `-K * (hL - h0) / (L * φ)`.

## iii. Table of contents

- A. Linear head profile and Darcy flux

## iv. References

- R. A. Freeze and J. A. Cherry, *Groundwater*, Prentice-Hall (1979),
  Chapter 2 (Physical Properties and Principles), for Darcy's law
  `q = -K dh/dl` and the average linear velocity `q / n`.
- `HasDerivAt.const_mul`, `HasDerivAt.div_const`, `HasDerivAt.const_add` in Mathlib.

## A. Linear head profile and Darcy flux
-/

@[expose] public section

namespace EarthScience

/-- Linear head profile: endpoints at `x = 0` and `x = L`. -/
theorem linear_head_profile_endpoints {h0 hL L : ℝ} (hLpos : 0 < L) :
    (h0 + (hL - h0) * 0 / L = h0) ∧
      (h0 + (hL - h0) * L / L = hL) := by
  have hLne : L ≠ 0 := ne_of_gt hLpos
  constructor
  · simp
  · field_simp
    ring

/-- Linear head profile: derivative is the constant slope `(hL - h0) / L`. -/
theorem linear_head_profile_hasDerivAt {h0 hL L x : ℝ} :
    HasDerivAt (fun x : ℝ => h0 + (hL - h0) * x / L) ((hL - h0) / L) x := by
  have hmul : HasDerivAt (fun x : ℝ => (hL - h0) * x) ((hL - h0) * 1) x :=
    (hasDerivAt_id x).const_mul (hL - h0)
  have hdiv : HasDerivAt (fun x : ℝ => (hL - h0) * x / L) ((hL - h0) * 1 / L) x :=
    hmul.div_const L
  have h := hdiv.const_add h0
  simpa using h

/-- Darcy flux for the linear head profile: `q = -K * h'` is the constant
`-K * (hL - h0) / L`. -/
theorem darcy_flux_linear_head {K h0 hL L : ℝ} :
    -K * ((hL - h0) / L) = -K * (hL - h0) / L := by
  ring

/-- Pore (average linear) velocity for the linear head profile:
`v = q / φ = -K * (hL - h0) / (L * φ)`. -/
theorem pore_velocity_linear_head {K h0 hL L phi : ℝ} (hLne : L ≠ 0) (hphine : phi ≠ 0) :
    (-K * (hL - h0) / L) / phi = -K * (hL - h0) / (L * phi) := by
  field_simp

end EarthScience
