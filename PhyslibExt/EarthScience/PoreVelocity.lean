/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity

/-!
# Pore velocity and Courant number

## i. Overview

Darcy discharge per bulk area `q` and porosity `n` give the pore
(seepage) velocity `q / n`; the two are different quantities and
this module records only the kinematic conversion. The Courant
number for time step `dt` and cell width `dx` is the
dimensionless expression `|q / n| * dt / dx`; no stability of any
numerical scheme is asserted.

## ii. Key results

- `EarthScience.poreVelocity_quarter`: porosity `1 / 4`
  multiplies the Darcy speed by four.
- `EarthScience.courantNumber_nonneg`: the Courant number is
  nonnegative for `dt ≥ 0` and `dx > 0`.
- `EarthScience.courantNumber_zero_dt`: a zero time step has
  Courant number zero.

## iii. Table of contents

- A. Pore velocity and Courant number

## iv. References

- J. Bear, *Dynamics of Fluids in Porous Media*, 1972
  (Darcy flux versus pore velocity).
-/

@[expose] public section

namespace EarthScience

/-! ## A. Pore velocity and Courant number -/

/-- Pore (seepage) velocity from Darcy discharge per bulk area `q`
and porosity `n`: `v = q / n`. The Darcy flux and pore velocity are
different quantities; this definition records only the kinematic
conversion. With the convention `x / 0 = 0`, it is `0` when `n = 0`. -/
noncomputable def poreVelocity (q n : ℝ) : ℝ := q / n

/-- Courant number for pore velocity `q / n`, time step `dt`, and
cell width `dx`: `|q / n| * dt / dx`. This is only the dimensionless
expression; it does not assert stability of any numerical scheme.
With the convention `x / 0 = 0`, it is `0` when `n = 0` or `dx = 0`. -/
noncomputable def courantNumber (q n dt dx : ℝ) : ℝ :=
  |q / n| * dt / dx

/-- A porosity of one quarter multiplies the Darcy speed by four. -/
lemma poreVelocity_quarter (q : ℝ) :
    poreVelocity q (1 / 4) = 4 * q := by
  unfold poreVelocity
  rw [div_eq_mul_inv, one_div, inv_inv, mul_comm]

/-- The pore velocity recovers the Darcy discharge when multiplied
back by a nonzero porosity. -/
lemma poreVelocity_mul {q n : ℝ} (hn : n ≠ 0) :
    poreVelocity q n * n = q := by
  unfold poreVelocity
  exact div_mul_cancel₀ q hn

/-- For every `q` and `n`, the Courant number is nonnegative for a nonnegative time step and
positive cell width. At `n = 0` it is `0`, by the convention `x / 0 = 0`. -/
lemma courantNumber_nonneg {q n dt dx : ℝ} (hdt : 0 ≤ dt)
    (hdx : 0 < dx) : 0 ≤ courantNumber q n dt dx := by
  unfold courantNumber
  positivity

/-- A zero time step has Courant number zero (also at `dx = 0`, by the
convention `x / 0 = 0`). -/
lemma courantNumber_zero_dt (q n dx : ℝ) :
    courantNumber q n 0 dx = 0 := by
  unfold courantNumber
  simp

end EarthScience
