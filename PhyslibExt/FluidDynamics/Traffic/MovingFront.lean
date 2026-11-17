/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite moving-front conservation

## i. Overview

A two-state region split by a front moving at constant speed has
inventory `kL * (xi - a) + kR * (b - xi)` while the front lies inside
`[a, b]`. Its time derivative is the net inflow exactly when the
Rankine-Hugoniot balance `s * (kR - kL) = qR - qL` holds for the
constant states; `inventory_deriv_eq_iff_of_mem` states this under
the front-inside hypothesis.

## ii. Key results

- `FluidDynamics.Traffic.MovingFront.inventory_hasDerivAt`:
  inventory slope.
- `FluidDynamics.Traffic.MovingFront.inventory_deriv_eq_iff_of_mem`:
  conservation form with the front inside the interval.
- `FluidDynamics.Traffic.MovingFront.front_speed_eq_of_ne`: forced
  front speed.

## iii. Table of contents

- A. Moving-front inventory

## iv. References

- Federal Highway Administration, *Traffic Flow Theory* (moving
  front / shock accounting for constant states).

## A. Moving-front inventory
-/

@[expose] public section

namespace FluidDynamics.Traffic.MovingFront

/-- Vehicle inventory of a two-state region `a ≤ x ≤ b` split by a front
at `xi`: left density `kL` on `[a, xi]`, right density `kR` on `[xi, b]`. -/
noncomputable def inventory (kL kR a b xi : ℝ) : ℝ :=
  kL * (xi - a) + kR * (b - xi)

/-- For a front moving at constant speed, `xi t = s * t + xi0`, the
inventory is affine in time with slope `s * (kL - kR)`. -/
theorem inventory_hasDerivAt (kL kR a b s xi0 t : ℝ) :
    HasDerivAt (fun t => inventory kL kR a b (s * t + xi0))
      (s * (kL - kR)) t := by
  unfold inventory
  have hlin : HasDerivAt (fun t : ℝ => s * t + xi0) s t := by
    simpa using ((hasDerivAt_id' t).const_mul s).add_const xi0
  have h1 : HasDerivAt (fun t : ℝ => kL * (s * t + xi0 - a)) (kL * s) t :=
    (hlin.sub_const a).const_mul kL
  have h2 : HasDerivAt (fun t : ℝ => kR * (b - (s * t + xi0))) (kR * -s) t :=
    (hlin.const_sub b).const_mul kR
  have hadd := h1.add h2
  have heq : s * (kL - kR) = kL * s + kR * -s := by ring
  rw [heq]
  exact hadd

/-- Conservation form: the inventory derivative equals the net inflow
`qL - qR` exactly when `s * (kR - kL) = qR - qL` (the Rankine-Hugoniot
balance for these constant states). -/
private lemma inventory_deriv_eq_iff (kL kR a b s xi0 qL qR t : ℝ) :
    HasDerivAt (fun t => inventory kL kR a b (s * t + xi0)) (qL - qR) t
      ↔ s * (kR - kL) = qR - qL := by
  constructor
  · intro h
    have huniq := h.unique (inventory_hasDerivAt kL kR a b s xi0 t)
    linarith
  · intro h
    have heq : qL - qR = s * (kL - kR) := by linarith
    rw [heq]
    exact inventory_hasDerivAt kL kR a b s xi0 t

/-- When the two states differ, the front speed is forced to be the
Rankine-Hugoniot speed `(qR - qL) / (kR - kL)`. -/
theorem front_speed_eq_of_ne {kL kR s qL qR : ℝ} (h : kR ≠ kL)
    (hbal : s * (kR - kL) = qR - qL) : s = (qR - qL) / (kR - kL) := by
  have hne : kR - kL ≠ 0 := sub_ne_zero.mpr h
  rw [eq_div_iff hne]
  exact hbal

/-- Conservation form while the front lies inside the finite control
interval: under `a < s * t + xi0 < b`, the inventory derivative equals
the net inflow `qL - qR` exactly when the Rankine-Hugoniot balance
`s * (kR - kL) = qR - qL` holds. -/
theorem inventory_deriv_eq_iff_of_mem {kL kR a b s xi0 qL qR t : ℝ}
    (hin : a < s * t + xi0 ∧ s * t + xi0 < b) :
    HasDerivAt (fun t => inventory kL kR a b (s * t + xi0)) (qL - qR) t
      ↔ s * (kR - kL) = qR - qL := by
  have _ : a < b := lt_trans hin.1 hin.2
  exact inventory_deriv_eq_iff kL kR a b s xi0 qL qR t

end FluidDynamics.Traffic.MovingFront
