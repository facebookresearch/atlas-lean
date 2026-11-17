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
inventory `kL * (xi - a) + kR * (b - xi)`. Its time derivative is the
net inflow exactly when the Rankine-Hugoniot balance
`s * (kR - kL) = qR - qL` holds for the constant states.

## ii. Key results

- `MovingFront.inventory_hasDerivAt`: inventory slope.
- `MovingFront.inventory_deriv_eq_iff`: conservation form.
- `MovingFront.front_speed_eq_of_ne`: forced front speed.

## iii. Table of contents

- A. Moving-front inventory

## iv. References

- Federal Highway Administration, *Traffic Flow Theory* (moving
  front / shock accounting for constant states).

## A. Moving-front inventory
-/

@[expose] public section

namespace MovingFront

/-- Vehicle inventory of a two-state region `a ≤ x ≤ b` split by a front
at `xi`: left density `kL` on `[a, xi]`, right density `kR` on `[xi, b]`. -/
noncomputable def inventory (kL kR a b xi : ℝ) : ℝ :=
  kL * (xi - a) + kR * (b - xi)

/-- For a front moving at constant speed, `xi t = s * t + xi0`, the
inventory is affine in time with slope `s * (kL - kR)`. -/
theorem inventory_hasDerivAt (kL kR a b s xi0 t : ℝ) :
    HasDerivAt (fun t => inventory kL kR a b (s * t + xi0))
      (s * (kL - kR)) t := by
  have hxi : HasDerivAt (fun t : ℝ => s * t + xi0) s t := by
    have h := HasDerivAt.add_const xi0 (HasDerivAt.const_mul s (hasDerivAt_id t))
    simpa using h
  have hleft_inner : HasDerivAt (fun t : ℝ => (s * t + xi0) - a) s t :=
    HasDerivAt.sub_const a hxi
  have hleft : HasDerivAt (fun t : ℝ => kL * ((s * t + xi0) - a)) (kL * s) t :=
    HasDerivAt.const_mul kL hleft_inner
  have hright_inner : HasDerivAt (fun t : ℝ => b - (s * t + xi0)) (-s) t :=
    HasDerivAt.const_sub b hxi
  have hright : HasDerivAt (fun t : ℝ => kR * (b - (s * t + xi0))) (kR * (-s)) t :=
    HasDerivAt.const_mul kR hright_inner
  have hsum := HasDerivAt.add hleft hright
  simp only [inventory] at hsum ⊢
  convert hsum using 2
  ring

/-- Conservation form: the inventory derivative equals the net inflow
`qL - qR` exactly when `s * (kR - kL) = qR - qL` (the Rankine-Hugoniot
balance for these constant states). -/
theorem inventory_deriv_eq_iff (kL kR a b s xi0 qL qR t : ℝ) :
    HasDerivAt (fun t => inventory kL kR a b (s * t + xi0)) (qL - qR) t
      ↔ s * (kR - kL) = qR - qL := by
  constructor
  · intro h
    have h0 := inventory_hasDerivAt kL kR a b s xi0 t
    have heq : qL - qR = s * (kL - kR) := HasDerivAt.unique h h0
    linear_combination heq
  · intro hbal
    have h0 := inventory_hasDerivAt kL kR a b s xi0 t
    have heq : s * (kL - kR) = qL - qR := by linear_combination -hbal
    rwa [heq] at h0

/-- When the two states differ, the front speed is forced to be the
Rankine-Hugoniot speed `(qR - qL) / (kR - kL)`. -/
theorem front_speed_eq_of_ne {kL kR s qL qR : ℝ} (h : kR ≠ kL)
    (hbal : s * (kR - kL) = qR - qL) : s = (qR - qL) / (kR - kL) := by
  have hne : kR - kL ≠ 0 := sub_ne_zero.mpr h
  rw [eq_div_iff hne]
  exact hbal

end MovingFront
