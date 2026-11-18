/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Greenshields front speed

## i. Overview

With free-flow speed `vf`, jam density `kj`, and the Greenshields
flux `q(k) = k * vf * (1 - k / kj)`, the moving-front speed between
two distinct densities is the Rankine-Hugoniot quotient
`(q(kR) - q(kL)) / (kR - kL) = vf * (1 - (kL + kR) / kj)`. For
complementary densities `kL + kR = kj` the front is stationary.

## ii. Key results

- `greenshields_front_speed`: the front-speed specialization for
  distinct states.

## iii. Table of contents

- A. Front speed

## iv. References

- Standard traffic-flow theory (Greenshields fundamental diagram
  and shock-wave speed).
-/

@[expose] public section

/-! ## A. Front speed -/

/-- Greenshields front speed between two distinct states. With
free-flow speed `vf`, jam density `kj ≠ 0`, and the Greenshields
flux `q(k) = k * vf * (1 - k / kj)`, the moving-front (shock) speed
between distinct densities `kL ≠ kR` is
`s = (q(kR) - q(kL)) / (kR - kL) = vf * (1 - (kL + kR) / kj)`.
For complementary densities (`kL + kR = kj`) the front is
stationary. -/
theorem greenshields_front_speed {vf kj kL kR : ℝ} (hkj : kj ≠ 0)
    (hdist : kL ≠ kR) :
    (kR * (vf * (1 - kR / kj)) - kL * (vf * (1 - kL / kj)))
        / (kR - kL)
      = vf * (1 - (kL + kR) / kj) := by
  have hne : kR - kL ≠ 0 := sub_ne_zero.mpr (Ne.symm hdist)
  rw [div_eq_iff hne]
  field_simp
  simp only [mul_sub, mul_add, mul_comm, mul_left_comm] at *
  have h_inner : vf * (kL * kR) + vf * (kR * kR) - (vf * (kL * kL) + vf * (kL * kR))
      = vf * (kR * kR) - vf * (kL * kL) := by
    rw [add_comm (vf * (kL * kL)) (vf * (kL * kR))]
    exact add_sub_add_left_eq_sub _ _ _
  rw [h_inner]
  simp only [sub_eq_add_neg, neg_add, neg_neg, add_assoc, add_comm, add_left_comm]
