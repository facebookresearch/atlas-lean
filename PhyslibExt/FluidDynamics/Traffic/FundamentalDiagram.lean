/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Greenshields fundamental diagram

## i. Overview

The Greenshields model of homogeneous traffic takes the mean speed to
decrease linearly in density, `v(k) = vf * (1 - k / kj)`, giving the flux
`q(k) = vf * k * (1 - k / kj)` for free-flow speed `vf > 0` and jam density
`kj > 0`, in a fixed lane and unit convention. This module records its
range on the physical density interval and its capacity. It is an
empirical closure (a kinematic-wave continuum model), not a claim about
any particular calibrated road.

## ii. Key results

- `FluidDynamics.Traffic.greenshieldsFlux`: the Greenshields flux function.
- `FluidDynamics.Traffic.greenshieldsFlux_nonneg_le`: the flux on
  `0 ≤ k ≤ kj` is between `0` and the capacity `vf * kj / 4`.
- `FluidDynamics.Traffic.greenshieldsFlux_half`: capacity is attained at
  half the jam density.

## iii. Table of contents

- A. Flux, range, and capacity

## iv. References

- B. D. Greenshields, a study of traffic capacity, 1935 (linear
  speed–density relation).
-/

@[expose] public section

namespace FluidDynamics.Traffic

/-! ## A. Flux, range, and capacity -/

/-- Greenshields traffic flux at density `k`, with free-flow speed `vf` and
jam density `kj`: `q(k) = vf * k * (1 - k / kj)`. This is the linear
speed–density empirical closure of the Greenshields fundamental diagram,
in a fixed lane and unit convention; it is physically meaningful for
`0 < vf`, `0 < kj`, and `0 ≤ k ≤ kj`. -/
noncomputable def greenshieldsFlux (vf kj k : ℝ) : ℝ :=
  vf * k * (1 - k / kj)

/-- **Greenshields flux range.** On the physical density range
`0 ≤ k ≤ kj`, the Greenshields flux is nonnegative and at most the capacity
`vf * kj / 4`. -/
theorem greenshieldsFlux_nonneg_le {vf kj k : ℝ} (hvf : 0 < vf)
    (hkj : 0 < kj) (hk0 : 0 ≤ k) (hk : k ≤ kj) :
    0 ≤ greenshieldsFlux vf kj k ∧ greenshieldsFlux vf kj k ≤ vf * kj / 4 := by
  unfold greenshieldsFlux
  have hkj_ne : kj ≠ 0 := ne_of_gt hkj
  have h1 : 0 ≤ 1 - k / kj := by
    have hdiv : k / kj ≤ 1 := (div_le_one hkj).mpr hk
    linarith
  refine ⟨mul_nonneg (mul_nonneg hvf.le hk0) h1, ?_⟩
  have hsq : 0 ≤ (kj - 2 * k) ^ 2 := sq_nonneg _
  have hcap : k * (kj - k) ≤ kj ^ 2 / 4 := by nlinarith [hsq]
  have hdecomp : vf * k * (1 - k / kj) = vf / kj * (k * (kj - k)) := by
    field_simp
  have hvfkj : 0 ≤ vf / kj := le_of_lt (div_pos hvf hkj)
  have hmul : vf / kj * (k * (kj - k)) ≤ vf / kj * (kj ^ 2 / 4) :=
    mul_le_mul_of_nonneg_left hcap hvfkj
  have heq : vf / kj * (kj ^ 2 / 4) = vf * kj / 4 := by
    field_simp
  calc vf * k * (1 - k / kj) = vf / kj * (k * (kj - k)) := hdecomp
    _ ≤ vf / kj * (kj ^ 2 / 4) := hmul
    _ = vf * kj / 4 := heq

/-- The Greenshields capacity `vf * kj / 4` is attained at half the jam
density. -/
lemma greenshieldsFlux_half {vf kj : ℝ} (hkj : 0 < kj) :
    greenshieldsFlux vf kj (kj / 2) = vf * kj / 4 := by
  have hkj_ne : kj ≠ 0 := ne_of_gt hkj
  unfold greenshieldsFlux
  field_simp
  ring

end FluidDynamics.Traffic
