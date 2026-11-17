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
- `FluidDynamics.Traffic.greenshieldsFlux_half`: midpoint value at half
  the jam density.
- `FluidDynamics.Traffic.greenshieldsFlux_capacity_attained`: for positive
  free-flow speed, that value is the capacity and is attained.

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
  have hkj' : kj ≠ 0 := ne_of_gt hkj
  have h2 : k / kj ≤ 1 := (div_le_one hkj).mpr hk
  have h3 : 0 ≤ (1 : ℝ) - k / kj := sub_nonneg.mpr h2
  have hkey : vf * kj / 4 - vf * k * (1 - k / kj)
      = vf * (k - kj / 2) ^ 2 / kj := by
    field_simp
    ring
  have hnonneg : 0 ≤ vf * (k - kj / 2) ^ 2 / kj := by positivity
  refine ⟨?_, ?_⟩
  · show 0 ≤ vf * k * (1 - k / kj)
    exact mul_nonneg (mul_nonneg hvf.le hk0) h3
  · show vf * k * (1 - k / kj) ≤ vf * kj / 4
    linarith

/-- Midpoint value: at half the jam density the flux equals
`vf * kj / 4`. This is a value identity for any `vf`; it is capacity
attainment only under `0 < vf`, as in
`greenshieldsFlux_capacity_attained`. -/
lemma greenshieldsFlux_half {vf kj : ℝ} (hkj : 0 < kj) :
    greenshieldsFlux vf kj (kj / 2) = vf * kj / 4 := by
  have hkj' : kj ≠ 0 := ne_of_gt hkj
  show vf * (kj / 2) * (1 - kj / 2 / kj) = vf * kj / 4
  field_simp
  ring

/-- **Capacity attainment.** For positive free-flow speed, the value
`vf * kj / 4` is attained at half the jam density and bounds every flux on
the physical density range. -/
theorem greenshieldsFlux_capacity_attained {vf kj : ℝ} (hvf : 0 < vf)
    (hkj : 0 < kj) :
    greenshieldsFlux vf kj (kj / 2) = vf * kj / 4
      ∧ ∀ k : ℝ, 0 ≤ k → k ≤ kj →
        greenshieldsFlux vf kj k ≤ vf * kj / 4 := by
  exact ⟨greenshieldsFlux_half hkj,
    fun k hk0 hk => (greenshieldsFlux_nonneg_le hvf hkj hk0 hk).2⟩

end FluidDynamics.Traffic
