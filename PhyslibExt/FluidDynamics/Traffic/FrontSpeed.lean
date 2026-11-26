/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.FluidDynamics.Traffic.FundamentalDiagram
public import PhyslibExt.FluidDynamics.Traffic.ShockOrdering

/-!
# Greenshields shock speed

## i. Overview

With the Greenshields flux `greenshieldsFlux vf kj` (free-flow
speed `vf`, jam density `kj`), the shock speed between two
distinct densities is the Rankine-Hugoniot secant
`ShockOrdering.shockSpeed (greenshieldsFlux vf kj) kL kR`, and it
specializes to `vf * (1 - (kL + kR) / kj)`. For complementary
densities `kL + kR = kj` the front is stationary.

## ii. Key results

- `FluidDynamics.Traffic.greenshields_shock_speed`: the shock
  speed specialization for distinct states.

## iii. Table of contents

- A. Shock speed

## iv. References

- Standard traffic-flow theory (Greenshields fundamental diagram
  and shock-wave speed).
-/

@[expose] public section

namespace FluidDynamics.Traffic

/-! ## A. Shock speed -/

/-- Greenshields shock speed between two distinct states. With
the Greenshields flux `greenshieldsFlux vf kj`, the shock speed
`ShockOrdering.shockSpeed (greenshieldsFlux vf kj) kL kR` between
distinct densities `kL ≠ kR` (with `kj ≠ 0`) is
`vf * (1 - (kL + kR) / kj)`. For complementary densities
(`kL + kR = kj`) the front is stationary. -/
theorem greenshields_shock_speed {vf kj kL kR : ℝ} (hkj : kj ≠ 0)
    (hdist : kL ≠ kR) :
    ShockOrdering.shockSpeed (greenshieldsFlux vf kj) kL kR
      = vf * (1 - (kL + kR) / kj) := by
  unfold ShockOrdering.shockSpeed greenshieldsFlux
  have hne : kR - kL ≠ 0 := sub_ne_zero.mpr (Ne.symm hdist)
  field_simp
  ring


end FluidDynamics.Traffic
