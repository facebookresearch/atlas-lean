/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.FluidDynamics.Traffic.FundamentalDiagram
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Characteristic versus vehicle speed

## i. Overview

For the Greenshields flux `q(k) = vf * k * (1 - k / kj)`, the
characteristic (kinematic wave) speed `q'(k) = vf * (1 - 2 * k / kj)`
differs from the vehicle speed, the Greenshields constitutive
speed `v(k) = vf * (1 - k / kj)`, which satisfies `q(k) = k * v(k)`
for every `k` and equals the quotient `q(k) / k` for `k ≠ 0`:
they agree at zero density, and the characteristic speed is
negative for `k > kj / 2` while vehicles still move forward.

## ii. Key results

- `FluidDynamics.Traffic.greenshields_characteristicSpeed`: the
  derivative of the Greenshields flux.
- `FluidDynamics.Traffic.greenshields_speeds_at_jam`,
  `FluidDynamics.Traffic.greenshields_speeds_at_zero`: the two
  speeds at jam and zero density.
- `FluidDynamics.Traffic.greenshields_characteristicSpeed_neg`:
  negative characteristic speed above half jam density.

## iii. Table of contents

- A. Characteristic and vehicle speeds

## iv. References

- M. J. Lighthill and G. B. Whitham, *On kinematic waves II*,
  Proceedings of the Royal Society A, 1955 (characteristic speed
  of traffic flow).
-/

@[expose] public section

namespace FluidDynamics.Traffic

/-! ## A. Characteristic and vehicle speeds -/

/-- Vehicle speed under the Greenshields closure. -/
noncomputable def greenshieldsVehicleSpeed (vf kj k : ℝ) : ℝ :=
  vf * (1 - k / kj)

/-- Characteristic speed: derivative of the Greenshields flux. -/
theorem greenshields_characteristicSpeed {vf kj : ℝ} (hkj : 0 < kj) :
    deriv (greenshieldsFlux vf kj) = fun k => vf * (1 - 2 * k / kj) := by
  have hkj' : kj ≠ 0 := ne_of_gt hkj
  have hfun : greenshieldsFlux vf kj = fun k => vf * k - (vf / kj) * k ^ 2 := by
    funext k
    show vf * k * (1 - k / kj) = vf * k - (vf / kj) * k ^ 2
    field_simp
  rw [hfun]
  funext k
  have e1 : HasDerivAt (fun k : ℝ => vf * k) vf k := hasDerivAt_const_mul vf
  have e2 : HasDerivAt (fun k : ℝ => (vf / kj) * k ^ 2) ((vf / kj) * (2 * k)) k := by
    have h := (hasDerivAt_pow 2 k).const_mul (vf / kj)
    simpa using h
  have hderiv : HasDerivAt (fun k : ℝ => vf * k - (vf / kj) * k ^ 2)
      (vf - (vf / kj) * (2 * k)) k := e1.sub e2
  rw [hderiv.deriv]
  field_simp

/-- At jam density the vehicle speed is zero while the
characteristic speed is `-vf`. -/
theorem greenshields_speeds_at_jam {vf kj : ℝ} (hkj : 0 < kj) :
    greenshieldsVehicleSpeed vf kj kj = 0
      ∧ vf * (1 - 2 * kj / kj) = -vf := by
  have hkj' : kj ≠ 0 := ne_of_gt hkj
  constructor
  · show vf * (1 - kj / kj) = 0
    rw [div_self hkj']
    ring
  · field_simp
    ring

/-- The two speeds agree at zero density. -/
theorem greenshields_speeds_at_zero {vf kj : ℝ} :
    greenshieldsVehicleSpeed vf kj 0 = vf
      ∧ vf * (1 - 2 * (0 : ℝ) / kj) = vf := by
  constructor
  · show vf * (1 - (0 : ℝ) / kj) = vf
    simp
  · simp

/-- For densities above half of jam, the characteristic speed is
negative while the vehicle speed stays positive. -/
theorem greenshields_characteristicSpeed_neg {vf kj k : ℝ}
    (hvf : 0 < vf) (hkj : 0 < kj) (h1 : kj / 2 < k) (h2 : k < kj) :
    vf * (1 - 2 * k / kj) < 0 ∧ 0 < greenshieldsVehicleSpeed vf kj k := by
  have hlt : (1 : ℝ) < 2 * k / kj := by
    rw [one_lt_div hkj]
    linarith
  have hlt2 : k / kj < (1 : ℝ) := by
    rw [div_lt_one hkj]
    exact h2
  constructor
  · have hneg : (1 : ℝ) - 2 * k / kj < 0 := by linarith
    calc vf * (1 - 2 * k / kj) < vf * 0 := mul_lt_mul_of_pos_left hneg hvf
      _ = 0 := mul_zero vf
  · show (0 : ℝ) < vf * (1 - k / kj)
    have hpos : (0 : ℝ) < 1 - k / kj := by linarith
    exact mul_pos hvf hpos

end FluidDynamics.Traffic
