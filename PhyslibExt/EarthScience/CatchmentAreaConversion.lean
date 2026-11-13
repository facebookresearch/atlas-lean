/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Catchment budget: closing after area and time conversion

A catchment budget is usually stated in depths (precipitation, evaporation
and runoff as depths per time), but storage is a volume. Multiplying by
the catchment area converts every depth term to a volume, and the budget
closes exactly.

## i. Overview

With catchment area `A`, a depth `d` is the volume `A * d` and a depth
rate `r` is the volume flux `A * r`. A depth flux times a duration is a
depth, so area times that depth equals the volume flux times the
duration. Depth in millimetres converts to metres by dividing by 1000
before area multiplication, and a daily depth rate agrees with the
hourly rate over `24 * n` hours. The volume budget closes: if the depth
storage change satisfies `ds = (p - e - q) * dt`, then
`A * ds + (A * e) * dt + (A * q) * dt = (A * p) * dt`.

## ii. Key results

- `EarthScience.catchmentVolume`, `EarthScience.catchmentVolumeFlux`:
  area conversion of depths and depth rates.
- `EarthScience.catchment_volume_flux_time`: a flux times a duration,
  converted by area.
- `EarthScience.catchment_volume_mm_to_m`: millimetre-to-metre conversion.
- `EarthScience.catchment_budget_closes`: the volume budget closes.
- `EarthScience.catchment_volume_daily_hourly`: daily/hourly agreement.

## iii. References

- `ring` for the conversion and budget identities.
-/

@[expose] public section

namespace EarthScience

/-- Volume from catchment area `A` and a depth `d`: `A * d`. -/
noncomputable def catchmentVolume (A d : ℝ) : ℝ := A * d

/-- Volume flux from area `A` and a depth rate `r` (depth per time): `A * r`. -/
noncomputable def catchmentVolumeFlux (A r : ℝ) : ℝ := A * r

/-- Area conversion: a depth flux times a duration gives a depth, and
area times that depth is the volume. -/
theorem catchment_volume_flux_time (A r dt : ℝ) :
    catchmentVolume A (r * dt) = catchmentVolumeFlux A r * dt := by
  unfold catchmentVolume catchmentVolumeFlux
  ring

/-- Depth in millimetres converts to metres by dividing by 1000 before
area multiplication. -/
theorem catchment_volume_mm_to_m (A d_mm : ℝ) :
    catchmentVolume A (d_mm / 1000) = A * d_mm / 1000 := by
  unfold catchmentVolume
  ring

/-- The catchment budget closes after area conversion: if the depth
storage change satisfies `ds = (p - e - q) * dt`, then the volume budget
`A * ds + (A * e) * dt + (A * q) * dt = (A * p) * dt` holds. -/
theorem catchment_budget_closes (A p e q dt ds : ℝ)
    (h : ds = (p - e - q) * dt) :
    catchmentVolume A ds + catchmentVolumeFlux A e * dt
      + catchmentVolumeFlux A q * dt = catchmentVolumeFlux A p * dt := by
  rw [h]
  unfold catchmentVolume catchmentVolumeFlux
  ring

/-- Time conversion: a daily depth rate over `n` days gives the same
volume as the hourly rate over `24 * n` hours. -/
theorem catchment_volume_daily_hourly (A r_day n : ℝ) :
    catchmentVolumeFlux A (r_day / 24) * (24 * n)
      = catchmentVolumeFlux A r_day * n := by
  unfold catchmentVolumeFlux
  ring

end EarthScience
