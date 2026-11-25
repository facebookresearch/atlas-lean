/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Soil unit weights

## i. Overview

Bulk unit weight `γ = (Gs + S * e) * γw / (1 + e)` from specific
gravity `Gs`, degree of saturation `S`, void ratio `e`, and water
unit weight `γw`; the submerged unit weight at full saturation is
`γ_sub = (Gs - 1) * γw / (1 + e)`, which is the saturated bulk
weight minus the water unit weight and is positive exactly when
`Gs > 1` (for positive `γw` and `1 + e > 0`).

## ii. Key results

- `EarthScience.submerged_eq_sat_sub_water`: submerged weight is
  saturated bulk weight minus water weight.
- `EarthScience.submerged_pos_iff`: positivity criterion `1 < Gs`.

## iii. Table of contents

- A. Unit-weight relations

## iv. References

- R. F. Craig, *Craig's Soil Mechanics*, 8th edition, Spon
  Press, 2012 (unit weights from the soil phase relations).
-/

@[expose] public section

namespace EarthScience

/-! ## A. Unit-weight relations -/

/-- Bulk unit weight of a soil element with specific gravity `Gs`,
degree of saturation `S`, void ratio `e`, and water unit weight
`γw`. The value is the declared total-weight-to-total-volume
convention `γ = (Gs + S * e) * γw / (1 + e)`, totalized as a real
division (no positivity is asserted by the definition itself): with
the convention `x / 0 = 0` it is `0` when `e = -1`. -/
noncomputable def bulkUnitWeight (Gs S e γw : ℝ) : ℝ :=
  (Gs + S * e) * γw / (1 + e)

/-- Submerged unit weight at full saturation, `γ_sub = (Gs - 1) * γw / (1 + e)`. With the convention
`x / 0 = 0` it is `0` when `e = -1`; the intended domain is `Gs > 0`, `e ≥ 0` and `γw > 0`. -/
noncomputable def submergedUnitWeight (Gs e γw : ℝ) : ℝ :=
  (Gs - 1) * γw / (1 + e)

/-- The submerged unit weight is the saturated bulk unit weight
minus the water unit weight, whenever `1 + e ≠ 0`. -/
theorem submerged_eq_sat_sub_water {Gs e γw : ℝ} (he : (1:ℝ) + e ≠ 0) :
    submergedUnitWeight Gs e γw
      = bulkUnitWeight Gs 1 e γw - γw := by
  unfold submergedUnitWeight bulkUnitWeight
  field_simp
  ring

/-- For positive water unit weight and `1 + e > 0`, the submerged
unit weight is positive exactly when the specific gravity exceeds
one; lighter solids (`Gs < 1`) do not give a positive submerged
weight. -/
theorem submerged_pos_iff {Gs e γw : ℝ} (hγ : 0 < γw) (he : 0 < 1 + e) :
    0 < submergedUnitWeight Gs e γw ↔ 1 < Gs := by
  unfold submergedUnitWeight
  rw [div_pos_iff_of_pos_right he, mul_pos_iff_of_pos_right hγ]
  exact sub_pos

end EarthScience
