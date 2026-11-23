/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Isochoric heating at constant heat capacity: temperature change is Q / C

## i. Overview

For an isochoric closed model with constant heat capacity `C > 0`
and `dU = C * dT`, the energy balance `U1 - U0 = Q` together with the
constitutive relation `U1 - U0 = C * (T1 - T0)` gives the temperature
change `T1 - T0 = Q / C`. Volume is fixed; there is no work, phase
change, or mass exchange. `U`, `Q` are energies, `C` energy per kelvin;
heat is a transfer, not a state function.

## ii. Key results

- `EarthScience.isochoric_temperature_change`: `T1 - T0 = Q / C`.
- `EarthScience.isochoric_heating`: heating by `Q` moves `T` to `T0 + Q / C`.
- `EarthScience.isochoric_zero_heating`: zero input gives zero change.

## iii. Table of contents

- A. Temperature change from the energy balance
- B. Heating and the zero-input case

## iv. References

- Field arithmetic in Mathlib (`field_simp`, `linear_combination`).
-/

@[expose] public section

namespace EarthScience

/-- Isochoric closed model with constant heat capacity `C > 0` and
`dU = C * dT`: if the energy balance is `U1 - U0 = Q` and the
constitutive relation is `U1 - U0 = C * (T1 - T0)`, then the temperature
change is `Q / C`. -/
theorem isochoric_temperature_change {C Q U0 U1 T0 T1 : ℝ} (hC : 0 < C)
    (hbalance : U1 - U0 = Q) (hconst : U1 - U0 = C * (T1 - T0)) :
    T1 - T0 = Q / C := by
  have hC' : C ≠ 0 := ne_of_gt hC
  have h : Q = C * (T1 - T0) := hbalance.symm.trans hconst
  field_simp
  linarith

/-- Heating: with the energy balance `U1 - U0 = Q`, the constitutive
relation `U1 - U0 = C * (T1 - T0)`, and heat input `0 ≤ Q`, the final
state satisfies `U1 = U0 + Q` and `T1 = T0 + Q / C`, so the energy
rises by `Q`. -/
theorem isochoric_heating {C Q U0 U1 T0 T1 : ℝ} (hC : 0 < C) (_hQ : 0 ≤ Q)
    (hbalance : U1 - U0 = Q) (hconst : U1 - U0 = C * (T1 - T0)) :
    U1 = U0 + Q ∧ T1 = T0 + Q / C := by
  constructor
  · linarith
  · have h := isochoric_temperature_change hC hbalance hconst
    linarith

/-- Zero heat input gives zero temperature change in the same model. -/
theorem isochoric_zero_heating {C U0 U1 T0 T1 : ℝ} (hC : 0 < C)
    (hbalance : U1 - U0 = 0) (hconst : U1 - U0 = C * (T1 - T0)) :
    T1 = T0 := by
  have hC' : C ≠ 0 := ne_of_gt hC
  have h : C * (T1 - T0) = 0 := hconst.symm.trans hbalance
  have h2 : T1 - T0 = 0 := (mul_eq_zero.mp h).resolve_left hC'
  linarith

end EarthScience
