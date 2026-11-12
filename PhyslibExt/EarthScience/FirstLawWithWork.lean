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
# First law with work: temperature change under the physics sign convention

With the physics sign convention `ΔU = Q - W` (heat `Q` added to the
system, work `W` done by the system) and constant heat capacity
`ΔU = C * (T1 - T0)`, `C > 0`, the temperature change is `(Q - W) / C`.

## i. Overview

This generalizes the isochoric `W = 0` case proved in
`PhyslibExt.EarthScience.ThermodynamicsState`: the work term enters the
energy balance, and the same field arithmetic gives the temperature
change. Volume is not assumed fixed here; only the two balance
relations and `C > 0` are used.

## ii. Key results

- `EarthScience.firstLaw_temperature_change`: `T1 - T0 = (Q - W) / C`.
- `EarthScience.firstLaw_final_temperature`: `T1 = T0 + (Q - W) / C`.

## iii. References

- Field arithmetic in Mathlib (`field_simp`, `linear_combination`).
-/

@[expose] public section

namespace EarthScience

/-- First law with the physics sign convention `ΔU = Q - W` (heat `Q` added to
the system, work `W` done by the system) and constant heat capacity
`ΔU = C * (T1 - T0)`, `C > 0`: the temperature change is `(Q - W) / C`. -/
theorem firstLaw_temperature_change {C Q W U0 U1 T0 T1 : ℝ} (hC : 0 < C)
    (hfirst : U1 - U0 = Q - W) (hconst : U1 - U0 = C * (T1 - T0)) :
    T1 - T0 = (Q - W) / C := by
  have hC' : C ≠ 0 := ne_of_gt hC
  have h : Q - W = C * (T1 - T0) := by linarith
  field_simp
  linarith

/-- First-law heating with work: under the same hypotheses the final
temperature is `T0 + (Q - W) / C`. -/
theorem firstLaw_final_temperature {C Q W U0 U1 T0 T1 : ℝ} (hC : 0 < C)
    (hfirst : U1 - U0 = Q - W) (hconst : U1 - U0 = C * (T1 - T0)) :
    T1 = T0 + (Q - W) / C := by
  have h := firstLaw_temperature_change hC hfirst hconst
  linarith

end EarthScience
