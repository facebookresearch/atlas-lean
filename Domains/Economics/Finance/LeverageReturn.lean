/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Modigliani–Miller II: the leverage identity

Value-weighted return accounting `(E + D) * rA = E * rE + D * rD` (the total
return on assets equals the value-weighted returns on equity and debt) gives,
when equity value `E` is nonzero, the leverage identity
`rE = rA + (D / E) * (rA - rD)`: equity holders earn the asset return plus a
leverage premium proportional to the debt–equity ratio. The weighted-average
cost of capital form says the value-weighted average of the equity and debt
returns is the asset return.

## Main results

* `MathlibExt.Economics.Finance.LeverageReturn.modiglianiMiller_II`: the
  leverage identity.
* `MathlibExt.Economics.Finance.LeverageReturn.wacc_eq_assetReturn`: the WACC
  form.

## References

F. Modigliani and M. H. Miller, "The Cost of Capital, Corporation Finance and
the Theory of Investment", American Economic Review 48(3), 1958. Atlas roadmap
target FI09.T02.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance.LeverageReturn

/-- **Modigliani–Miller II (leverage identity).** Value-weighted return accounting
`(E + D) * rA = E * rE + D * rD` (the total return on assets equals the
value-weighted returns on equity and debt) gives, when equity value `E` is nonzero,
the leverage identity `rE = rA + (D / E) * (rA - rD)`: equity holders earn the asset
return plus a leverage premium proportional to the debt–equity ratio. -/
theorem modiglianiMiller_II {E D rA rD rE : ℝ} (hE : E ≠ 0)
    (haccount : (E + D) * rA = E * rE + D * rD) :
    rE = rA + (D / E) * (rA - rD) := by
  field_simp
  linarith

/-- Weighted-average cost of capital form: under the same accounting identity and a
nonzero total firm value, the value-weighted average of the equity and debt returns
is the asset return. -/
theorem wacc_eq_assetReturn {E D rA rD rE : ℝ} (hV : E + D ≠ 0)
    (haccount : (E + D) * rA = E * rE + D * rD) :
    (E / (E + D)) * rE + (D / (E + D)) * rD = rA := by
  field_simp
  linarith

end MathlibExt.Economics.Finance.LeverageReturn
