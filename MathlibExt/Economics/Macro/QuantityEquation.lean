/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic

/-!
# The quantity equation is an identity

With velocity defined consistently as `V = P * Y / M` (nominal output divided
by the money supply) and nonzero money (`M ≠ 0`), the quantity equation
`M * V = P * Y` holds by cancellation. This is an identity following from the
definition: it does not claim velocity is constant, that money is neutral, or
any causal direction from `M` to `P`.

## Main results

* `quantityEquation`: `M * quantityVelocity M P Y = P * Y`.
* `priceLevel_from_quantity`: `P = M * V / Y` for `M ≠ 0` and `Y ≠ 0`.

## References

* I. Fisher, *The Purchasing Power of Money*, Macmillan (1911).

Atlas roadmap target MA05.T01.
-/

@[expose] public section

namespace MathlibExt.Economics.Macro.QuantityEquation

/-- Velocity of money, DEFINED consistently as `P * Y / M`: nominal output
divided by the money supply (source clause: "velocity defined consistently").
This is a definition, not a behavioural claim; it does not assert velocity is
constant. -/
noncomputable def quantityVelocity (M P Y : ℝ) : ℝ :=
  P * Y / M

/-- **The quantity equation is an identity.** With velocity defined as
`P * Y / M` and nonzero money (`M ≠ 0`), `M * V = P * Y` holds by
cancellation (Atlas roadmap MA05.T01). No constancy, neutrality, or causality
claim is made. -/
theorem quantityEquation (M P Y : ℝ) (hM : M ≠ 0) :
    M * quantityVelocity M P Y = P * Y := by
  unfold quantityVelocity
  exact mul_div_cancel₀ _ hM

/-- **Price level from the quantity equation.** With nonzero money and nonzero
real output, `P = M * V / Y`. -/
theorem priceLevel_from_quantity (M P Y : ℝ) (hM : M ≠ 0) (hY : Y ≠ 0) :
    P = M * quantityVelocity M P Y / Y := by
  have h := quantityEquation M P Y hM
  calc P = P * Y / Y := (mul_div_cancel_right₀ P hY).symm
    _ = M * quantityVelocity M P Y / Y := by rw [h]

end MathlibExt.Economics.Macro.QuantityEquation
