/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Unicycle no-lateral-velocity identity

For the ideal unicycle trace equations `x' = v * cos θ` and
`y' = v * sin θ`, the lateral velocity
`-sin θ * x' + cos θ * y'` vanishes identically.
-/

@[expose] public section

namespace ControlTheory

/-- No-lateral-velocity identity for the ideal unicycle. If a
planar trace satisfies the ideal unicycle equations
`x' = v * cos θ` and `y' = v * sin θ` at a point (as
`HasDerivAt` values), then the lateral velocity of the
trace vanishes:
`-sin θ * x' + cos θ * y' = 0` for the actual derivatives
`deriv x t` and `deriv y t`. -/
theorem unicycle_no_lateral_velocity
    {x y θ : ℝ → ℝ} {t v : ℝ}
    (hx : HasDerivAt x (v * Real.cos (θ t)) t)
    (hy : HasDerivAt y (v * Real.sin (θ t)) t) :
    -Real.sin (θ t) * deriv x t
      + Real.cos (θ t) * deriv y t = 0 := by
  rw [hx.deriv, hy.deriv]
  ring

end ControlTheory
