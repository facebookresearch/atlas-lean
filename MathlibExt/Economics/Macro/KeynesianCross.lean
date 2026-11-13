/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Keynesian-cross multiplier

At fixed prices, planned expenditure is `E = A + c * Y` and equilibrium is `Y = E`.
With `0 ≤ c < 1` the equilibrium output is `Y = A / (1 - c)`, and two equilibria differ
by the multiplier times the change in autonomous expenditure.

## Main results

* `MathlibExt.Economics.Macro.KeynesianCross.keynesianCross_solution`: equilibrium output.
* `MathlibExt.Economics.Macro.KeynesianCross.keynesianCross_multiplier`: multiplier form.
-/

namespace MathlibExt.Economics.Macro.KeynesianCross

/-- The linear Keynesian-cross equilibrium condition at fixed prices: output `Y` equals
autonomous expenditure `A` plus induced consumption `c * Y`, where `c` is the marginal
propensity to consume. The price level is not in the model (fixed-price assumption) and `A`
is exogenous. -/
def IsKeynesianEquilibrium (c A Y : ℝ) : Prop :=
  Y = A + c * Y

/-- **Keynesian multiplier (MA06.T01).** If `0 ≤ c < 1` and `Y` satisfies the
Keynesian-cross equilibrium condition, then `Y = A / (1 - c)`. The multiplier is
`1 / (1 - c)`: each unit of autonomous expenditure supports `1 / (1 - c)` units of output.
This solves a scalar linear equation with field algebra; it is not a new fixed-point theorem. -/
theorem keynesianCross_solution {c A Y : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (h : IsKeynesianEquilibrium c A Y) : Y = A / (1 - c) := by
  have _hc := hc
  unfold IsKeynesianEquilibrium at h
  have hne : (1 : ℝ) - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt hc1)
  field_simp
  linear_combination h

/-- **Multiplier form (MA06.T01).** Two equilibria with the same `c` differ by the multiplier
times the change in autonomous expenditure: `Y₂ - Y₁ = (A₂ - A₁) / (1 - c)`. -/
theorem keynesianCross_multiplier {c A₁ A₂ Y₁ Y₂ : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (h₁ : IsKeynesianEquilibrium c A₁ Y₁) (h₂ : IsKeynesianEquilibrium c A₂ Y₂) :
    Y₂ - Y₁ = (A₂ - A₁) / (1 - c) := by
  have _hc := hc
  unfold IsKeynesianEquilibrium at h₁ h₂
  have hne : (1 : ℝ) - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt hc1)
  field_simp
  linear_combination h₂ - h₁

end MathlibExt.Economics.Macro.KeynesianCross
