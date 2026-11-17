/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Slope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Concave-flux shock-speed ordering

## i. Overview

For a concave traffic flux, the shock (secant) speed between two
densities `kL < kR` lies between the characteristic speeds at the
endpoints; under strict concavity both inequalities are strict (the
Lax entropy condition for increasing-density shocks).

## ii. Key results

- `FluidDynamics.Traffic.ShockOrdering.shockSpeed_between_of_concave`: the ordering.
- `FluidDynamics.Traffic.ShockOrdering.shockSpeed_strict_between_of_strictConcave`: the
  strict form.

## iii. Table of contents

- A. Shock ordering

## iv. References

- M. J. Lighthill and G. B. Whitham, kinematic waves, 1955; Lax
  entropy condition for concave fluxes.

## A. Shock ordering
-/

@[expose] public section

namespace FluidDynamics.Traffic.ShockOrdering

/-- Shock speed between two densities: the secant slope of the flux. -/
noncomputable def shockSpeed (q : ℝ → ℝ) (kL kR : ℝ) : ℝ :=
  (q kR - q kL) / (kR - kL)

/-- For a flux concave on the closed interval `[kL, kR]` and
differentiable at the endpoints, the shock speed lies between the
characteristic speeds: `q'(kR) ≤ s ≤ q'(kL)`. -/
theorem shockSpeed_between_of_concave {q : ℝ → ℝ} {kL kR : ℝ}
    (hconc : ConcaveOn ℝ (Set.Icc kL kR) q)
    (hL : HasDerivAt q (deriv q kL) kL)
    (hR : HasDerivAt q (deriv q kR) kR)
    (h : kL < kR) :
    deriv q kR ≤ shockSpeed q kL kR ∧ shockSpeed q kL kR ≤ deriv q kL := by
  have hx : kL ∈ Set.Icc kL kR := ⟨le_refl _, le_of_lt h⟩
  have hy : kR ∈ Set.Icc kL kR := ⟨le_of_lt h, le_refl _⟩
  have hR' := hconc.le_slope_of_hasDerivAt hx hy h hR
  have hL' := hconc.slope_le_of_hasDerivAt hx hy h hL
  rw [slope_def_field] at hR' hL'
  unfold shockSpeed
  exact ⟨hR', hL'⟩

/-- Strict form under strict concavity on the interval: both
inequalities are strict (Lax entropy condition). -/
theorem shockSpeed_strict_between_of_strictConcave {q : ℝ → ℝ} {kL kR : ℝ}
    (hconc : StrictConcaveOn ℝ (Set.Icc kL kR) q)
    (hL : HasDerivAt q (deriv q kL) kL)
    (hR : HasDerivAt q (deriv q kR) kR)
    (h : kL < kR) :
    deriv q kR < shockSpeed q kL kR ∧ shockSpeed q kL kR < deriv q kL := by
  have hx : kL ∈ Set.Icc kL kR := ⟨le_refl _, le_of_lt h⟩
  have hy : kR ∈ Set.Icc kL kR := ⟨le_of_lt h, le_refl _⟩
  have hR' := hconc.lt_slope_of_hasDerivAt hx hy h hR
  have hL' := hconc.slope_lt_of_hasDerivAt hx hy h hL
  rw [slope_def_field] at hR' hL'
  unfold shockSpeed
  exact ⟨hR', hL'⟩

end FluidDynamics.Traffic.ShockOrdering
