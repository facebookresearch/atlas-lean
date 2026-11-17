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

- `ShockOrdering.shockSpeed_between_of_concave`: the ordering.
- `ShockOrdering.shockSpeed_strict_between_of_strictConcave`: the
  strict form.

## iii. Table of contents

- A. Shock ordering

## iv. References

- M. J. Lighthill and G. B. Whitham, kinematic waves, 1955; Lax
  entropy condition for concave fluxes.

## A. Shock ordering
-/

@[expose] public section

namespace ShockOrdering


/-- Shock speed between two densities: the secant slope of the flux. -/
noncomputable def shockSpeed (q : ℝ → ℝ) (kL kR : ℝ) : ℝ :=
  (q kR - q kL) / (kR - kL)

/-- For a concave flux differentiable on all of `ℝ`, with
`kL < kR`, the shock speed lies between the characteristic speeds at
the endpoints: `q'(kR) ≤ s ≤ q'(kL)`. -/
theorem shockSpeed_between_of_concave {q : ℝ → ℝ}
    (hconc : ConcaveOn ℝ Set.univ q)
    (hdiff : ∀ x : ℝ, HasDerivAt q (deriv q x) x)
    {kL kR : ℝ} (h : kL < kR) :
    deriv q kR ≤ shockSpeed q kL kR ∧ shockSpeed q kL kR ≤ deriv q kL := by
  have e : shockSpeed q kL kR = slope q kL kR := by
    simp only [shockSpeed, slope_def_field]
  rw [e]
  exact ⟨hconc.deriv_le_slope (Set.mem_univ kL) (Set.mem_univ kR) h
    (hdiff kR).differentiableAt,
    hconc.slope_le_deriv (Set.mem_univ kL) (Set.mem_univ kR) h
    (hdiff kL).differentiableAt⟩

/-- Strict form under strict concavity on the interval: both
inequalities are strict. -/
theorem shockSpeed_strict_between_of_strictConcave {q : ℝ → ℝ}
    (hconc : StrictConcaveOn ℝ Set.univ q)
    (hdiff : ∀ x : ℝ, HasDerivAt q (deriv q x) x)
    {kL kR : ℝ} (h : kL < kR) :
    deriv q kR < shockSpeed q kL kR ∧ shockSpeed q kL kR < deriv q kL := by
  have e : shockSpeed q kL kR = slope q kL kR := by
    simp only [shockSpeed, slope_def_field]
  rw [e]
  exact ⟨hconc.deriv_lt_slope (Set.mem_univ kL) (Set.mem_univ kR) h
    (hdiff kR).differentiableAt,
    hconc.slope_lt_deriv (Set.mem_univ kL) (Set.mem_univ kR) h
    (hdiff kL).differentiableAt⟩

end ShockOrdering
