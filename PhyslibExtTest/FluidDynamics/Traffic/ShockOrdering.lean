/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.FluidDynamics.Traffic.ShockOrdering

/-!
# Shock-ordering checks

Focused checks for `PhyslibExt.FluidDynamics.Traffic.ShockOrdering`:
the shock speed of the quadratic flux `q(k) = k * (1 - k)` between
densities `0` and `1 / 2` is `3 / 4` by computation, and the public
ordering theorems apply to it (concavity of the quadratic on `ℝ` is
standard; here the checked content is the secant value and that the
theorem's hypotheses are the ones used).

These are elaboration and non-vacuity checks, not new results.
-/

open ShockOrdering

/-- The secant value on the quadratic flux, by computation. -/
example : shockSpeed (fun k : ℝ => k * (1 - k)) 0 (1 / 2) = 1 / 2 := by
  rw [shockSpeed]
  norm_num

/-- The ordering theorems elaborate on the quadratic flux with its
standard concavity/differentiability facts. -/
example (hconc : ConcaveOn ℝ Set.univ (fun k : ℝ => k * (1 - k)))
    (hdiff : ∀ x : ℝ, HasDerivAt (fun k : ℝ => k * (1 - k))
      (deriv (fun k : ℝ => k * (1 - k)) x) x) :
    deriv (fun k : ℝ => k * (1 - k)) (1 / 2)
      ≤ shockSpeed (fun k : ℝ => k * (1 - k)) 0 (1 / 2)
    ∧ shockSpeed (fun k : ℝ => k * (1 - k)) 0 (1 / 2)
      ≤ deriv (fun k : ℝ => k * (1 - k)) 0 :=
  shockSpeed_between_of_concave hconc hdiff (by norm_num)
