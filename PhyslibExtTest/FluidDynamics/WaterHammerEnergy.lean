/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.FluidDynamics.WaterHammerEnergy

/-!
# Water-hammer energy checks

Focused checks for `PhyslibExt.FluidDynamics.WaterHammerEnergy`: a
constant state `h = 2`, `q = 0` (with all partials zero) satisfies
the hypotheses, and the theorem gives energy derivative
`2 * 0 - 2 * 0 = 0` at every time.

These are elaboration and non-vacuity checks, not new results.
-/

open FluidDynamics.WaterHammerEnergy

/-- Constant-state application of the public theorem. -/
example (t : ℝ) : HasDerivAt (fun s => ∫ x in (0:ℝ)..(1:ℝ),
      (1 * 1 / (1:ℝ)^2) * (2:ℝ)^2 / 2 + (0:ℝ)^2 / (2 * 1 * 1))
    (2 * 0 - 2 * 0) t :=
  energy_hasDerivAt (a := 1) (g := 1) (A := 1) (L := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ _ => 2) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
    (fun _ _ => 0) (fun _ _ => 0)
    (fun t x _ => hasDerivAt_const t (2:ℝ))
    (fun t x _ => hasDerivAt_const t (0:ℝ))
    (fun s x _ => HasDerivAt.hasDerivWithinAt (hasDerivAt_const x (2:ℝ)))
    (fun s x _ => HasDerivAt.hasDerivWithinAt (hasDerivAt_const x (0:ℝ)))
    (fun t x _ => by norm_num)
    (fun t x _ => by norm_num)
    (by fun_prop)
    (by fun_prop)
    t
