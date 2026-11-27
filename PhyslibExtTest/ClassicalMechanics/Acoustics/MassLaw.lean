/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.ClassicalMechanics.Acoustics.MassLaw

/-!
# Mass-law checks

Focused checks for `PhyslibExt.ClassicalMechanics.Acoustics.MassLaw`:
the split and the doubling law at `x = 1` (transmission loss
`10 * log10 2`, about 3.01 dB).

These are elaboration and non-vacuity checks, not new results.
-/

open Acoustics

/-- Split at `x = 1`. -/
example : 10 * Real.logb 10 (1 + (1 : ℝ) ^ 2)
    = 20 * Real.logb 10 1 + 10 * Real.logb 10 (1 + (1 : ℝ) ^ (-2 : ℤ)) :=
  (mass_law_comparison one_pos).1

/-- Doubling the asymptote at `x = 1`. -/
example : 20 * Real.logb 10 (2 * (1 : ℝ))
    = 20 * Real.logb 10 1 + 20 * Real.logb 10 2 :=
  (mass_law_comparison one_pos).2.2
