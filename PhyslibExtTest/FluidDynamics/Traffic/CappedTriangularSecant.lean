/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.FluidDynamics.Traffic.CappedTriangularSecant
import Mathlib.Tactic.NormNum

/-!
# Secant-bound checks

Focused checks for
`PhyslibExt.FluidDynamics.Traffic.CappedTriangularSecant`: a
rising-branch secant attains the upper slope `v = 2`, and the
theorem applies at a plateau pair.

These are elaboration and non-vacuity checks, not new results.
-/

/-- Rising branch: secant slope equals `v = 2`. -/
example : (min (2 * (2 : ℝ)) (min (3 * (10 - 2)) 5)
      - min (2 * 1) (min (3 * (10 - 1)) 5)) / (2 - 1) = 2 := by
  norm_num

/-- The bounds hold at a plateau pair. -/
example : -3 ≤ (min (2 * (7 : ℝ)) (min (3 * (10 - 7)) 5)
        - min (2 * 6) (min (3 * (10 - 6)) 5)) / (7 - 6)
    ∧ (min (2 * (7 : ℝ)) (min (3 * (10 - 7)) 5)
        - min (2 * 6) (min (3 * (10 - 6)) 5)) / (7 - 6) ≤ 2 :=
  FluidDynamics.Traffic.capped_triangular_secant_bounds (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num [Set.mem_Icc])
    (by norm_num [Set.mem_Icc]) (by norm_num)
