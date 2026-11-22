/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.FluidDynamics.Traffic.SignalQueueArea

/-!
# Queue-area checks

Focused checks for `PhyslibExt.FluidDynamics.Traffic.SignalQueueArea`:
`lam = 1`, `mu = 3`, `R = G = 2` gives area 3, and `R = 0` gives 0.

These are elaboration and non-vacuity checks, not new results.
-/

open FluidDynamics.Traffic.SignalQueue

/-- Area 3 for `lam = 1`, `mu = 3`, `R = G = 2`. -/
example : ∫ t in (0)..(2 + 2), queueLen 1 3 2 t = 3 := by
  have h := queueLen_integral_cycle (lam := 1) (mu := 3) (R := 2) (G := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [h]
  norm_num

/-- Zero red time gives zero area. -/
example : ∫ t in (0)..(0 + 2), queueLen 1 3 0 t = 0 := by
  have h := queueLen_integral_cycle (lam := 1) (mu := 3) (R := 0) (G := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [h]
  norm_num
