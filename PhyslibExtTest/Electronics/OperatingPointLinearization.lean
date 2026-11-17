/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electronics.OperatingPointLinearization
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Electronics.OperatingPointLinearization

namespace PhyslibExtTest.Electronics.OperatingPointLinearization

/-- The quadratic law attains the factor: at deviation `3` the
remainder of linearizing `v ↦ v^2` at `0` is exactly `9`. -/
example : smallSignalRemainder (fun v : Fin 1 → ℝ => (v 0) ^ 2) 0
    (fun _ => 3) = 9 := by
  rw [smallSignal_quadratic_attains_factor]; norm_num

/-- At zero deviation the remainder vanishes for the same law. -/
example : smallSignalRemainder (fun v : Fin 1 → ℝ => (v 0) ^ 2) 0
    (fun _ => 0) = 0 := by
  rw [smallSignal_quadratic_attains_factor]; norm_num

end PhyslibExtTest.Electronics.OperatingPointLinearization
