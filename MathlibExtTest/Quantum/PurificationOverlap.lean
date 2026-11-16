/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.PurificationOverlap

@[expose] public section

/-- Identical point masses have Bhattacharyya coefficient 1. -/
example : bhattC (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => 1) = 1 := by
  simp [bhattC]

end
