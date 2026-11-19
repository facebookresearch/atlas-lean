/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Macro.LinearPolicy

@[expose] public section

namespace MathlibExtTest.Economics.Macro.LinearPolicy

open MathlibExt.Economics.Macro.LinearPolicy Matrix

/-- The second eigenvalue equation at the concrete parameters:
`d = 1/3` has eigenvector `![1/4, -1/6]`. -/
example : linearPolicyMatrix (1 / 2 : ℝ) (1 / 4) (1 / 3) *ᵥ ![1 / 4, -1 / 6] =
    (1 / 3 : ℝ) • ![1 / 4, -1 / 6] := by
  ext i
  fin_cases i
  · simp [linearPolicyMatrix, Matrix.mulVec]
    norm_num
  · simp [linearPolicyMatrix, Matrix.mulVec]

end MathlibExtTest.Economics.Macro.LinearPolicy
