/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.TwoVarLP
import Mathlib.Tactic.NormNum

@[expose] public section

/-- The origin satisfies `x ≤ 1`. -/
example : feasible [(1, 0, 1)] (0, 0) := by
  intro c hc
  simp at hc
  subst hc
  norm_num

end
