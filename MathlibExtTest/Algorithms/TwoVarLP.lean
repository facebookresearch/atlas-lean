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

open MathlibExt.Algorithms.TwoVarLP

/-- The origin satisfies `x ≤ 1`. -/
example : feasible [(1, 0, 1)] (0, 0) := by
  intro c hc
  simp at hc
  subst hc
  norm_num

/-- The point `(2, 0)` violates `x ≤ 1`. -/
example : ¬ feasible [(1, 0, 1)] (2, 0) := by
  intro h
  have h1 := h (1, 0, 1) (by simp)
  norm_num at h1

/-- Dropping a constraint keeps a point feasible. -/
example {cs : List (ℚ × ℚ × ℚ)} {c : ℚ × ℚ × ℚ} {p : ℚ × ℚ}
    (h : feasible (c :: cs) p) : feasible cs p :=
  feasible_mono h fun _ hd => List.mem_cons_of_mem c hd

/-- A point feasible for `x ≤ 1` and the appended `y ≤ 2` has `y ≤ 2`. -/
example {p : ℚ × ℚ} (h : feasible ([(1, 0, 1)] ++ [(0, 1, 2)]) p) :
    p.2 ≤ 2 := by
  simpa using feasible_new_constraint (0, 1, 2) h

end
