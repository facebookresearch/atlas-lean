/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Parallel.GrahamBound
import Mathlib.Tactic.NormNum

@[expose] public section

/-- Two machines, total work 10, largest job 4: makespan at most 9. -/
example (M : ℝ) (h : 2 * (M - 4) < 10) : M ≤ 10 / 2 + 4 :=
  graham_bound 2 M 4 10 (by norm_num) h

/-- The same numbers give the `2 * OPT` form at `OPT = 5`. -/
example (M : ℝ) (h : 2 * (M - 4) < 10) : M ≤ 2 * 5 :=
  graham_two_approx 2 M 4 10 5 (by norm_num) h (by norm_num) (by norm_num)

end
