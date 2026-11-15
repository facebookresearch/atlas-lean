/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.MisraGries

@[expose] public section

/-- Two distinct items fill the `k - 1 = 2` slots of `k = 3`. -/
example : mgRun 3 [0, 1] = ([(1, 1), (0, 1)], 0) := by decide

/-- A third distinct item finds the summary full: both counters drop to `0` and are removed in
one decrement round. -/
example : mgRun 3 [0, 1, 2] = ([], 1) := by decide

/-- The error bound is sharp there: item `0` has frequency `1` and counter `0`, the stored mass
is `0`, and `(1 - 0) * 3 = 3 - 0`. -/
example :
    (List.count 0 [0, 1, 2] - mgCounter (mgRun 3 [0, 1, 2]).1 0) * 3
      = [0, 1, 2].length - mgMass (mgRun 3 [0, 1, 2]).1 := by
  decide

/-- The theorems on the same run. -/
example :
    (List.count 0 [0, 1, 2] - mgCounter (mgRun 3 [0, 1, 2]).1 0) * 3
      ≤ [0, 1, 2].length - mgMass (mgRun 3 [0, 1, 2]).1 :=
  mg_error_bound 3 (by decide) [0, 1, 2] 0

example : (mgRun 3 [0, 1, 2]).2 * 3 + mgMass (mgRun 3 [0, 1, 2]).1 = [0, 1, 2].length :=
  mg_rounds_mul_add_mass 3 (by decide) [0, 1, 2]

/-- A stored item survives a decrement round with its counter one lower: item `0` occurs `3`
times, ends with counter `2` after `1` round, and `(3 - 2) * 3 = 5 - 2`. -/
example : mgRun 3 [0, 0, 1, 2, 0] = ([(0, 2)], 1) := by decide

example :
    (List.count 0 [0, 0, 1, 2, 0] - mgCounter (mgRun 3 [0, 0, 1, 2, 0]).1 0) * 3
      = [0, 0, 1, 2, 0].length - mgMass (mgRun 3 [0, 0, 1, 2, 0]).1 := by
  decide

/-- Items the summary never stored have counter `0`. -/
example : mgCounter (mgRun 3 [0, 0, 1, 2, 0]).1 1 = 0 := by decide

/-- With `k = 2` one counter is kept: item `0`, a majority with `3` of `5` occurrences, keeps
counter `1` after `2` rounds, and `(3 - 1) * 2 = 5 - 1`. -/
example : mgRun 2 [0, 1, 0, 2, 0] = ([(0, 1)], 2) := by decide

example :
    (List.count 0 [0, 1, 0, 2, 0] - mgCounter (mgRun 2 [0, 1, 0, 2, 0]).1 0) * 2
      = [0, 1, 0, 2, 0].length - mgMass (mgRun 2 [0, 1, 0, 2, 0]).1 := by
  decide

/-- With `k = 1` there are no slots, so every item is a decrement round. -/
example : mgRun 1 [0, 0, 1] = ([], 3) := by decide

/-- Items need only decidable equality, as in this run over strings with `k = 3`. -/
example : mgRun 3 ["a", "b", "a", "c", "a", "d", "b"] = ([("a", 1)], 2) := by decide

end
