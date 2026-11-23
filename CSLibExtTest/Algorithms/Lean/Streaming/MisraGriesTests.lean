/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Streaming.MisraGries

/-!
# Tests for Misra-Gries heavy hitters

Concrete runs checked with `decide`: a full summary emptied by one decrement round, a stored
item surviving a round, the `k = 2` majority case, `k = 1`, and a string stream, together with
the error bound and the round identity on concrete streams.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.MisraGriesTests

open Cslib.Algorithms.Lean.MisraGries

/-- Two distinct items fill the `k - 1 = 2` slots of `k = 3`. -/
example : run 3 [0, 1] = ([(1, 1), (0, 1)], 0) := by decide

/-- A third distinct item finds the summary full: both counters drop to `0` and are removed in
one decrement round. -/
example : run 3 [0, 1, 2] = ([], 1) := by decide

/-- The error bound is sharp there: item `0` has frequency `1` and counter `0`, the stored mass
is `0`, and `(1 - 0) * 3 = 3 - 0`. -/
example :
    (List.count 0 [0, 1, 2] - counter (run 3 [0, 1, 2]).1 0) * 3
      = [0, 1, 2].length - mass (run 3 [0, 1, 2]).1 := by
  decide

/-- The theorems on the same run. -/
example :
    (List.count 0 [0, 1, 2] - counter (run 3 [0, 1, 2]).1 0) * 3
      ≤ [0, 1, 2].length - mass (run 3 [0, 1, 2]).1 :=
  error_bound 3 [0, 1, 2] 0

example : (run 3 [0, 1, 2]).2 * 3 + mass (run 3 [0, 1, 2]).1 = [0, 1, 2].length :=
  rounds_mul_add_mass 3 (by decide) [0, 1, 2]

/-- A stored item survives a decrement round with its counter one lower: item `0` occurs `3`
times, ends with counter `2` after `1` round, and `(3 - 2) * 3 = 5 - 2`. -/
example : run 3 [0, 0, 1, 2, 0] = ([(0, 2)], 1) := by decide

example :
    (List.count 0 [0, 0, 1, 2, 0] - counter (run 3 [0, 0, 1, 2, 0]).1 0) * 3
      = [0, 0, 1, 2, 0].length - mass (run 3 [0, 0, 1, 2, 0]).1 := by
  decide

/-- Item `1` was stored, then dropped by the decrement round, so its counter is `0`. -/
example : counter (run 3 [0, 0, 1, 2, 0]).1 1 = 0 := by decide

/-- An item that never occurs has counter `0`. -/
example : counter (run 3 [0, 0, 1, 2, 0]).1 3 = 0 := by decide

/-- With `k = 2` one counter is kept: item `0`, a majority with `3` of `5` occurrences, ends
with counter `1` after `2` rounds, and `(3 - 1) * 2 = 5 - 1`. -/
example : run 2 [0, 1, 0, 2, 0] = ([(0, 1)], 2) := by decide

example :
    (List.count 0 [0, 1, 0, 2, 0] - counter (run 2 [0, 1, 0, 2, 0]).1 0) * 2
      = [0, 1, 0, 2, 0].length - mass (run 2 [0, 1, 0, 2, 0]).1 := by
  decide

/-- With `k = 1` there are no slots, so every item is a decrement round. -/
example : run 1 [0, 0, 1] = ([], 3) := by decide

/-- The error bound and the round identity at `k = 1`. -/
example :
    (List.count 0 [0, 0, 1] - counter (run 1 [0, 0, 1]).1 0) * 1
      ≤ [0, 0, 1].length - mass (run 1 [0, 0, 1]).1 :=
  error_bound 1 [0, 0, 1] 0

example : (run 1 [0, 0, 1]).2 * 1 + mass (run 1 [0, 0, 1]).1 = [0, 0, 1].length :=
  rounds_mul_add_mass 1 (by decide) [0, 0, 1]

/-- Items need only decidable equality, as in this run over strings with `k = 3`. -/
example : run 3 ["a", "b", "a", "c", "a", "d", "b"] = ([("a", 1)], 2) := by decide

end Cslib.Algorithms.Lean.MisraGriesTests

end
