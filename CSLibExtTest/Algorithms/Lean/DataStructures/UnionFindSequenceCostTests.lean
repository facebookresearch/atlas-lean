/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.UnionFind.SequenceCost
public meta import CSLibExt.Algorithms.Lean.DataStructures.UnionFind.SequenceCost

/-!
# Tests for the cost of set-union operation sequences

Values of the Tarjan–van Leeuwen Ackermann function (Remark 2: `A(3, 1) = 16`), the cost of a
small sequence computed by hand, and the logarithmic bound applied to it.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UnionByRankSequenceTests

open UnionByRank

#guard ackermannTvL 1 5 == 32
#guard ackermannTvL 2 1 == 4
#guard ackermannTvL 2 2 == 16
#guard ackermannTvL 3 1 == 16

/-- Four make-sets, unions `{0, 1}`, `{2, 3}` and of the two pairs, then a find on `1`. -/
def ops : List Op :=
  [.makeSet, .makeSet, .makeSet, .makeSet, .union 0 1, .union 2 3, .union 0 2, .find 1]

#guard numMakeSet ops == 4
#guard numFinds ops == 7
-- Costs `4` (make-sets) `+ 3 + 3` (first unions) `+ 5` (paths of one edge, then a link)
-- `+ 2` (find on `1`, one edge to the new root).
#guard (run ops Batteries.UnionFind.empty).2 == 17

/-- The logarithmic bound on this sequence: `17 ≤ 4 + 7 · (2 + 2)`. -/
example : (run ops Batteries.UnionFind.empty).2 ≤
    numMakeSet ops + numFinds ops * (Nat.log 2 (numMakeSet ops) + 2) :=
  run_empty_cost_le_log ops

end Cslib.Algorithms.Lean.UnionByRankSequenceTests
