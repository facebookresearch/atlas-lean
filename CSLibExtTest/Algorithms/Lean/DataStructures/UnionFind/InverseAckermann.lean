/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.DataStructures.UnionFind.InverseAckermann
meta import CSLibExt.Algorithms.Lean.DataStructures.UnionFind.SequenceCost

/-!
# Tests for the inverse Ackermann bound

Check a run with no finds and a run with invalid calls and repeated path compression.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UnionByRank.InverseAckermannTests

private def makesOnly : List Op := [.makeSet, .makeSet]

private def compression : List Op :=
  [.find 0, .makeSet, .makeSet, .makeSet, .makeSet, .union 0 4,
    .union 0 1, .union 2 3, .union 1 3, .find 0, .find 0]

#guard (run makesOnly Batteries.UnionFind.empty).2 == 2
#guard numFinds makesOnly == 0
#guard (run compression Batteries.UnionFind.empty).2 == 20
#guard numMakeSet compression == 4
#guard numFinds compression == 11

example : ∃ C : ℕ, (run makesOnly Batteries.UnionFind.empty).2 ≤ C * numMakeSet makesOnly := by
  obtain ⟨C, hC⟩ := run_empty_cost_le_inverseAckermann
  exact ⟨C, by simpa [makesOnly, numMakeSet, numFinds] using hC makesOnly (by decide)⟩

example : ∃ C : ℕ, (run compression Batteries.UnionFind.empty).2 ≤
    C * (4 + 11 * inverseAckermannTvL 15 4) := by
  obtain ⟨C, hC⟩ := run_empty_cost_le_inverseAckermann
  exact ⟨C, hC compression (by decide)⟩

end Cslib.Algorithms.Lean.UnionByRank.InverseAckermannTests
