/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GraphTheory.SnortOppositionsExistsLargeTreeSnortSecondPlayerWins

/-!
# Tests for large Snort second-player-winning trees

The existence theorem supplies a tree with at least one hundred vertices and
implies that a winning tree can be chosen with more vertices than any given bound.
-/

namespace MathlibExtTest.GraphTheory
namespace SnortOppositionsExistsLargeTreeSnortSecondPlayerWins

open MetaMathlibExt

example : ∃ n ≥ 100, ∃ T : SimpleGraph (Fin n), ∃ _ : DecidableRel T.Adj,
    T.IsTree ∧ SnortSecondPlayerWins T :=
  exists_large_tree_snortSecondPlayerWins 100

example (N : ℕ) : ∃ n > N, ∃ T : SimpleGraph (Fin n), ∃ _ : DecidableRel T.Adj,
    T.IsTree ∧ SnortSecondPlayerWins T := by
  obtain ⟨n, hn, T, hdec, htree, hwin⟩ := exists_large_tree_snortSecondPlayerWins (N + 1)
  exact ⟨n, by omega, T, hdec, htree, hwin⟩

end SnortOppositionsExistsLargeTreeSnortSecondPlayerWins
end MathlibExtTest.GraphTheory
