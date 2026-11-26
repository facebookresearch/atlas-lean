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
The bounded outcome `snortMoverWins` is evaluated on the two graphs on two vertices: an
edge blocks the reply, two isolated vertices do not.
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

-- On the complete graph on two vertices, the first player's opening blocks the other vertex,
-- so the second player has no legal reply and the player to move wins.
example : snortMoverWins (⊤ : SimpleGraph (Fin 2)) 2 ∅ ∅ = true := by decide

-- On two isolated vertices the second player can always colour the other vertex, after which
-- the first player has no move, so the player to move loses.
example : snortMoverWins (⊥ : SimpleGraph (Fin 2)) 2 ∅ ∅ = false := by decide

end SnortOppositionsExistsLargeTreeSnortSecondPlayerWins
end MathlibExtTest.GraphTheory
