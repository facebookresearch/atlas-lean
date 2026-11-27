/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.WythoffTerminalPositions

namespace MetaMathlibExt.WythoffTerminalPositionsTest

-- Zero has an empty word, and the leading digit at a Fibonacci number is the only one set.
example : fibRep 0 = [] ∧ fibRep 8 = [true, false, false, false, false] := by decide

-- Extra places in the fixed-width greedy representation contribute leading zeros.
example : fibGreedyDigits 4 2 = [false, false, true, false] := by decide

-- At the terminal boundary both orders of (0, 1) have no moves.
example (q : ℕ × ℕ) :
    ¬wythoffTerminalMove 1 (0, 1) q ∧ ¬wythoffTerminalMove 1 (1, 0) q :=
  ⟨not_wythoffTerminalMove_of_terminal (by decide) q,
    not_wythoffTerminalMove_of_terminal (by decide) q⟩

private abbrev Listed (p : ℕ × ℕ) : Prop :=
  p.1 + p.2 ≤ 1 ∨
    (p.1 ≤ p.2 ∧ (fibRep p.1).getLast? = some false ∧ fibRep p.2 = fibRep p.1 ++ [true]) ∨
    (p.2 ≤ p.1 ∧ (fibRep p.2).getLast? = some false ∧ fibRep p.1 = fibRep p.2 ++ [true])

example : Listed (0, 0) ∧ Listed (0, 1) ∧ Listed (1, 0) ∧ ¬Listed (1, 1) := by decide

-- Stability applies to the first nonterminal pair with its coordinates reversed.
example (q : ℕ × ℕ) (hm : wythoffTerminalMove 1 (4, 2) q) : ¬Listed q :=
  wythoffTerminal_one_fibRep.1 _ _ (by decide : Listed (4, 2)) hm

example : ∃ q, wythoffTerminalMove 1 (3, 5) q ∧ Listed q :=
  wythoffTerminal_one_fibRep.2 _ (by decide : ¬Listed (3, 5))

-- From (3, 5) one can reach the first nonterminal pair by taking one from each pile.
example : wythoffTerminalMove 1 (3, 5) (2, 4) ∧ fibRep 4 = fibRep 2 ++ [true] :=
  ⟨⟨by decide, Or.inr (Or.inr ⟨1, by decide⟩)⟩, by decide⟩

end MetaMathlibExt.WythoffTerminalPositionsTest
