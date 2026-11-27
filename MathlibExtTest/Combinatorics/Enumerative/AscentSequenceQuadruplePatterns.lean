/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.List.Sublists
import MathlibExt.Combinatorics.Enumerative.AscentSequenceQuadruplePatterns

namespace MetaMathlibExt.isBigEntry_succ_or_descent

private abbrev patterns : Finset (List ℕ) := {[0, 1, 1], [1, 0, 0], [2, 0, 1], [2, 1, 0]}

private theorem example_mem : [0, 1, 0, 2, 3] ∈ weakAscentAvoiders patterns 5 := by
  refine ⟨rfl, by unfold IsWeakAscentSeq; decide, ?_⟩
  have h : ∀ p ∈ patterns, ∀ s ∈ [0, 1, 0, 2, 3].sublistsLen p.length,
      ¬ (∀ i < p.length, ∀ j < p.length, s.getD i 0 < s.getD j 0 ↔ p.getD i 0 < p.getD j 0) := by
    decide
  rintro p hp ⟨s, hs, hlen, hord⟩
  exact h p hp s (List.mem_sublistsLen.mpr ⟨hs, hlen⟩) hord

-- The descent at position two forces both remaining entries, including the final one.
example : IsBigEntry [0, 1, 0, 2, 3] 3 ∧ IsBigEntry [0, 1, 0, 2, 3] 4 := by
  have h := isBigEntry_succ_or_descent 5 _ example_mem 2 (by decide) (by decide) (by decide)
  obtain ⟨_, htail⟩ := h.resolve_left (by decide)
  exact ⟨htail 4 (by decide) (by decide), htail 5 (by decide) (by decide)⟩

-- At the last possible descent top, the same word instead has a big successor.
example : IsBigEntry [0, 1, 0, 2, 3] 4 := by
  apply (isBigEntry_succ_or_descent 5 _ example_mem 4 (by decide) (by decide) (by decide)).elim
  · exact id
  · rintro ⟨hlt, _⟩
    exact absurd hlt (by decide)

-- Neither the initial position nor a default value beyond the word can witness a big entry.
example : ¬ IsBigEntry [0, 1] 0 ∧ ¬ IsBigEntry [0, 1] 2 := by decide

end MetaMathlibExt.isBigEntry_succ_or_descent
