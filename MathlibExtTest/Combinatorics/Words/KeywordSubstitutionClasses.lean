/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.Combinatorics.Words.KeywordSubstitutionClasses

namespace MetaMathlibExt.KeywordSubstitutionClasses

-- The last two letters match the negated keyword. Flipping them preserves total bit parity.
private abbrev keyword := ![true, false]
private abbrev before := ![true, false, true]
private abbrev after := ![true, true, false]

private theorem flip_suffix : keywordSimpleMap keyword 1 before = after := by
  have ha : KeywordApplicable keyword 1 before := ⟨by decide, Or.inr (by decide)⟩
  funext j
  rw [keywordSimpleMap_apply_of_applicable keyword 1 before ha]
  revert j
  decide

example : ∃ c : (keywordGraph keyword 3).Coloring (Fin 2), c before ≠ c after := by
  obtain ⟨c⟩ := keywordGraph_isBipartite keyword 3
  exact ⟨c, c.valid ((keywordGraph_adj ..).mpr ⟨by decide, Or.inl ⟨1, flip_suffix⟩⟩)⟩

example : KeywordEquiv keyword before after :=
  Relation.ReflTransGen.single ⟨1, flip_suffix⟩

-- Index 2 overruns the word, so the second map fixes the result of the first.
example : keywordListApply keyword [1, 2] before = after ∧
    ¬ KeywordActsCompletely keyword [1, 2] before := by
  have h : ¬ KeywordApplicable keyword 2 after := fun ⟨h, _⟩ => by omega
  simp [keywordListApply, KeywordActsCompletely, flip_suffix,
    keywordSimpleMap_of_not_applicable keyword 2 after h]

-- The in-bounds prefix of the result matches neither the keyword nor its negation.
example : keywordSimpleMap keyword 0 after = after := by
  apply keywordSimpleMap_of_not_applicable
  rintro ⟨_, h | h⟩
  · exact Bool.noConfusion (h 1)
  · exact Bool.noConfusion (h 0)

-- The empty word has no incident edge.
example {m : ℕ} (a : Fin (m + 1) → Bool) (u v : Fin 0 → Bool) : ¬ (keywordGraph a 0).Adj u v :=
  fun h => h.ne (Subsingleton.elim u v)

end MetaMathlibExt.KeywordSubstitutionClasses
