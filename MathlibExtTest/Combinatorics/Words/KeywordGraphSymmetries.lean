/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.Combinatorics.Words.KeywordGraphSymmetries

namespace MetaMathlibExt.keywordGraph_neg_rev_seminegation

private abbrev keyword := ![false, false, false, true]
private abbrev before := ![true, false, false, false, true]
private abbrev after := ![true, true, true, true, false]

-- The same suffix substitution is an edge for the complemented keyword.
example : (keywordGraph (fun t => !keyword t) 5).Adj before after := by
  rw [← (keywordGraph_neg_rev_seminegation keyword 5).1]
  refine (keywordGraph_adj ..).mpr ⟨by decide, Or.inl ⟨1, ?_⟩⟩
  have applicable : KeywordApplicable keyword 1 before := ⟨by decide, Or.inl (by decide)⟩
  funext j
  rw [keywordSimpleMap_apply_of_applicable _ _ _ applicable]
  revert j
  decide

-- Reversal sends 0001 to 1000 and seminegation sends it to 0100.
example (n : ℕ) : Nonempty (keywordGraph ![true, false, false, false] n ≃g
    keywordGraph ![false, true, false, false] n) := by
  obtain ⟨_, ⟨revIso⟩, ⟨semiIso⟩⟩ := keywordGraph_neg_rev_seminegation keyword n
  have rev : (fun t => keyword t.rev) = ![true, false, false, false] := by decide
  have semi : (fun t => if t.val % 2 = 0 then keyword t else !keyword t) =
      ![false, true, false, false] := by decide
  rw [rev] at revIso
  rw [semi] at semiIso
  exact ⟨revIso.symm.trans semiIso⟩

-- At length zero the seminegation isomorphism fixes the unique empty word.
example (u : Fin 0 → Bool) :
    ∃ e : keywordGraph keyword 0 ≃g keywordGraph (fun t =>
      if t.val % 2 = 0 then keyword t else !keyword t) 0, e u = u := by
  obtain ⟨e⟩ := (keywordGraph_neg_rev_seminegation keyword 0).2.2
  exact ⟨e, Subsingleton.elim _ _⟩

end MetaMathlibExt.keywordGraph_neg_rev_seminegation
