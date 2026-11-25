/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.InversionSequencePatternSets

open MetaMathlibExt

-- The empty inversion sequence avoids every pattern set.
example (B : Set (Fin 3 → ℕ)) : invSeqAvoidCount B 0 = 1 := by
  rw [invSeqAvoidCount, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun e f => Subtype.ext (funext fun i => Fin.elim0 i)⟩, ?_⟩
  exact ⟨⟨Fin.elim0, fun i => Fin.elim0 i,
    fun p _ => not_invSeqContainsPattern_of_lt (by decide) _ p⟩⟩

-- The second copy of the maximum switches sides of the smaller entry.
example : InvSeqContainsPattern (![0, 0, 2, 2, 1] : Fin 5 → ℕ) ![1, 1, 0] := by
  let f : Fin 3 → Fin 5 := ![2, 3, 4]
  refine ⟨OrderEmbedding.ofStrictMono f (by decide), ?_⟩
  decide

example : InvSeqContainsPattern (![0, 0, 2, 1, 2] : Fin 5 → ℕ) ![1, 0, 1] := by
  let f : Fin 3 → Fin 5 := ![2, 3, 4]
  refine ⟨OrderEmbedding.ofStrictMono f (by decide), ?_⟩
  decide
