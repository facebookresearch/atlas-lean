/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Paul Bendich
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.StrongChromaticNumber

@[expose] public section

open Classical

namespace MathlibExtTest.Combinatorics.SimpleGraph.StrongChromaticNumber

open MetaMathlibExt

-- Combinatorics 496: Strongly k-colorable

lemma K1_strong : (⊤ : SimpleGraph (Fin 1)).IsStronglyColorable 1 := by
  intro P _; exact ⟨⟨fun _ => 0, by simp⟩, by simp⟩

-- Combinatorics 499: Strong Chromatic Number

lemma sChi_le_card {V} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
   G.sChi ≤ Fintype.card V :=
  Nat.sInf_le fun _ _ => ⟨⟨Fintype.equivFin V, fun h => (Fintype.equivFin V).injective.ne h.ne⟩, by simp⟩

end MathlibExtTest.Combinatorics.SimpleGraph.StrongChromaticNumber

end
