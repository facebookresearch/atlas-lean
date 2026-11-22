/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.ModelTheory.LabelledStructureCount
public import Mathlib.ModelTheory.Graph

/-!
# Tests for counting labelled finite structures

The language of graphs (one binary relation symbol) satisfies every hypothesis of the
zero-one law: it is relational, has finitely many symbols and no nullary relation symbol.
On it the proportion of structures satisfying `⊤` is `1` and the proportion satisfying
`∼⊤` is `0`, for every domain size, so the proportion is not degenerate.
-/

@[expose] public section

namespace MathlibExtTest.ModelTheory.LabelledStructureCount

open FirstOrder FirstOrder.Language

instance : Finite Language.graph.Symbols := by
  refine Finite.of_injective (β := Unit) (fun _ => ()) ?_
  rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩) (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩) _
  rfl

example : Language.graph.IsRelational := inferInstance

example : IsEmpty (Language.graph.Relations 0) := ⟨fun r => nomatch r⟩

example (n : ℕ) : Finite (Language.graph.Structure (Fin n)) :=
  Language.graph.finite_structure (Fin n)

theorem satFraction_top (n : ℕ) : Language.graph.satFraction ⊤ n = 1 := by
  have := Language.graph.finite_structure (Fin n)
  have := Language.graph.nonempty_structure (Fin n)
  have hpos : (0 : ℝ) < Nat.card (Language.graph.Structure (Fin n)) := by
    exact_mod_cast Nat.card_pos
  have hset : {S : Language.graph.Structure (Fin n) |
      @Sentence.Realize Language.graph (Fin n) S ⊤} = Set.univ := by
    ext S
    simp [Sentence.Realize, Formula.Realize]
  unfold satFraction
  rw [hset, Set.ncard_univ, div_self hpos.ne']

example (n : ℕ) : Language.graph.satFraction (∼⊤) n = 0 := by
  rw [satFraction_not, satFraction_top, sub_self]

end MathlibExtTest.ModelTheory.LabelledStructureCount
