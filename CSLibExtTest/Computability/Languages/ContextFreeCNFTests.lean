/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.ChomskyNormalForm
public import CSLibExt.Computability.Languages.ContextFree.NonClosure

/-!
# Ordinary-client tests for Chomsky normal form
-/

public section

namespace Cslib.Language.ContextFreeCNFTests

/-- The `a^n b^n` language has a Chomsky-normal-form grammar
generating it, and sample words (including the empty word) survive
the conversion. -/
theorem anbn_cnf_example :
    ∃ g : ContextFreeGrammar (Fin 3),
      IsChomskyNormalForm g ∧
      ([] : List (Fin 3)) ∈ g.language ∧
      ([0, 1] : List (Fin 3)) ∈ g.language ∧
      ([0, 0, 1, 1] : List (Fin 3)) ∈ g.language ∧
      ([0, 1, 1] : List (Fin 3)) ∉ g.language := by
  obtain ⟨g, hg, hcnf⟩ :=
    IsContextFree.exists_chomskyNormalForm (eqPowLang_isContextFree
      (0 : Fin 3) 1)
  refine ⟨g, hcnf, ?_, ?_, ?_, ?_⟩ <;> rw [hg]
  · exact ⟨0, rfl⟩
  · exact ⟨1, by decide⟩
  · exact ⟨2, by decide⟩
  · rintro ⟨n, hn⟩
    have hlen : ([0, 1, 1] : List (Fin 3)).length =
        (List.replicate n (0 : Fin 3) ++
          List.replicate n (1 : Fin 3)).length := by rw [hn]
    simp only [List.length_append, List.length_replicate] at hlen
    have h3 : 3 = n + n := hlen
    omega

/-- Every grammar in this test file's favorite one-rule shape is in
Chomsky normal form. -/
theorem epsOnly_isChomskyNormalForm :
    IsChomskyNormalForm (g := (⟨Unit, (), {⟨(), []⟩}⟩ :
      ContextFreeGrammar Bool)) := by
  constructor
  · intro r hr
    simp only [Finset.mem_singleton] at hr
    subst hr
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · left
    intro r hr
    simp only [Finset.mem_singleton] at hr
    subst hr
    simp

end Cslib.Language.ContextFreeCNFTests
