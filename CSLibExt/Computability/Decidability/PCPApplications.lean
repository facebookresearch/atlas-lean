/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Undecidable problems about context-free grammars
-/
module

public import CSLibExt.Computability.Decidability.PCPUndecidable
public import CSLibExt.Computability.Decidability.PCPAmbiguity
public import CSLibExt.Computability.Decidability.PCPUniversality

/-!
# Undecidable problems about context-free grammars

PCP is undecidable over a finite alphabet (`exists_not_tm2Decidable_pcp`), so the problems it
reduces to are undecidable too:

* whether two context-free languages intersect, and whether they are disjoint
  (`exists_not_tm2Decidable_overlap`, `exists_not_tm2Decidable_disjoint`, via
  `Grammar.manyOneReducible_pcp_inter`);
* whether a context-free grammar is ambiguous (`exists_not_tm2Decidable_isAmbiguous`, via
  `Grammar.manyOneReducible_pcp_isAmbiguous`);
* whether a context-free grammar generates every word (`exists_not_tm2Decidable_univ`, via
  `Grammar.manyOneReducible_not_pcp_univ`);
* whether two context-free grammars are equivalent, and whether one language is included in
  another (`exists_not_tm2Decidable_language_eq`, `exists_not_tm2Decidable_language_le`): compare
  with the grammar `allWordsCFG` of all words.

Grammars are `Cslib.Language.EncodedCFG`s, over some alphabet (finite in the last statement).

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, §5.1
  (`ALL_CFG`, `EQ_CFG`) and the Chapter 5 problems on `AMBIG_CFG` and `OVERLAP_CFG`.
* J. E. Hopcroft, R. Motwani, J. D. Ullman, *Introduction to Automata Theory, Languages, and
  Computation*, 3rd ed., Pearson, 2006, §9.5.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability

open Cslib.Language Grammar

/-- **Whether two context-free languages intersect is undecidable** (`OVERLAP_CFG`). -/
theorem exists_not_tm2Decidable_overlap :
    ∃ (T : Type) (_ : Primcodable T) (_ : DecidableEq T),
      ¬TM2Decidable fun g : EncodedCFG T × EncodedCFG T ↦
        ∃ w, w ∈ g.1.language ∧ w ∈ g.2.language := by
  obtain ⟨α, _, _, h⟩ := exists_not_tm2Decidable_pcp
  classical
  exact ⟨α ⊕ ℕ, inferInstance, inferInstance, fun hd ↦
    h (tm2Decidable_of_manyOneReducible manyOneReducible_pcp_inter hd)⟩

/-- **Whether two context-free languages are disjoint is undecidable.** -/
theorem exists_not_tm2Decidable_disjoint :
    ∃ (T : Type) (_ : Primcodable T) (_ : DecidableEq T),
      ¬TM2Decidable fun g : EncodedCFG T × EncodedCFG T ↦
        ∀ w, ¬(w ∈ g.1.language ∧ w ∈ g.2.language) := by
  obtain ⟨T, _, _, h⟩ := exists_not_tm2Decidable_overlap
  refine ⟨T, inferInstance, inferInstance, fun hd ↦ h ?_⟩
  simpa only [not_forall, not_not] using hd.not

/-- **Whether a context-free grammar is ambiguous is undecidable** (`AMBIG_CFG`). -/
theorem exists_not_tm2Decidable_isAmbiguous :
    ∃ (T : Type) (_ : Primcodable T) (_ : DecidableEq T),
      ¬TM2Decidable fun g : EncodedCFG T ↦ IsAmbiguous g.toCFG := by
  obtain ⟨α, _, _, h⟩ := exists_not_tm2Decidable_pcp
  classical
  exact ⟨α ⊕ ℕ, inferInstance, inferInstance, fun hd ↦
    h (tm2Decidable_of_manyOneReducible manyOneReducible_pcp_isAmbiguous hd)⟩

/-- **Whether a context-free grammar generates every word is undecidable** (`ALL_CFG`), over a
finite alphabet. -/
theorem exists_not_tm2Decidable_univ :
    ∃ (T : Type) (_ : Fintype T) (_ : Primcodable T) (_ : DecidableEq T),
      ¬TM2Decidable fun g : EncodedCFG T ↦ ∀ w, w ∈ g.language := by
  obtain ⟨α, _, _, h⟩ := exists_not_tm2Decidable_pcp
  classical
  refine ⟨α ⊕ Bool, inferInstance, inferInstance, inferInstance, fun hd ↦ h ?_⟩
  simpa only [not_not] using (tm2Decidable_of_manyOneReducible manyOneReducible_not_pcp_univ hd).not

/-! ### Equivalence and inclusion -/

section AllWords

variable {T : Type} [Fintype T] [DecidableEq T]

/-- The grammar `S → a S | ε` (for every letter `a`), generating every word. -/
noncomputable def allWordsCFG : EncodedCFG T :=
  ⟨0, (0, []) :: (Finset.univ : Finset T).toList.map fun a ↦ (0, [Sum.inr a, Sum.inl 0])⟩

theorem mem_language_allWordsCFG (w : List T) : w ∈ (allWordsCFG (T := T)).language := by
  rw [EncodedCFG.language, ← languageFrom_initial]
  have hval := isValuation_languageFrom (g := (allWordsCFG (T := T)).toCFG)
  induction w with
  | nil =>
    refine hval (EncodedCFG.decodeRule (0, []))
      (EncodedCFG.mem_toCFG_rules.mpr ⟨(0, []), List.mem_cons_self, rfl⟩) ?_
    exact Language.nil_mem_one
  | cons a w ih =>
    refine hval (EncodedCFG.decodeRule (0, [Sum.inr a, Sum.inl 0]))
      (EncodedCFG.mem_toCFG_rules.mpr ⟨(0, [Sum.inr a, Sum.inl 0]),
        List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a, by simp, rfl⟩), rfl⟩) ?_
    simp only [EncodedCFG.decodeRule, List.map_cons, List.map_nil, EncodedCFG.decodeSymbol,
      evalForm_cons, evalSymbol_terminal, evalSymbol_nonterminal, evalForm_nil, mul_one]
    exact Language.mem_mul.mpr ⟨[a], rfl, w, ih, rfl⟩

end AllWords

/-- **Equivalence of context-free grammars is undecidable** (`EQ_CFG`), over a finite alphabet. -/
theorem exists_not_tm2Decidable_language_eq :
    ∃ (T : Type) (_ : Fintype T) (_ : Primcodable T) (_ : DecidableEq T),
      ¬TM2Decidable fun g : EncodedCFG T × EncodedCFG T ↦ g.1.language = g.2.language := by
  obtain ⟨T, _, _, _, h⟩ := exists_not_tm2Decidable_univ
  refine ⟨T, inferInstance, inferInstance, inferInstance, fun hd ↦ h ?_⟩
  refine tm2Decidable_of_manyOneReducible ⟨fun g ↦ (g, allWordsCFG),
    (Primrec.pair Primrec.id (Primrec.const _)).to_comp, fun g ↦ ⟨fun hg ↦ ?_, fun hg w ↦ ?_⟩⟩ hd
  · exact Set.ext fun w ↦ ⟨fun _ ↦ mem_language_allWordsCFG w, fun _ ↦ hg w⟩
  · exact (congrArg (w ∈ ·) hg).mpr (mem_language_allWordsCFG w)

/-- **Inclusion of context-free languages is undecidable**, over a finite alphabet. -/
theorem exists_not_tm2Decidable_language_le :
    ∃ (T : Type) (_ : Fintype T) (_ : Primcodable T) (_ : DecidableEq T),
      ¬TM2Decidable fun g : EncodedCFG T × EncodedCFG T ↦ g.1.language ≤ g.2.language := by
  obtain ⟨T, _, _, _, h⟩ := exists_not_tm2Decidable_univ
  refine ⟨T, inferInstance, inferInstance, inferInstance, fun hd ↦ h ?_⟩
  refine tm2Decidable_of_manyOneReducible ⟨fun g ↦ (allWordsCFG, g),
    (Primrec.pair (Primrec.const _) Primrec.id).to_comp, fun g ↦ ⟨fun hg w _ ↦ hg w,
      fun hg w ↦ hg (mem_language_allWordsCFG w)⟩⟩ hd

end Cslib.Decidability
