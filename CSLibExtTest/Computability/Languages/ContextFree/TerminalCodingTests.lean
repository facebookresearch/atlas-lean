/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Languages.ContextFree.TerminalCoding
import CSLibExt.Computability.Decidability.PCPBinary

/-!
# Consumers of encoded terminal coding

The fixtures distinguish grammar derivations from languages and rule values from duplicate
list occurrences. Every test is a named stored declaration; concrete finite checks use `decide`.
-/

set_option autoImplicit false

open Cslib.Language Cslib.Language.EncodedCFG Cslib.Decidability.Post

namespace CSLibExtTest.Computability.Languages.ContextFree.TerminalCoding

private def code : Bool → List Bool := unaryCode Bool.toNat

private theorem code_injective : Function.Injective (_root_.Language.Hom.lift code) := by
  apply unaryHom_injective
  intro a b h
  cases a <;> cases b <;> simp_all

private def epsilonUnit : EncodedCFG Bool :=
  ⟨7, [(7, [Sum.inl 8]), (8, []), (8, [])]⟩

private def unitRule : ContextFreeRule Bool ℕ := decodeRule (7, [Sum.inl 8])

private def epsilonRule : ContextFreeRule Bool ℕ := decodeRule (8, [])

private theorem epsilonUnit_derivation :
    LeftDerivation epsilonUnit.toCFG [Symbol.nonterminal 7] [] [unitRule, epsilonRule] :=
  LeftDerivation.step (g := epsilonUnit.toCFG) (r := unitRule) (p := []) (v := []) (by decide)
    (LeftDerivation.step (g := epsilonUnit.toCFG) (r := epsilonRule) (p := []) (v := [])
      (by decide) (LeftDerivation.done []))

private theorem duplicate_entries_are_not_rules :
    epsilonUnit.rules.length = 3 ∧ epsilonUnit.toCFG.rules.card = 2 := by decide

private theorem encoded_unit_and_epsilon_unchanged :
    (mapTerminals code epsilonUnit).start = 7 ∧
      (mapTerminals code epsilonUnit).rules = epsilonUnit.rules := by
  constructor
  · exact start_mapTerminals code epsilonUnit
  · rfl

private theorem coded_duplicate_entries_are_not_rules :
    (mapTerminals code epsilonUnit).rules.length = 3 ∧
      (mapTerminals code epsilonUnit).toCFG.rules.card = 2 := by decide

private theorem forms_include_empty_blocks :
    mapTerminalForm code [Symbol.nonterminal 1, Symbol.terminal true,
        Symbol.nonterminal 2, Symbol.nonterminal 3] =
      [Symbol.nonterminal 1, Symbol.terminal true, Symbol.terminal false,
        Symbol.nonterminal 2, Symbol.nonterminal 3] := rfl

private theorem form_simp_interface (p q : List (Symbol Bool ℕ)) (w : List Bool) :
    mapTerminalForm code (p ++ w.map Symbol.terminal ++ q) =
      mapTerminalForm code p ++ ((_root_.Language.Hom.lift code) w).map Symbol.terminal ++
        mapTerminalForm code q := by simp

private theorem rule_simp_interface (r : ContextFreeRule Bool ℕ) :
    (mapTerminalRule code r).input = r.input ∧
      (mapTerminalRule code r).output = mapTerminalForm code r.output := by simp

private theorem form_injection_consumer : Function.Injective (mapTerminalForm code) :=
  mapTerminalForm_injective code_injective

private theorem rule_injection_consumer : Function.Injective (mapTerminalRule code) :=
  mapTerminalRule_injective code_injective

private theorem trace_injection_consumer : Function.Injective (List.map (mapTerminalRule code)) :=
  mapTerminalRules_injective code_injective

private theorem coded_rule_membership :
    mapTerminalRule code unitRule ∈ (mapTerminals code epsilonUnit).toCFG.rules :=
  (mem_rules_mapTerminals code epsilonUnit _).mpr ⟨unitRule, by decide, rfl⟩

private theorem epsilon_forward_exact_trace :
    LeftDerivation (mapTerminals code epsilonUnit).toCFG [Symbol.nonterminal 7] []
      ([unitRule, epsilonRule].map (mapTerminalRule code)) :=
  leftDerivation_mapTerminals epsilonUnit_derivation

private theorem epsilon_reflection_exact_trace :
    LeftDerivation epsilonUnit.toCFG [Symbol.nonterminal 7] [] [unitRule, epsilonRule] :=
  (leftDerivation_mapTerminals_iff_of_injective code_injective).mp epsilon_forward_exact_trace

private theorem epsilon_reflection_witnesses :
    ∃ w rs, LeftDerivation epsilonUnit.toCFG [Symbol.nonterminal 7] w rs ∧
      (_root_.Language.Hom.lift code) w = [] ∧
        rs.map (mapTerminalRule code) = [unitRule, epsilonRule].map (mapTerminalRule code) :=
  leftDerivation_mapTerminals_iff.mp epsilon_forward_exact_trace

private theorem nonterminal_cases {g : EncodedCFG Bool} {A : ℕ} {w : List Bool}
    {rs : List (ContextFreeRule Bool ℕ)}
    (h : LeftDerivation g.toCFG [Symbol.nonterminal A] w rs) :
    ∃ r rs', r ∈ g.toCFG.rules ∧ r.input = A ∧ rs = r :: rs' ∧
      LeftDerivation g.toCFG r.output w rs' := by
  generalize hs : ([Symbol.nonterminal A] : List (Symbol Bool ℕ)) = s at h
  cases h using @LeftDerivation.casesOn Bool g.toCFG with
  | done w =>
    have hm : Symbol.nonterminal A ∈ w.map (Symbol.terminal (N := ℕ)) := by
      rw [← hs]
      simp
    simp at hm
  | @step p v w r rs hr hrest =>
    cases p with
    | nil =>
      simp only [List.map_nil, List.nil_append, List.cons.injEq, Symbol.nonterminal.injEq] at hs
      obtain ⟨ha, hv⟩ := hs
      subst v
      exact ⟨r, rs, hr, ha.symm, rfl, by simpa using hrest⟩
    | cons a p => simp at hs

private theorem epsilonUnit_unique {w : List Bool} {rs : List (ContextFreeRule Bool ℕ)}
    (h : LeftDerivation epsilonUnit.toCFG [Symbol.nonterminal 7] w rs) :
    rs = [unitRule, epsilonRule] ∧ w = [] := by
  have rules : ∀ r ∈ epsilonUnit.toCFG.rules, r = unitRule ∨ r = epsilonRule := by
    intro r hr
    obtain ⟨e, he, rfl⟩ := mem_toCFG_rules.mp hr
    simp only [epsilonUnit, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
  obtain ⟨r₁, ts₁, hr₁, hin₁, ht₁, hd₁⟩ := nonterminal_cases h
  have he₁ : r₁ = unitRule := by
    rcases rules r₁ hr₁ with he | he
    · exact he
    · subst r₁
      cases hin₁
  subst r₁
  obtain ⟨r₂, ts₂, hr₂, hin₂, ht₂, hd₂⟩ := nonterminal_cases (A := 8) hd₁
  have he₂ : r₂ = epsilonRule := by
    rcases rules r₂ hr₂ with he | he
    · subst r₂
      cases hin₂
    · exact he
  subst r₂
  obtain ⟨hrs, hw⟩ := LeftDerivation.eq_of_terminal (u := []) hd₂
  exact ⟨by rw [ht₁, ht₂, hrs], hw⟩

private theorem duplicate_epsilon_grammar_unambiguous : ¬IsAmbiguous epsilonUnit.toCFG := by
  rintro ⟨w, rs₁, rs₂, hne, h₁, h₂⟩
  exact hne ((epsilonUnit_unique h₁).1.trans (epsilonUnit_unique h₂).1.symm)

private theorem coded_epsilon_grammar_unambiguous :
    ¬IsAmbiguous (mapTerminals code epsilonUnit).toCFG :=
  fun h => duplicate_epsilon_grammar_unambiguous
    ((isAmbiguous_mapTerminals_iff code_injective).mp h)

private def cyclic : EncodedCFG Bool := ⟨0, [(0, []), (0, [Sum.inl 0]), (0, [])]⟩

private def stopRule : ContextFreeRule Bool ℕ := decodeRule (0, [])

private def loopRule : ContextFreeRule Bool ℕ := decodeRule (0, [Sum.inl 0])

private theorem cyclic_short_trace :
    LeftDerivation cyclic.toCFG [Symbol.nonterminal 0] [] [stopRule] :=
  LeftDerivation.step (g := cyclic.toCFG) (r := stopRule) (p := []) (v := [])
    (by decide) (LeftDerivation.done [])

private theorem cyclic_long_trace :
    LeftDerivation cyclic.toCFG [Symbol.nonterminal 0] [] [loopRule, stopRule] :=
  LeftDerivation.step (g := cyclic.toCFG) (r := loopRule) (p := []) (v := [])
    (by decide) cyclic_short_trace

private theorem cyclic_ambiguous : IsAmbiguous cyclic.toCFG :=
  ⟨[], [stopRule], [loopRule, stopRule], by decide, cyclic_short_trace, cyclic_long_trace⟩

private theorem coded_cyclic_ambiguous : IsAmbiguous (mapTerminals code cyclic).toCFG :=
  (isAmbiguous_mapTerminals_iff code_injective).mpr cyclic_ambiguous

private def oneWord (w : List Bool) : EncodedCFG Bool := ⟨0, [(0, w.map Sum.inr)]⟩

private theorem oneWord_derivation (w : List Bool) :
    LeftDerivation (oneWord w).toCFG [Symbol.nonterminal 0] w
      [decodeRule (0, w.map Sum.inr)] := by
  have hr : decodeRule (0, w.map Sum.inr) ∈ (oneWord w).toCFG.rules :=
    mem_toCFG_rules.mpr ⟨_, by simp [oneWord], rfl⟩
  have hd := LeftDerivation.done (g := (oneWord w).toCFG) w
  have ho : (decodeRule (0, w.map Sum.inr)).output = w.map Symbol.terminal := by
    simp [decodeRule, decodeSymbol, List.map_map, Function.comp_def]
  rw [← ho] at hd
  exact LeftDerivation.step (p := []) (v := []) hr (by simpa using hd)

private theorem oneWord_language (w : List Bool) : (oneWord w).language = {w} := by
  apply le_antisymm
  · apply language_le_of_valuation (V := fun _ => ({w} : Language Bool))
    intro r hr
    obtain ⟨e, he, rfl⟩ := mem_toCFG_rules.mp hr
    obtain rfl : e = (0, w.map Sum.inr) := by simpa [oneWord] using he
    simpa [decodeRule, decodeSymbol, List.map_map, Function.comp_def] using
      (le_of_eq (evalForm_map_terminal (fun _ : ℕ => ({w} : Language Bool)) w))
  · intro v hv
    have hv' : v = w := hv
    subst v
    exact (oneWord_derivation w).mem_language

private theorem singleton_languages_separated :
    ¬∃ w, w ∈ (oneWord [false]).language ∧ w ∈ (oneWord [true]).language := by
  simp only [oneWord_language]
  rintro ⟨w, rfl, h⟩
  cases h

private def collapse (_ : Bool) : List Bool := [false]

private theorem collapse_not_injective : ¬Function.Injective (_root_.Language.Hom.lift collapse) := by
  intro h
  have he := h (a₁ := [false]) (a₂ := [true]) rfl
  cases he

private theorem noninjective_coding_creates_overlap :
    [false] ∈ (mapTerminals collapse (oneWord [false])).language ∧
      [false] ∈ (mapTerminals collapse (oneWord [true])).language :=
  ⟨(mem_language_mapTerminals _ _ _).mpr ⟨[false], (oneWord_derivation [false]).mem_language, rfl⟩,
    (mem_language_mapTerminals _ _ _).mpr ⟨[true], (oneWord_derivation [true]).mem_language, rfl⟩⟩

private theorem injective_overlap_consumer :
    ¬∃ w, w ∈ (mapTerminals code (oneWord [false])).language ∧
      w ∈ (mapTerminals code (oneWord [true])).language := by
  rw [overlap_mapTerminals_iff code code_injective]
  exact singleton_languages_separated

private theorem canonical_image_consumer :
    (mapTerminals code (oneWord [true])).language =
      (oneWord [true]).language.image (_root_.Language.Hom.lift code) :=
  language_mapTerminals _ _

private theorem erasing_trace :
    LeftDerivation (mapTerminals (fun _ : Bool => ([] : List Bool)) (oneWord [true])).toCFG
      [Symbol.nonterminal 0] []
      ([decodeRule (0, [Sum.inr true])].map (mapTerminalRule (fun _ : Bool => ([] : List Bool)))) :=
  leftDerivation_mapTerminals (oneWord_derivation [true])

private theorem erasing_reflection :
    ∃ w rs, LeftDerivation (oneWord [true]).toCFG [Symbol.nonterminal 0] w rs ∧
      (_root_.Language.Hom.lift (fun _ : Bool => ([] : List Bool))) w = [] ∧
      rs.map (mapTerminalRule (fun _ : Bool => ([] : List Bool))) =
        [decodeRule (0, [Sum.inr true])].map (mapTerminalRule (fun _ : Bool => ([] : List Bool))) :=
  leftDerivation_mapTerminals_iff.mp erasing_trace

private theorem infinite_source_primrec_consumer {φ : ℕ → List Bool} (hφ : Primrec φ) :
    Primrec (mapTerminals φ) := primrec_mapTerminals hφ

end CSLibExtTest.Computability.Languages.ContextFree.TerminalCoding
