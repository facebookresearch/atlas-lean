/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Decidability.CFGFiniteAlphabet

/-!
# Binary CFG undecidability consumers

Concrete solvable and unsolvable PCP instances, explicit common binary words, and two unequal
leftmost rule traces exercise the reductions on actual encoded grammars.
-/

set_option autoImplicit false

open Cslib.Language Cslib.Language.EncodedCFG Cslib.Decidability
open Cslib.Decidability.Post Cslib.Decidability.Grammar

namespace CSLibExtTest.Computability.Decidability.CFGFiniteAlphabet

private def yesInstance : List (Domino Bool) := [([true], [true])]

private def noInstance : List (Domino Bool) := [([true], [false])]

private theorem yes_pcp : PCP yesInstance :=
  ⟨yesInstance, by decide, fun _ h => h, rfl⟩

private theorem no_pcp : ¬PCP noInstance := by
  rintro ⟨s, hne, hmem, htop⟩
  obtain ⟨d, s, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain rfl : d = ([true], [false]) := by
    simpa [noInstance] using hmem d List.mem_cons_self
  simp [top, bottom] at htop

private theorem index_zero_one_and_marker :
    boolNatIndex (.inl false) = 0 ∧ boolNatIndex (.inl true) = 1 ∧
      boolNatIndex (.inr 0) = 2 := by decide

private theorem index_arbitrary_marker (n : ℕ) : boolNatIndex (.inr n) = n + 2 := rfl

private theorem arbitrary_marker_code_length (n : ℕ) :
    (unaryCode boolNatIndex (Sum.inr n)).length = n + 3 := by
  simp [unaryCode, boolNatIndex, Nat.add_assoc]

private theorem index_injection_consumer : Function.Injective boolNatIndex := boolNatIndex_injective

private theorem infinite_index_primrec : Primrec boolNatIndex := primrec_boolNatIndex

private theorem infinite_code_primrec : Primrec (unaryCode boolNatIndex) :=
  primrec_unaryCode primrec_boolNatIndex

private theorem natural_code_primrec : Primrec (unaryCode (fun n : ℕ => n)) :=
  primrec_unaryCode Primrec.id

private theorem infinite_word_injection :
    Function.Injective (_root_.Language.Hom.lift (unaryCode boolNatIndex)) := boolNatWord_injective

private theorem binary_conversion_primrec : Primrec binaryCFG := primrec_binaryCFG

private theorem actual_encoded_rhs :
    (binaryCFG (⟨42, [(42, [Sum.inr (Sum.inl false), Sum.inl 3,
      Sum.inr (Sum.inr 2)])]⟩ : EncodedCFG (Bool ⊕ ℕ))).rules =
      [(42, [Sum.inr false, Sum.inl 3, Sum.inr true, Sum.inr true,
        Sum.inr true, Sum.inr true, Sum.inr false])] := rfl

private def commonWord : List Bool := [true, false, true, true, false]

private theorem commonWord_nonempty : commonWord ≠ [] := by decide

private theorem source_top_word :
    [Sum.inl true, Sum.inr 0] ∈ (sideGrammar Prod.fst yesInstance).language :=
  mem_language_sideGrammar.mpr ⟨[0], by decide, by simp [yesInstance], rfl⟩

private theorem source_bottom_word :
    [Sum.inl true, Sum.inr 0] ∈ (sideGrammar Prod.snd yesInstance).language :=
  mem_language_sideGrammar.mpr ⟨[0], by decide, by simp [yesInstance], rfl⟩

private theorem actual_nonempty_binary_overlap :
    commonWord ∈ (binaryCFG (sideGrammar Prod.fst yesInstance)).language ∧
      commonWord ∈ (binaryCFG (sideGrammar Prod.snd yesInstance)).language :=
  ⟨(mem_language_mapTerminals _ _ _).mpr ⟨_, source_top_word, rfl⟩,
    (mem_language_mapTerminals _ _ _).mpr ⟨_, source_bottom_word, rfl⟩⟩

private theorem no_binary_overlap :
    ¬∃ w, w ∈ (binaryCFG (sideGrammar Prod.fst noInstance)).language ∧
      w ∈ (binaryCFG (sideGrammar Prod.snd noInstance)).language := by
  rw [overlap_binaryCFG_iff, ← pcp_iff_exists_mem_inter]
  exact no_pcp

private theorem binary_language_image :
    (binaryCFG (sideGrammar Prod.fst yesInstance)).language =
      (sideGrammar Prod.fst yesInstance).language.image
        (_root_.Language.Hom.lift (unaryCode boolNatIndex)) := language_binaryCFG _

private def topTrace : List (ContextFreeRule (Bool ⊕ ℕ) ℕ) :=
  startRule 1 :: canon Prod.fst 1 yesInstance [0]

private def bottomTrace : List (ContextFreeRule (Bool ⊕ ℕ) ℕ) :=
  startRule 2 :: canon Prod.snd 2 yesInstance [0]

private theorem source_top_trace :
    LeftDerivation (ambGrammar yesInstance).toCFG [Symbol.nonterminal 0]
      [Sum.inl true, Sum.inr 0] topTrace :=
  leftDerivation_start (is := [0]) (Or.inl ⟨rfl, rfl⟩) (by decide) (by simp [yesInstance])

private theorem source_bottom_trace :
    LeftDerivation (ambGrammar yesInstance).toCFG [Symbol.nonterminal 0]
      [Sum.inl true, Sum.inr 0] bottomTrace :=
  leftDerivation_start (is := [0]) (Or.inr ⟨rfl, rfl⟩) (by decide) (by simp [yesInstance])

private theorem source_traces_distinct : topTrace ≠ bottomTrace := by decide

private theorem binary_top_trace :
    LeftDerivation (binaryCFG (ambGrammar yesInstance)).toCFG [Symbol.nonterminal 0]
      commonWord (topTrace.map (mapTerminalRule (unaryCode boolNatIndex))) :=
  leftDerivation_mapTerminals source_top_trace

private theorem binary_bottom_trace :
    LeftDerivation (binaryCFG (ambGrammar yesInstance)).toCFG [Symbol.nonterminal 0]
      commonWord (bottomTrace.map (mapTerminalRule (unaryCode boolNatIndex))) :=
  leftDerivation_mapTerminals source_bottom_trace

private theorem binary_traces_distinct :
    topTrace.map (mapTerminalRule (unaryCode boolNatIndex)) ≠
      bottomTrace.map (mapTerminalRule (unaryCode boolNatIndex)) :=
  fun h => source_traces_distinct (mapTerminalRules_injective boolNatWord_injective h)

private theorem actual_binary_ambiguity : IsAmbiguous (binaryCFG (ambGrammar yesInstance)).toCFG :=
  ⟨commonWord, _, _, binary_traces_distinct, binary_top_trace, binary_bottom_trace⟩

private theorem actual_binary_unambiguity : ¬IsAmbiguous (binaryCFG (ambGrammar noInstance)).toCFG := by
  rw [isAmbiguous_binaryCFG_iff, isAmbiguous_iff_pcp]
  exact no_pcp

private theorem source_solution_reflected : PCP yesInstance := by
  exact (isAmbiguous_iff_pcp _).mp ((isAmbiguous_binaryCFG_iff _).mp actual_binary_ambiguity)

private theorem epsilon_domino_solution : PCP ([([], [])] : List (Domino Bool)) :=
  ⟨[([], [])], by decide, by simp, rfl⟩

private theorem epsilon_domino_binary_ambiguity :
    IsAmbiguous (binaryCFG (ambGrammar ([([], [])] : List (Domino Bool)))).toCFG :=
  (isAmbiguous_binaryCFG_iff _).mpr ((isAmbiguous_iff_pcp _).mpr epsilon_domino_solution)

private theorem overlap_reduction_consumer :
    ManyOneReducible (PCP (α := Bool)) fun g : EncodedCFG Bool × EncodedCFG Bool =>
      ∃ w, w ∈ g.1.language ∧ w ∈ g.2.language := manyOneReducible_pcp_overlap_bool

private theorem ambiguity_reduction_consumer :
    ManyOneReducible (PCP (α := Bool)) fun g : EncodedCFG Bool => IsAmbiguous g.toCFG :=
  manyOneReducible_pcp_isAmbiguous_bool

private theorem binary_overlap_undecidable :
    ¬TM2Decidable fun g : EncodedCFG Bool × EncodedCFG Bool =>
      ∃ w, w ∈ g.1.language ∧ w ∈ g.2.language := not_tm2Decidable_overlap_bool

private theorem binary_ambiguity_undecidable :
    ¬TM2Decidable fun g : EncodedCFG Bool => IsAmbiguous g.toCFG :=
  not_tm2Decidable_isAmbiguous_bool

end CSLibExtTest.Computability.Decidability.CFGFiniteAlphabet
