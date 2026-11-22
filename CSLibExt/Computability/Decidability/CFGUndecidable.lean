/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Post correspondence problem reduces to intersection of context-free languages
-/
module

public import CSLibExt.Computability.Decidability.PCP
public import CSLibExt.Computability.Languages.ContextFree.Encoded

/-!
# The Post correspondence problem reduces to intersection of context-free languages

For a PCP instance `P` with dominoes `(t₁, b₁), …, (tₖ, bₖ)`, the **top grammar** has the
productions `S → tᵢ S i | tᵢ i` and the **bottom grammar** `S → bᵢ S i | bᵢ i`, over the letters of
`P` together with index terminals `i` (`sideGrammar`). They generate the words
`t_{i₁} ⋯ t_{iₙ} iₙ ⋯ i₁` and `b_{i₁} ⋯ b_{iₙ} iₙ ⋯ i₁` for nonempty index sequences
(`mem_language_sideGrammar`). A common word has the same index sequence on both sides and equal
letter parts, which is exactly a PCP solution (`pcp_iff_exists_mem_inter`).

The grammars are `Cslib.Language.EncodedCFG`s built primitive recursively from `P`, so PCP many-one
reduces to nonemptiness of the intersection of two context-free languages
(`manyOneReducible_pcp_inter`). The derivations are analyzed through the single nonterminal of each
sentential form (`eq_sideWord_of_derives`).

## Main results

- `sideGrammar`, `mem_language_sideGrammar`.
- `pcp_iff_exists_mem_inter`, `manyOneReducible_pcp_inter`.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, Problem 5.32
  (`OVERLAP_CFG`).
* J. E. Hopcroft, R. Motwani, J. D. Ullman, *Introduction to Automata Theory, Languages, and
  Computation*, 3rd ed., Pearson, 2006, §9.5.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability.Grammar

open Cslib.Language Post

variable {α : Type*}

/-! ### The grammars -/

/-- A letter of the PCP alphabet, as an encoded terminal. -/
def letterSym (a : α) : ℕ ⊕ (α ⊕ ℕ) := .inr (.inl a)

/-- The index terminal `i`. -/
def indexSym (i : ℕ) : ℕ ⊕ (α ⊕ ℕ) := .inr (.inr i)

/-- The nonterminal `A`. -/
def ntSym (A : ℕ) : ℕ ⊕ (α ⊕ ℕ) := .inl A

/-- The `i`-th domino of `P` (empty past the end). -/
def domino (P : List (Domino α)) (i : ℕ) : Domino α := P.getD i ([], [])

/-- The production `A → wᵢ A i`, for `wᵢ` the chosen side of the `i`-th domino. -/
def contRule (side : Domino α → List α) (A : ℕ) (P : List (Domino α)) (i : ℕ) :
    ℕ × List (ℕ ⊕ (α ⊕ ℕ)) :=
  (A, (side (domino P i)).map letterSym ++ [ntSym A, indexSym i])

/-- The production `A → wᵢ i`. -/
def termRule (side : Domino α → List α) (A : ℕ) (P : List (Domino α)) (i : ℕ) :
    ℕ × List (ℕ ⊕ (α ⊕ ℕ)) :=
  (A, (side (domino P i)).map letterSym ++ [indexSym i])

/-- The productions `A → wᵢ A i | wᵢ i` for every domino. -/
def sideRules (side : Domino α → List α) (A : ℕ) (P : List (Domino α)) :
    List (ℕ × List (ℕ ⊕ (α ⊕ ℕ))) :=
  (List.range P.length).flatMap fun i ↦ [contRule side A P i, termRule side A P i]

/-- The grammar of one side of `P` (the top side for `Prod.fst`, the bottom for `Prod.snd`). -/
def sideGrammar (side : Domino α → List α) (P : List (Domino α)) : EncodedCFG (α ⊕ ℕ) :=
  ⟨0, sideRules side 0 P⟩

/-- The letters `w_{i₁} ⋯ w_{iₙ}` of an index sequence. -/
def flat (side : Domino α → List α) (P : List (Domino α)) (is : List ℕ) : List α :=
  is.flatMap fun i ↦ side (domino P i)

/-- The word `w_{i₁} ⋯ w_{iₙ} iₙ ⋯ i₁` of an index sequence. -/
def sideWord (side : Domino α → List α) (P : List (Domino α)) (is : List ℕ) : List (α ⊕ ℕ) :=
  (flat side P is).map Sum.inl ++ is.reverse.map Sum.inr

/-! ### Derivations -/

section Derivations

variable [DecidableEq α] {side : Domino α → List α} {P : List (Domino α)}

omit [DecidableEq α] in
theorem decodeRule_contRule (A : ℕ) (i : ℕ) :
    EncodedCFG.decodeRule (contRule side A P i) =
      ⟨A, (side (domino P i)).map (Symbol.terminal ∘ Sum.inl) ++
        [Symbol.nonterminal A, Symbol.terminal (Sum.inr i)]⟩ := by
  simp [EncodedCFG.decodeRule, contRule, EncodedCFG.decodeSymbol, letterSym, ntSym, indexSym,
    Function.comp_def]

omit [DecidableEq α] in
theorem decodeRule_termRule (A : ℕ) (i : ℕ) :
    EncodedCFG.decodeRule (termRule side A P i) =
      ⟨A, (side (domino P i)).map (Symbol.terminal ∘ Sum.inl) ++
        [Symbol.terminal (Sum.inr i)]⟩ := by
  simp [EncodedCFG.decodeRule, termRule, EncodedCFG.decodeSymbol, letterSym, indexSym,
    Function.comp_def]

theorem contRule_mem {i : ℕ} (hi : i < P.length) :
    EncodedCFG.decodeRule (contRule side 0 P i) ∈ (sideGrammar side P).toCFG.rules :=
  EncodedCFG.mem_toCFG_rules.mpr ⟨_, List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, by simp⟩, rfl⟩

theorem termRule_mem {i : ℕ} (hi : i < P.length) :
    EncodedCFG.decodeRule (termRule side 0 P i) ∈ (sideGrammar side P).toCFG.rules :=
  EncodedCFG.mem_toCFG_rules.mpr ⟨_, List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, by simp⟩, rfl⟩

theorem cases_of_mem_rules {r : ContextFreeRule (α ⊕ ℕ) ℕ}
    (hr : r ∈ (sideGrammar side P).toCFG.rules) : ∃ i < P.length,
      r = EncodedCFG.decodeRule (contRule side 0 P i) ∨
        r = EncodedCFG.decodeRule (termRule side 0 P i) := by
  obtain ⟨e, he, rfl⟩ := EncodedCFG.mem_toCFG_rules.mp hr
  obtain ⟨i, hi, he⟩ := List.mem_flatMap.mp he
  refine ⟨i, List.mem_range.mp hi, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

omit [DecidableEq α] in
/-- A word of terminals derives only itself. -/
theorem eq_of_derives_terminal {g : ContextFreeGrammar (α ⊕ ℕ)} {u : List (α ⊕ ℕ)}
    {v : List (Symbol (α ⊕ ℕ) g.NT)} (h : g.Derives (u.map Symbol.terminal) v) :
    v = u.map Symbol.terminal := by
  rcases h.eq_or_head with rfl | ⟨w, hw, -⟩
  · rfl
  · obtain ⟨r, -, hr⟩ := hw.exists_nonterminal_input_mem
    simp at hr

omit [DecidableEq α] in
/-- Splitting a sentential form at its single nonterminal. -/
theorem eq_of_terminal_append_nonterminal {N : Type*} {pre suf : List (α ⊕ ℕ)} {A B : N}
    {p q : List (Symbol (α ⊕ ℕ) N)}
    (h : pre.map Symbol.terminal ++ Symbol.nonterminal A :: suf.map Symbol.terminal =
      p ++ [Symbol.nonterminal B] ++ q) :
    p = pre.map Symbol.terminal ∧ B = A ∧ q = suf.map Symbol.terminal := by
  induction pre generalizing p with
  | nil =>
    cases p with
    | nil =>
      simp only [List.map_nil, List.nil_append, List.cons_append, List.cons.injEq,
        Symbol.nonterminal.injEq] at h
      exact ⟨rfl, h.1.symm, h.2.symm⟩
    | cons x p =>
      simp only [List.map_nil, List.nil_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨-, h⟩ := h
      have : Symbol.nonterminal B ∈ suf.map Symbol.terminal := by rw [h]; simp
      simp at this
  | cons a pre ih =>
    cases p with
    | nil =>
      simp only [List.map_cons, List.cons_append, List.nil_append, List.cons.injEq] at h
      exact absurd h.1 (by simp)
    | cons x p =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, rfl, rfl⟩ := ih h
      exact ⟨rfl, rfl, rfl⟩

/-- **The analysis of derivations.** A derivation from `pre S suf` to a word of terminals applies
`S → wᵢ S i` for each index but the last and then `S → wᵢ i`. -/
theorem eq_sideWord_of_derives {s : List (Symbol (α ⊕ ℕ) ℕ)} {w : List (α ⊕ ℕ)}
    (h : (sideGrammar side P).toCFG.Derives s (w.map Symbol.terminal)) :
    ∀ pre suf : List (α ⊕ ℕ),
      s = pre.map Symbol.terminal ++ Symbol.nonterminal 0 :: suf.map Symbol.terminal →
      ∃ is : List ℕ, is ≠ [] ∧ (∀ i ∈ is, i < P.length) ∧ w = pre ++ sideWord side P is ++ suf := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro pre suf hs
    have : Symbol.nonterminal 0 ∈ w.map (Symbol.terminal (N := ℕ)) := by rw [hs]; simp
    simp at this
  | head hstep hrest ih =>
    intro pre suf hs
    subst hs
    obtain ⟨r, hr, hrw⟩ := hstep
    obtain ⟨p, q, hs, hs₁⟩ := hrw.exists_parts
    obtain ⟨rfl, hin, rfl⟩ := eq_of_terminal_append_nonterminal hs
    obtain ⟨i, hi, rfl | rfl⟩ := cases_of_mem_rules hr
    · -- `S → wᵢ S i`
      obtain ⟨is, hne, hlt, rfl⟩ := ih (pre ++ (side (domino P i)).map Sum.inl) (Sum.inr i :: suf)
        (by rw [hs₁, decodeRule_contRule]; simp)
      refine ⟨i :: is, List.cons_ne_nil _ _, ?_, ?_⟩
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hi
        · exact hlt j hj
      · simp [sideWord, flat, List.append_assoc]
    · -- `S → wᵢ i`
      rw [hs₁, decodeRule_termRule] at hrest
      have := eq_of_derives_terminal (u := pre ++ (side (domino P i)).map Sum.inl ++
        Sum.inr i :: suf) (by simpa [Function.comp_def] using hrest)
      refine ⟨[i], List.cons_ne_nil _ _, by simpa using hi, ?_⟩
      have hw := List.map_injective_iff.mpr (fun _ _ h ↦ Symbol.terminal.inj h) this
      rw [hw]
      simp [sideWord, flat]

/-- **The construction of derivations.** -/
theorem derives_sideWord : ∀ (is : List ℕ), is ≠ [] → (∀ i ∈ is, i < P.length) →
    ∀ pre suf : List (α ⊕ ℕ), (sideGrammar side P).toCFG.Derives
      (pre.map Symbol.terminal ++ Symbol.nonterminal 0 :: suf.map Symbol.terminal)
      ((pre ++ sideWord side P is ++ suf).map Symbol.terminal)
  | [], hne, _, _, _ => absurd rfl hne
  | [i], _, hlt, pre, suf => by
    refine ContextFreeGrammar.Produces.single ⟨_, termRule_mem (hlt i (by simp)), ?_⟩
    have := ContextFreeRule.rewrites_of_exists_parts
      (EncodedCFG.decodeRule (termRule side 0 P i)) (pre.map Symbol.terminal)
      (suf.map Symbol.terminal)
    rw [decodeRule_termRule] at this ⊢
    simpa [sideWord, flat, Function.comp_def] using this
  | i :: j :: is, _, hlt, pre, suf => by
    have hd := derives_sideWord (j :: is) (List.cons_ne_nil _ _)
      (fun k hk ↦ hlt k (List.mem_cons_of_mem _ hk)) (pre ++ (side (domino P i)).map Sum.inl)
      (Sum.inr i :: suf)
    have e : pre ++ (side (domino P i)).map Sum.inl ++ sideWord side P (j :: is) ++
        Sum.inr i :: suf = pre ++ sideWord side P (i :: j :: is) ++ suf := by
      simp [sideWord, flat, List.append_assoc]
    rw [e] at hd
    refine ContextFreeGrammar.Produces.trans_derives ⟨_, contRule_mem (hlt i (by simp)), ?_⟩ hd
    have := ContextFreeRule.rewrites_of_exists_parts
      (EncodedCFG.decodeRule (contRule side 0 P i)) (pre.map Symbol.terminal)
      (suf.map Symbol.terminal)
    rw [decodeRule_contRule] at this ⊢
    simpa [Function.comp_def] using this

/-- **The language of a side grammar**: the words `w_{i₁} ⋯ w_{iₙ} iₙ ⋯ i₁` for nonempty index
sequences. -/
theorem mem_language_sideGrammar {w : List (α ⊕ ℕ)} :
    w ∈ (sideGrammar side P).language ↔
      ∃ is : List ℕ, is ≠ [] ∧ (∀ i ∈ is, i < P.length) ∧ w = sideWord side P is := by
  rw [EncodedCFG.mem_language_iff]
  constructor
  · intro h
    obtain ⟨is, hne, hlt, rfl⟩ := eq_sideWord_of_derives h [] [] rfl
    exact ⟨is, hne, hlt, by simp⟩
  · rintro ⟨is, hne, hlt, rfl⟩
    simpa [sideGrammar] using derives_sideWord is hne hlt [] []

end Derivations

/-! ### Common words are PCP solutions -/

/-- A word of letters followed by a word of markers splits uniquely. -/
theorem eq_of_map_inl_append_map_inr {β : Type*} {A C : List α} {B D : List β}
    (h : A.map Sum.inl ++ B.map Sum.inr = C.map Sum.inl ++ D.map Sum.inr) : A = C ∧ B = D := by
  induction A generalizing C with
  | nil =>
    cases C with
    | nil =>
      simp only [List.map_nil, List.nil_append] at h
      exact ⟨rfl, List.map_injective_iff.mpr (fun _ _ h ↦ Sum.inr_injective h) h⟩
    | cons c C =>
      cases B with
      | nil => simp at h
      | cons b B => simp at h
  | cons a A ih =>
    cases C with
    | nil =>
      cases D with
      | nil => simp at h
      | cons d D => simp at h
    | cons c C =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq, Sum.inl.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, rfl⟩ := ih h
      exact ⟨rfl, rfl⟩

theorem exists_indices {P s : List (Domino α)} (hs : ∀ d ∈ s, d ∈ P) :
    ∃ is : List ℕ, (∀ i ∈ is, i < P.length) ∧ is.map (domino P) = s := by
  induction s with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons d s ih =>
    obtain ⟨is, hlt, rfl⟩ := ih fun e he ↦ hs e (List.mem_cons_of_mem _ he)
    obtain ⟨i, hi, hd⟩ := List.mem_iff_getElem.mp (hs d List.mem_cons_self)
    refine ⟨i :: is, ?_, ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hlt j hj
    · simp [domino, List.getElem?_eq_getElem hi, hd]

theorem flat_eq (side : Domino α → List α) (P : List (Domino α)) (is : List ℕ) :
    flat side P is = (is.map (domino P)).flatMap side := by
  simp [flat, List.flatMap_map]

theorem domino_mem {P : List (Domino α)} {i : ℕ} (hi : i < P.length) : domino P i ∈ P := by
  simp [domino, List.getElem?_eq_getElem hi]

/-- **PCP solutions are the common words of the top and bottom grammars.** -/
theorem pcp_iff_exists_mem_inter [DecidableEq α] (P : List (Domino α)) :
    PCP P ↔ ∃ w, w ∈ (sideGrammar Prod.fst P).language ∧ w ∈ (sideGrammar Prod.snd P).language := by
  constructor
  · rintro ⟨s, hne, hmem, htop⟩
    obtain ⟨is, hlt, rfl⟩ := exists_indices hmem
    have hne' : is ≠ [] := by rintro rfl; exact hne rfl
    refine ⟨sideWord Prod.fst P is, mem_language_sideGrammar.mpr ⟨is, hne', hlt, rfl⟩,
      mem_language_sideGrammar.mpr ⟨is, hne', hlt, ?_⟩⟩
    simp only [sideWord, flat_eq]
    rw [show (is.map (domino P)).flatMap Prod.fst = (is.map (domino P)).flatMap Prod.snd from htop]
  · rintro ⟨w, h₁, h₂⟩
    obtain ⟨is, hne, hlt, rfl⟩ := mem_language_sideGrammar.mp h₁
    obtain ⟨js, -, -, h⟩ := mem_language_sideGrammar.mp h₂
    obtain ⟨hflat, hrev⟩ := eq_of_map_inl_append_map_inr h
    obtain rfl : is = js := List.reverse_injective hrev
    refine ⟨is.map (domino P), by simpa using hne, fun d hd ↦ ?_, ?_⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
      exact domino_mem (hlt i hi)
    · simpa [flat_eq, top, bottom] using hflat

/-! ### The many-one reduction -/

section Computable

variable [Primcodable α]

theorem primrec_sideRules {side : Domino α → List α} (hside : Primrec side) (A : ℕ) :
    Primrec (sideRules side A) := by
  have hdom : Primrec₂ (domino (α := α)) := Primrec.list_getD _
  have hletter : Primrec (letterSym (α := α)) := Primrec.sumInr.comp Primrec.sumInl
  have hindex : Primrec (indexSym (α := α)) := Primrec.sumInr.comp Primrec.sumInr
  have hside' : Primrec₂ fun (P : List (Domino α)) (i : ℕ) ↦ (side (domino P i)).map letterSym :=
    Primrec.list_map (hside.comp hdom) (hletter.comp Primrec.snd).to₂
  have hcont : Primrec₂ (contRule side A (α := α)) :=
    Primrec.pair (Primrec.const A) (Primrec.list_append.comp hside'
      (Primrec.list_cons.comp (Primrec.const _) (Primrec.list_cons.comp (hindex.comp Primrec.snd)
        (Primrec.const []))))
  have hterm : Primrec₂ (termRule side A (α := α)) :=
    Primrec.pair (Primrec.const A) (Primrec.list_append.comp hside'
      (Primrec.list_cons.comp (hindex.comp Primrec.snd) (Primrec.const [])))
  exact Primrec.list_flatMap (Primrec.list_range.comp Primrec.list_length)
    (Primrec.list_cons.comp hcont (Primrec.list_cons.comp hterm (Primrec.const []))).to₂

theorem primrec_sideGrammar {side : Domino α → List α} (hside : Primrec side) :
    Primrec (sideGrammar side) :=
  EncodedCFG.primrec₂_mk.comp (Primrec.const 0) (primrec_sideRules hside 0)

/-- **PCP many-one reduces to nonemptiness of the intersection of two context-free
languages.** -/
theorem manyOneReducible_pcp_inter [DecidableEq α] :
    ManyOneReducible (PCP (α := α)) fun g : EncodedCFG (α ⊕ ℕ) × EncodedCFG (α ⊕ ℕ) ↦
      ∃ w, w ∈ g.1.language ∧ w ∈ g.2.language :=
  ⟨fun P ↦ (sideGrammar Prod.fst P, sideGrammar Prod.snd P),
    (Primrec.pair (primrec_sideGrammar Primrec.fst) (primrec_sideGrammar Primrec.snd)).to_comp,
    pcp_iff_exists_mem_inter⟩

end Computable

end Cslib.Decidability.Grammar
