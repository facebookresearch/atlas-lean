/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Post correspondence problem reduces to ambiguity of context-free grammars
-/
module

public import CSLibExt.Computability.Decidability.CFGUndecidable
public import CSLibExt.Computability.Languages.ContextFree.Ambiguity

/-!
# The Post correspondence problem reduces to ambiguity of context-free grammars

For a PCP instance `P`, the grammar `ambGrammar P` has the start productions `S → A | B`, the
productions `A → tᵢ A i | tᵢ i` of the top grammar and `B → bᵢ B i | bᵢ i` of the bottom grammar
(`Cslib.Decidability.Grammar.sideGrammar`).

Every sentential form below `A` (or `B`) has a single nonterminal, so a leftmost derivation from
`A` is determined by its word: it is `canon` of the index sequence read off the end of the word
(`eq_canon_of_leftDerivation`). Two different leftmost derivations of one word must therefore
start with different productions `S → A` and `S → B`, which makes the word common to the top and
bottom languages, i.e. a PCP solution. Conversely a solution's word has a leftmost derivation
through `A` and one through `B` (`isAmbiguous_iff_pcp`).

`ambGrammar` is primitive recursive, so PCP many-one reduces to ambiguity of encoded context-free
grammars (`manyOneReducible_pcp_isAmbiguous`).

## Main results

- `ambGrammar`, `isAmbiguous_iff_pcp`, `manyOneReducible_pcp_isAmbiguous`.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, Problem 5.21
  (`AMBIG_CFG`).
* J. E. Hopcroft, R. Motwani, J. D. Ullman, *Introduction to Automata Theory, Languages, and
  Computation*, 3rd ed., Pearson, 2006, §9.5.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability.Grammar

open Cslib.Language Post

variable {α : Type*}

/-- **The ambiguity grammar of a PCP instance.** Let $P = [(t_0, b_0), \dots, (t_{m-1}, b_{m-1})]$
be a list of dominoes over an alphabet $\alpha$, with top words $t_i$ and bottom words $b_i$. The
ambiguity grammar of $P$ is the encoded context-free grammar over the terminals
$\alpha \sqcup \mathbb{N}$ (letters and indices) with nonterminals $S = 0$, $A = 1$, $B = 2$, start
symbol $S$, and the productions $S \to A$ and $S \to B$ together with, for every $i < m$, the
productions $A \to t_i\, A\, i$, $A \to t_i\, i$, $B \to b_i\, B\, i$ and $B \to b_i\, i$, in which
the index $i$ is a terminal. -/
def ambGrammar (P : List (Domino α)) : EncodedCFG (α ⊕ ℕ) :=
  ⟨0, (0, [ntSym 1]) :: (0, [ntSym 2]) :: (sideRules Prod.fst 1 P ++ sideRules Prod.snd 2 P)⟩

/-- **The canonical rule sequence along an index sequence.** Let $P$ be a list of dominoes over
$\alpha$, let $\sigma$ assign a word over $\alpha$ to each domino, let $A$ be a natural number,
and for $i \in \mathbb{N}$ write $w_i$ for $\sigma$ applied to the $i$-th domino of $P$ (the domino
with both words empty when $i$ is past the end of $P$). For a sequence $i_1, \dots, i_n$ of
natural numbers, this is the list of productions, with terminals $\alpha \sqcup \mathbb{N}$ and
nonterminals $\mathbb{N}$, consisting of $A \to w_{i_k}\, A\, i_k$ for $k = 1, \dots, n - 1$ in
order, followed by $A \to w_{i_n}\, i_n$, where the letters of $w_{i_k}$ and the index $i_k$ are
terminals and $A$ is a nonterminal; the empty sequence gives the empty list. -/
def canon (side : Domino α → List α) (A : ℕ) (P : List (Domino α)) :
    List ℕ → List (ContextFreeRule (α ⊕ ℕ) ℕ)
  | [] => []
  | [i] => [EncodedCFG.decodeRule (termRule side A P i)]
  | i :: j :: is => EncodedCFG.decodeRule (contRule side A P i) :: canon side A P (j :: is)

theorem canon_cons {side : Domino α → List α} {A : ℕ} {P : List (Domino α)} {i : ℕ}
    {is : List ℕ} (h : is ≠ []) :
    canon side A P (i :: is) =
      EncodedCFG.decodeRule (contRule side A P i) :: canon side A P is := by
  obtain ⟨j, is, rfl⟩ := List.exists_cons_of_ne_nil h
  rfl

theorem eq_of_map_terminal_append_cons {N : Type*} {p pre : List (α ⊕ ℕ)} {A B : N}
    {v v' : List (Symbol (α ⊕ ℕ) N)}
    (h : p.map Symbol.terminal ++ Symbol.nonterminal B :: v =
      pre.map Symbol.terminal ++ Symbol.nonterminal A :: v') : p = pre ∧ B = A ∧ v = v' := by
  induction p generalizing pre with
  | nil =>
    cases pre with
    | nil =>
      simp only [List.map_nil, List.nil_append, List.cons.injEq, Symbol.nonterminal.injEq] at h
      exact ⟨rfl, h.1, h.2⟩
    | cons b pre => simp at h
  | cons a p ih =>
    cases pre with
    | nil => simp at h
    | cons b pre =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq, Symbol.terminal.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, rfl, rfl⟩ := ih h
      exact ⟨rfl, rfl, rfl⟩

section Derivations

variable [DecidableEq α] {P : List (Domino α)}

theorem decodeRule_mem_ambGrammar {e : ℕ × List (ℕ ⊕ (α ⊕ ℕ))} (he : e ∈ (ambGrammar P).rules) :
    EncodedCFG.decodeRule e ∈ (ambGrammar P).toCFG.rules :=
  EncodedCFG.mem_toCFG_rules.mpr ⟨e, he, rfl⟩

omit [DecidableEq α] in
theorem cases_of_mem_sideRules {side : Domino α → List α} {A : ℕ}
    {e : ℕ × List (ℕ ⊕ (α ⊕ ℕ))} (he : e ∈ sideRules side A P) :
    ∃ i < P.length, e = contRule side A P i ∨ e = termRule side A P i := by
  obtain ⟨i, hi, he⟩ := List.mem_flatMap.mp he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  exact ⟨i, List.mem_range.mp hi, he⟩

/-- **The productions of $A$ and $B$ in the ambiguity grammar.** Let
$P = [(t_0, b_0), \dots, (t_{m-1}, b_{m-1})]$ be a list of dominoes, and let $A$, $B$ be the
nonterminals of the ambiguity grammar of $P$ for its top and bottom words. Every production of
that grammar with left-hand side $A$ is $A \to t_i\, A\, i$ or $A \to t_i\, i$ for some $i < m$,
and every production with left-hand side $B$ is $B \to b_i\, B\, i$ or $B \to b_i\, i$ for some
$i < m$. -/
theorem cases_of_mem_ambGrammar_of_input {side : Domino α → List α} {A : ℕ}
    (hA : (A = 1 ∧ side = Prod.fst) ∨ (A = 2 ∧ side = Prod.snd))
    {r : ContextFreeRule (α ⊕ ℕ) ℕ} (hr : r ∈ (ambGrammar P).toCFG.rules) (hin : r.input = A) :
    ∃ i < P.length, r = EncodedCFG.decodeRule (contRule side A P i) ∨
      r = EncodedCFG.decodeRule (termRule side A P i) := by
  obtain ⟨e, he, rfl⟩ := EncodedCFG.mem_toCFG_rules.mp hr
  simp only [ambGrammar, List.mem_cons, List.mem_append] at he
  rcases he with rfl | rfl | he | he
  · rcases hA with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> cases hin
  · rcases hA with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> cases hin
  · obtain ⟨i, hi, rfl | rfl⟩ := cases_of_mem_sideRules he
    · rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, -⟩
      · exact ⟨i, hi, Or.inl rfl⟩
      · cases hin
    · rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, -⟩
      · exact ⟨i, hi, Or.inr rfl⟩
      · cases hin
  · obtain ⟨i, hi, rfl | rfl⟩ := cases_of_mem_sideRules he
    · rcases hA with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
      · cases hin
      · exact ⟨i, hi, Or.inl rfl⟩
    · rcases hA with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
      · cases hin
      · exact ⟨i, hi, Or.inr rfl⟩

/-- **Leftmost derivations from $A$ and $B$ follow an index sequence.** Let
$P = [(t_0, b_0), \dots, (t_{m-1}, b_{m-1})]$ be a list of dominoes, let $A$, $B$ be the
nonterminals of the ambiguity grammar of $P$ for its top and bottom words, and let $u$, $v$ be
words of terminals. Every leftmost derivation of a word $w$ from the sentential form $u\,A\,v$ is
the canonical rule sequence from $A$ for the words $t_i$ along some nonempty sequence
$i_1, \dots, i_n$ of indices less than $m$, and
$w = u\, t_{i_1} \cdots t_{i_n}\, i_n \cdots i_1\, v$. Likewise, every leftmost derivation of $w$
from $u\,B\,v$ is the canonical rule sequence from $B$ for the words $b_i$ along such a sequence,
and $w = u\, b_{i_1} \cdots b_{i_n}\, i_n \cdots i_1\, v$. -/
theorem eq_canon_of_leftDerivation {side : Domino α → List α} {A : ℕ}
    (hA : (A = 1 ∧ side = Prod.fst) ∨ (A = 2 ∧ side = Prod.snd))
    {s : List (Symbol (α ⊕ ℕ) (ambGrammar P).toCFG.NT)} {w : List (α ⊕ ℕ)}
    {rs : List (ContextFreeRule (α ⊕ ℕ) (ambGrammar P).toCFG.NT)}
    (h : LeftDerivation (ambGrammar P).toCFG s w rs) :
    ∀ pre suf : List (α ⊕ ℕ),
      s = pre.map Symbol.terminal ++ Symbol.nonterminal A :: suf.map Symbol.terminal →
      ∃ is : List ℕ, is ≠ [] ∧ (∀ i ∈ is, i < P.length) ∧ rs = canon side A P is ∧
        w = pre ++ sideWord side P is ++ suf := by
  induction h with
  | done w =>
    intro pre suf hs
    have : Symbol.nonterminal A ∈ w.map (Symbol.terminal (N := ℕ)) := by rw [hs]; simp
    simp at this
  | @step p v w r rs hr hrest ih =>
    intro pre suf hs
    obtain ⟨rfl, hin, rfl⟩ := eq_of_map_terminal_append_cons hs
    obtain ⟨i, hi, rfl | rfl⟩ := cases_of_mem_ambGrammar_of_input hA hr hin
    · -- `A → wᵢ A i`
      obtain ⟨is, hne, hlt, rfl, rfl⟩ := ih (p ++ (side (domino P i)).map Sum.inl)
        (Sum.inr i :: suf) (by rw [decodeRule_contRule]; simp)
      refine ⟨i :: is, List.cons_ne_nil _ _, ?_, (canon_cons hne).symm, ?_⟩
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hi
        · exact hlt j hj
      · simp [sideWord, flat, List.append_assoc]
    · -- `A → wᵢ i`
      rw [decodeRule_termRule] at hrest
      obtain ⟨rfl, rfl⟩ := LeftDerivation.eq_of_terminal (u := p ++
        (side (domino P i)).map Sum.inl ++ Sum.inr i :: suf)
        (by simpa [Function.comp_def] using hrest)
      exact ⟨[i], List.cons_ne_nil _ _, by simpa using hi, rfl, by simp [sideWord, flat]⟩

/-- **The leftmost derivation along an index sequence.** Let
$P = [(t_0, b_0), \dots, (t_{m-1}, b_{m-1})]$ be a list of dominoes, and let $A$, $B$ be the
nonterminals of the ambiguity grammar of $P$ for its top and bottom words. For every nonempty
sequence $i_1, \dots, i_n$ of indices less than $m$ and all words of terminals $u$, $v$, the
canonical rule sequence from $A$ for the words $t_i$ along $i_1, \dots, i_n$ is a leftmost
derivation of $u\, t_{i_1} \cdots t_{i_n}\, i_n \cdots i_1\, v$ from $u\,A\,v$, and the canonical
rule sequence from $B$ for the words $b_i$ along $i_1, \dots, i_n$ is a leftmost derivation of
$u\, b_{i_1} \cdots b_{i_n}\, i_n \cdots i_1\, v$ from $u\,B\,v$. -/
theorem leftDerivation_canon {side : Domino α → List α} {A : ℕ}
    (hA : (A = 1 ∧ side = Prod.fst) ∨ (A = 2 ∧ side = Prod.snd)) :
    ∀ is : List ℕ, is ≠ [] → (∀ i ∈ is, i < P.length) → ∀ pre suf : List (α ⊕ ℕ),
      LeftDerivation (ambGrammar P).toCFG
        (pre.map Symbol.terminal ++ Symbol.nonterminal A :: suf.map Symbol.terminal)
        (pre ++ sideWord side P is ++ suf) (canon side A P is) := by
  have hmem : ∀ e ∈ sideRules side A P, e ∈ (ambGrammar P).rules := by
    intro e he
    rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [ambGrammar, he]
  intro is
  induction is with
  | nil => exact fun hne ↦ absurd rfl hne
  | cons i is ih =>
    intro _ hlt pre suf
    have hi : i < P.length := hlt i List.mem_cons_self
    rcases eq_or_ne is [] with rfl | hne
    · -- `A → wᵢ i`
      have hr := decodeRule_mem_ambGrammar (hmem _
        (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, by simp⟩) : termRule side A P i ∈ _)
      have hd := LeftDerivation.done (g := (ambGrammar P).toCFG)
        (pre ++ sideWord side P [i] ++ suf)
      have e : (pre ++ sideWord side P [i] ++ suf).map Symbol.terminal =
          pre.map Symbol.terminal ++ (EncodedCFG.decodeRule (termRule side A P i)).output ++
            suf.map Symbol.terminal := by
        rw [decodeRule_termRule]
        simp [sideWord, flat, Function.comp_def]
      rw [e] at hd
      exact LeftDerivation.step hr hd
    · -- `A → wᵢ A i`
      have hr := decodeRule_mem_ambGrammar (hmem _
        (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, by simp⟩) : contRule side A P i ∈ _)
      have hd := ih hne (fun j hj ↦ hlt j (List.mem_cons_of_mem _ hj))
        (pre ++ (side (domino P i)).map Sum.inl) (Sum.inr i :: suf)
      have e₁ : (pre ++ (side (domino P i)).map Sum.inl).map Symbol.terminal ++
          Symbol.nonterminal A :: (Sum.inr i :: suf).map Symbol.terminal =
          pre.map Symbol.terminal ++ (EncodedCFG.decodeRule (contRule side A P i)).output ++
            suf.map Symbol.terminal := by
        rw [decodeRule_contRule]
        simp [Function.comp_def]
      have e₂ : pre ++ (side (domino P i)).map Sum.inl ++ sideWord side P is ++ Sum.inr i :: suf =
          pre ++ sideWord side P (i :: is) ++ suf := by
        simp [sideWord, flat, List.append_assoc]
      rw [e₁, e₂] at hd
      rw [canon_cons hne]
      exact LeftDerivation.step hr hd

/-- **The start production $S \to A$.** For an alphabet $\alpha$ and a natural number $A$, this is
the production with terminals $\alpha \sqcup \mathbb{N}$ and nonterminals $\mathbb{N}$ whose
left-hand side is the nonterminal $S = 0$ and whose right-hand side is the single nonterminal $A$.

In the ambiguity grammar of a PCP instance it is used with $A = 1$ and $A = 2$. -/
def startRule (A : ℕ) : ContextFreeRule (α ⊕ ℕ) ℕ := ⟨0, [Symbol.nonterminal A]⟩

/-- **Leftmost derivations in the ambiguity grammar.** Let
$P = [(t_0, b_0), \dots, (t_{m-1}, b_{m-1})]$ be a list of dominoes, and let $S$, $A$, $B$ be the
nonterminals of the ambiguity grammar of $P$. Every leftmost derivation of a word $w$ from $S$ in
that grammar has one of two forms, for some nonempty sequence $i_1, \dots, i_n$ of indices less
than $m$: either it is $S \to A$ followed by the canonical rule sequence from $A$ for the words
$t_i$ along $i_1, \dots, i_n$, and $w = t_{i_1} \cdots t_{i_n}\, i_n \cdots i_1$; or it is
$S \to B$ followed by the canonical rule sequence from $B$ for the words $b_i$ along
$i_1, \dots, i_n$, and $w = b_{i_1} \cdots b_{i_n}\, i_n \cdots i_1$. -/
theorem cases_of_leftDerivation_start {w : List (α ⊕ ℕ)}
    {rs : List (ContextFreeRule (α ⊕ ℕ) (ambGrammar P).toCFG.NT)}
    (h : LeftDerivation (ambGrammar P).toCFG [Symbol.nonterminal 0] w rs) :
    ∃ A side, ((A = 1 ∧ side = Prod.fst) ∨ (A = 2 ∧ side = Prod.snd)) ∧
      ∃ is : List ℕ, is ≠ [] ∧ (∀ i ∈ is, i < P.length) ∧
        rs = startRule A :: canon side A P is ∧ w = sideWord side P is := by
  generalize hs :
    ([Symbol.nonterminal 0] : List (Symbol (α ⊕ ℕ) (ambGrammar P).toCFG.NT)) = s at h
  cases h with
  | done w =>
    have : Symbol.nonterminal 0 ∈ w.map (Symbol.terminal (N := ℕ)) := by rw [← hs]; simp
    simp at this
  | @step p v w r rs hr hrest =>
    obtain ⟨rfl, hin, rfl⟩ := eq_of_map_terminal_append_cons (pre := []) (v' := []) hs.symm
    obtain ⟨e, he, rfl⟩ := EncodedCFG.mem_toCFG_rules.mp hr
    simp only [ambGrammar, List.mem_cons, List.mem_append] at he
    rcases he with rfl | rfl | he | he
    · obtain ⟨is, hne, hlt, rfl, rfl⟩ :=
        eq_canon_of_leftDerivation (Or.inl ⟨rfl, rfl⟩) hrest [] [] rfl
      exact ⟨1, Prod.fst, Or.inl ⟨rfl, rfl⟩, is, hne, hlt, rfl, by simp⟩
    · obtain ⟨is, hne, hlt, rfl, rfl⟩ :=
        eq_canon_of_leftDerivation (Or.inr ⟨rfl, rfl⟩) hrest [] [] rfl
      exact ⟨2, Prod.snd, Or.inr ⟨rfl, rfl⟩, is, hne, hlt, rfl, by simp⟩
    · obtain ⟨i, -, rfl | rfl⟩ := cases_of_mem_sideRules he <;> cases hin
    · obtain ⟨i, -, rfl | rfl⟩ := cases_of_mem_sideRules he <;> cases hin

/-- **Leftmost derivations from the start symbol along an index sequence.** Let
$P = [(t_0, b_0), \dots, (t_{m-1}, b_{m-1})]$ be a list of dominoes, and let $S$, $A$, $B$ be the
nonterminals of the ambiguity grammar of $P$. For every nonempty sequence $i_1, \dots, i_n$ of
indices less than $m$, the production $S \to A$ followed by the canonical rule sequence from $A$
for the words $t_i$ along $i_1, \dots, i_n$ is a leftmost derivation of
$t_{i_1} \cdots t_{i_n}\, i_n \cdots i_1$ from $S$, and the production $S \to B$ followed by the
canonical rule sequence from $B$ for the words $b_i$ along $i_1, \dots, i_n$ is a leftmost
derivation of $b_{i_1} \cdots b_{i_n}\, i_n \cdots i_1$ from $S$. -/
theorem leftDerivation_start {A : ℕ} {side : Domino α → List α}
    (hA : (A = 1 ∧ side = Prod.fst) ∨ (A = 2 ∧ side = Prod.snd)) {is : List ℕ} (hne : is ≠ [])
    (hlt : ∀ i ∈ is, i < P.length) :
    LeftDerivation (ambGrammar P).toCFG [Symbol.nonterminal 0] (sideWord side P is)
      (startRule A :: canon side A P is) := by
  have hr : startRule A ∈ (ambGrammar P).toCFG.rules := by
    refine EncodedCFG.mem_toCFG_rules.mpr ⟨(0, [ntSym A]), ?_, rfl⟩
    rcases hA with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [ambGrammar]
  have hd := leftDerivation_canon hA is hne hlt [] []
  simp only [List.map_nil, List.nil_append, List.append_nil] at hd
  exact LeftDerivation.step (p := []) (v := []) hr hd

omit [DecidableEq α] in
theorem eq_of_sideWord_eq {side : Domino α → List α} {is js : List ℕ}
    (h : sideWord side P is = sideWord side P js) : is = js :=
  List.reverse_injective (eq_of_map_inl_append_map_inr h).2

/-- **The ambiguity grammar of $P$ is ambiguous exactly when $P$ has a solution.** For every list
$P$ of dominoes, the ambiguity grammar of $P$ is ambiguous, that is, some word has two different
leftmost derivations from its start symbol, if and only if $P$ has a PCP solution. -/
theorem isAmbiguous_iff_pcp (P : List (Domino α)) : IsAmbiguous (ambGrammar P).toCFG ↔ PCP P := by
  constructor
  · rintro ⟨w, rs₁, rs₂, hne, h₁, h₂⟩
    obtain ⟨A₁, side₁, hA₁, is₁, hne₁, hlt₁, rfl, rfl⟩ := cases_of_leftDerivation_start h₁
    obtain ⟨A₂, side₂, hA₂, is₂, -, hlt₂, rfl, hw⟩ := cases_of_leftDerivation_start h₂
    have hmem : ∀ {A side}, ((A = 1 ∧ side = Prod.fst) ∨ (A = 2 ∧ side = Prod.snd)) →
        ∀ {is : List ℕ}, is ≠ [] → (∀ i ∈ is, i < P.length) →
          sideWord side P is ∈ (sideGrammar side P).language :=
      fun {_ _} _ {is} hne hlt ↦ mem_language_sideGrammar.mpr ⟨is, hne, hlt, rfl⟩
    have hne₂ : is₂ ≠ [] := by
      rintro rfl
      have := congrArg List.length hw
      simp only [sideWord, flat, List.length_append, List.length_map, List.length_reverse,
        List.flatMap_nil, List.reverse_nil, List.map_nil, List.length_nil] at this
      exact hne₁ (List.eq_nil_of_length_eq_zero (by omega))
    rcases hA₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hA₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (hne (by rw [eq_of_sideWord_eq hw])).elim
    · exact (pcp_iff_exists_mem_inter P).mpr ⟨_, hmem (Or.inl ⟨rfl, rfl⟩) hne₁ hlt₁,
        hw ▸ hmem (Or.inr ⟨rfl, rfl⟩) hne₂ hlt₂⟩
    · exact (pcp_iff_exists_mem_inter P).mpr ⟨_, hw ▸ hmem (Or.inl ⟨rfl, rfl⟩) hne₂ hlt₂,
        hmem (Or.inr ⟨rfl, rfl⟩) hne₁ hlt₁⟩
    · exact (hne (by rw [eq_of_sideWord_eq hw])).elim
  · intro h
    obtain ⟨w, h₁, h₂⟩ := (pcp_iff_exists_mem_inter P).mp h
    obtain ⟨is, hne, hlt, rfl⟩ := mem_language_sideGrammar.mp h₁
    obtain ⟨js, hne', hlt', hw⟩ := mem_language_sideGrammar.mp h₂
    refine ⟨_, _, _, ?_, leftDerivation_start (Or.inl ⟨rfl, rfl⟩) hne hlt,
      hw ▸ leftDerivation_start (Or.inr ⟨rfl, rfl⟩) hne' hlt'⟩
    intro heq
    have := (List.cons.inj heq).1
    simp [startRule] at this

end Derivations

/-! ### The many-one reduction -/

/-- **The ambiguity grammar is primitive recursive.** For every alphabet $\alpha$ with a
primitive recursive encoding by natural numbers, the map sending a list $P$ of dominoes over
$\alpha$ to the ambiguity grammar of $P$ is primitive recursive, where encoded grammars are
encoded as pairs of a start nonterminal and a list of productions. -/
theorem primrec_ambGrammar [Primcodable α] : Primrec (ambGrammar (α := α)) :=
  EncodedCFG.primrec₂_mk.comp (Primrec.const 0) (Primrec.list_cons.comp (Primrec.const _)
    (Primrec.list_cons.comp (Primrec.const _) (Primrec.list_append.comp
      (primrec_sideRules Primrec.fst 1) (primrec_sideRules Primrec.snd 2))))

/-- **PCP many-one reduces to ambiguity of context-free grammars.** For every alphabet $\alpha$
with a primitive recursive encoding by natural numbers and decidable equality, the Post
correspondence problem over $\alpha$ many-one reduces to ambiguity of encoded context-free
grammars over the terminals $\alpha \sqcup \mathbb{N}$: there is a computable function sending
each list $P$ of dominoes over $\alpha$ to such a grammar, which is ambiguous if and only if $P$
has a PCP solution. -/
theorem manyOneReducible_pcp_isAmbiguous [Primcodable α] [DecidableEq α] :
    ManyOneReducible (PCP (α := α)) fun g : EncodedCFG (α ⊕ ℕ) ↦ IsAmbiguous g.toCFG :=
  ⟨ambGrammar, primrec_ambGrammar.to_comp, fun P ↦ (isAmbiguous_iff_pcp P).symm⟩

end Cslib.Decidability.Grammar
