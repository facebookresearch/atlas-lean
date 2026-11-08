/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Equivalence of regular expressions is decidable
-/
module

public import CSLibExt.Computability.Automata.EpsilonNA.Thompson
public import CSLibExt.Computability.Decidability.Regular
public import CSLibExt.Computability.Decidability.RegularExpression
public import Mathlib.Data.Fintype.Powerset

/-!
# Equivalence of regular expressions is decidable (EQ_REX)

Two regular expressions denote the same language exactly when they agree on every word shorter
than a bound computed from the expressions. Equivalence of encoded regular expressions
(`Cslib.Language.EncodedRegex`) is therefore decided by bounded search: run the A_REX decider
`EncodedRegex.memB` on both expressions for every word below the bound and compare the answers.
This is the regular-expression analogue of EQ_DFA (M. Sipser, *Introduction to the Theory of
Computation*, 3rd ed., Theorem 4.5), decided there by testing the symmetric difference of two
DFAs for emptiness. Here no automaton is built: the automata appear only in the proof of the
bound.

The bound comes from three constructions. The (compact) Thompson ε-NFA of `r`
(`Thompson.toεNFA`) has `Thompson.numStates r` states (`Thompson.card_state`); Mathlib's
`εNFA.toNFA` keeps them and the subset construction `NFA.toDFA` gives a DFA on
`Set (Thompson.State r)`, with `2 ^ card (State r)` states. The product DFA `DFA.symmDiff` of the DFAs of `r` and `s` accepts the words on which
`r` and `s` disagree, and a DFA with `n` states that accepts some word accepts one of length
`< n` (pump down with `DFA.pumping_lemma`). So expressions with different languages disagree
on a word of length `< 2 ^ (card (State r) + card (State s))`.

An encoding shares subterms, so its expression tree can be exponentially larger than its node
list; the number of Thompson states is computed by one left-to-right pass over the nodes, like
the flags of `EncodedRegex.infiniteB`. That number is the size of the expression tree, which
can be exponential in the number of nodes, and the search runs over all words shorter than a bound
exponential in it, so the bound is doubly exponential in the size of the encoding: a
decidability proof, not a practical algorithm.

## Main results

* `Thompson.matches'_eq_iff_forall_length_lt`: two regular expressions denote the same language
  iff they agree on all words of length `< 2 ^ (numStates r + numStates s)`.
* `EncodedRegex.numThompsonStates`, `EncodedRegex.numThompsonStates_eq`: the same count for an
  encoding, by a pass over the nodes (`EncodedRegex.stateCounts`).
* `EncodedRegex.eqB`, `EncodedRegex.eqB_iff`: the equivalence test, over a finite alphabet
  (`FinEnum`), with the words of each length from `EncodedDFA.wordsOfLength`.
* `EncodedRegex.primrec_eqB`, `EncodedRegex.tm2Decidable_matches_eq`: equivalence of regular
  expressions (EQ_REX) is decidable by a multi-stack machine, over a finite alphabet.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Theorem 4.5 (EQ_DFA); its
  proof applies to regular expressions once they are converted to DFAs.
* K. Thompson, *Regular expression search algorithm*, CACM 11(6), 1968.
-/

@[expose] public section

set_option autoImplicit false

/-! ## Short witnesses and the bound for Mathlib's regular expressions -/

namespace Cslib.Automata.Thompson

variable {α : Type*}

/-- A DFA with finitely many states that accepts some word accepts one shorter than its number
of states: pump the word down until it is short. -/
private theorem exists_mem_accepts_length_lt {σ : Type*} [Fintype σ] (M : DFA α σ) :
    ∀ (n : ℕ) (w : List α), w.length = n → w ∈ M.accepts →
      ∃ v ∈ M.accepts, v.length < Fintype.card σ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hn hw
    by_cases hlt : w.length < Fintype.card σ
    · exact ⟨w, hw, hlt⟩
    · obtain ⟨a, b, c, rfl, -, hb, hsub⟩ := M.pumping_lemma hw (not_lt.1 hlt)
      have hac : a ++ c ∈ M.accepts :=
        hsub (Language.mem_mul.2 ⟨a, Language.mem_mul.2 ⟨a, rfl, [],
          Language.nil_mem_kstar _, by simp⟩, c, rfl, rfl⟩)
      have hbpos : 0 < b.length := List.length_pos_iff.2 hb
      simp only [List.length_append] at hn
      exact ih (a ++ c).length (by simp only [List.length_append]; omega) (a ++ c) rfl hac

/-- **Short distinguishing words**: two regular expressions denote the same language iff they
agree on every word of length `< 2 ^ (numStates r + numStates s)`. The bound is the number of
states of the product of the subset-construction DFAs of the Thompson automata. -/
theorem matches'_eq_iff_forall_length_lt {r s : RegularExpression α} :
    r.matches' = s.matches' ↔ ∀ w : List α, w.length < 2 ^ (numStates r + numStates s) →
      (w ∈ r.matches' ↔ w ∈ s.matches') := by
  refine ⟨fun h w _ => by rw [h], fun h => ?_⟩
  set M := (toεNFA r).toNFA.toDFA
  set N := (toεNFA s).toNFA.toDFA
  have hM : M.accepts = r.matches' := by
    rw [NFA.toDFA_correct, εNFA.toNFA_correct, accepts_toεNFA]
  have hN : N.accepts = s.matches' := by
    rw [NFA.toDFA_correct, εNFA.toNFA_correct, accepts_toεNFA]
  have hdiff : ∀ w, w ∈ (M.symmDiff N).accepts ↔ ¬ (w ∈ r.matches' ↔ w ∈ s.matches') := by
    intro w
    rw [DFA.mem_accepts, DFA.eval_symmDiff, ← hM, ← hN, DFA.mem_accepts, DFA.mem_accepts]
    rfl
  by_contra hne
  obtain ⟨w, hw⟩ : ∃ w, w ∈ (M.symmDiff N).accepts := by
    by_contra hc
    refine hne (Set.ext fun w => ?_)
    by_contra hw
    exact hc ⟨w, (hdiff w).2 hw⟩
  obtain ⟨v, hv, hlen⟩ := exists_mem_accepts_length_lt (M.symmDiff N) _ w rfl hw
  rw [Fintype.card_prod, Fintype.card_set, Fintype.card_set, card_state, card_state,
    ← pow_add] at hlen
  exact (hdiff v).1 hv (h v hlen)

end Cslib.Automata.Thompson

/-! ## The bound for encoded regular expressions -/

namespace Cslib.Language.EncodedRegex

open Cslib.Decidability Cslib.Automata

variable {α : Type*}

/-- The number of Thompson states of a node, from the counts `acc` of the nodes before it; an
argument that is not an earlier node counts `0`, as the expression `0` does. -/
def stepStates (acc : List ℕ) : RegexNode α → ℕ
  | .zero => 0
  | .epsilon => 1
  | .char _ => 2
  | .plus i j => acc.getD i 0 + acc.getD j 0
  | .comp i j => acc.getD i 0 + acc.getD j 0
  | .star i => acc.getD i 0 + 1

/-- The Thompson state counts of all nodes, in one left-to-right pass. -/
def stateCounts (l : List (RegexNode α)) : List ℕ :=
  l.foldl (fun acc n => acc ++ [stepStates acc n]) []

/-- The number of states of Thompson's automaton of the expression: the count of the root. -/
def numThompsonStates (e : EncodedRegex α) : ℕ :=
  (stateCounts e.nodes).getD (e.nodes.length - 1) 0

/-- The pass computes one count per node. -/
theorem length_stateCounts (l : List (RegexNode α)) : (stateCounts l).length = l.length := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l n ih =>
      rw [stateCounts, List.foldl_append, ← stateCounts]
      simp [ih]

/-- One more node appends its count. -/
theorem stateCounts_append_singleton (l : List (RegexNode α)) (n : RegexNode α) :
    stateCounts (l ++ [n]) = stateCounts l ++ [stepStates (stateCounts l) n] := by
  rw [stateCounts, List.foldl_append, ← stateCounts]
  rfl

/-- The count of every node is the number of Thompson states of its expression (`0` past the
end). -/
theorem getD_stateCounts (l : List (RegexNode α)) :
    ∀ k, (stateCounts l).getD k 0 =
      Thompson.numStates (if k < l.length then (⟨l⟩ : EncodedRegex α).regexAt k else 0) := by
  induction l using List.reverseRecOn with
  | nil =>
      intro k
      rfl
  | append_singleton l n ih =>
      intro k
      rw [stateCounts_append_singleton]
      rcases lt_trichotomy k l.length with hk | rfl | hk
      · have hk' : k < l.length + 1 := by omega
        rw [List.getD_append _ _ _ _ (by rwa [length_stateCounts]), List.length_append,
          List.length_singleton]
        simp only [hk', ↓reduceIte, regexAt_append hk]
        simpa [hk] using ih k
      · rw [List.getD_append_right _ _ _ _ (by rw [length_stateCounts]), length_stateCounts,
          Nat.sub_self, List.length_append, List.length_singleton]
        simp only [Nat.lt_add_one, ↓reduceIte, List.getD_cons_zero]
        have hnode : (⟨l ++ [n]⟩ : EncodedRegex α).node l.length = n := by
          simp [node]
        have harg : ∀ i, (stateCounts l).getD i 0 = Thompson.numStates
            (if i < l.length then (⟨l ++ [n]⟩ : EncodedRegex α).regexAt i else 0) := fun i => by
          rw [ih i]
          split_ifs with hi
          exacts [by rw [regexAt_append hi], rfl]
        cases n with
        | zero => rw [regexAt_of_zero hnode]; rfl
        | epsilon => rw [regexAt_of_epsilon hnode]; rfl
        | char a => rw [regexAt_of_char hnode]; rfl
        | plus i j => rw [regexAt_of_plus hnode, stepStates, harg, harg]; rfl
        | comp i j => rw [regexAt_of_comp hnode, stepStates, harg, harg]; rfl
        | star i => rw [regexAt_of_star hnode, stepStates, harg]; rfl
      · have hk' : ¬ k < l.length + 1 := by omega
        rw [List.getD_eq_default _ _ (by rw [List.length_append, length_stateCounts]; simp; omega),
          List.length_append, List.length_singleton]
        simp only [hk', ↓reduceIte]
        rfl

/-- **The pass counts the states of Thompson's automaton** of the expression, even when the
expression tree is exponentially larger than the node list. -/
theorem numThompsonStates_eq (e : EncodedRegex α) :
    e.numThompsonStates = Thompson.numStates e.toRegex := by
  rw [numThompsonStates, getD_stateCounts, toRegex]
  rcases Nat.lt_or_ge (e.nodes.length - 1) e.nodes.length with hk | hk
  · simp only [hk, ↓reduceIte]
  · have hk' : ¬ e.nodes.length - 1 < e.nodes.length := by omega
    simp only [hk', ↓reduceIte, regexAt_of_zero (node_of_le hk)]

/-- The search bound for equivalence: `2 ^ (m + n)` for expressions whose Thompson automata
have `m` and `n` states. -/
def eqBound (e₁ e₂ : EncodedRegex α) : ℕ :=
  2 ^ (e₁.numThompsonStates + e₂.numThompsonStates)

/-- Two encoded regular expressions denote the same language iff they agree on every word
shorter than `eqBound`. -/
theorem matches'_eq_iff_forall_length_lt {e₁ e₂ : EncodedRegex α} :
    e₁.toRegex.matches' = e₂.toRegex.matches' ↔ ∀ w : List α, w.length < eqBound e₁ e₂ →
      (w ∈ e₁.toRegex.matches' ↔ w ∈ e₂.toRegex.matches') := by
  rw [eqBound, numThompsonStates_eq, numThompsonStates_eq]
  exact Thompson.matches'_eq_iff_forall_length_lt

/-! ## The decision procedure -/

section Decide

variable [DecidableEq α] [FinEnum α]

/-- **Equivalence test**: the A_REX decider gives the same answer for both expressions on every
word shorter than `eqBound`, enumerated by length. -/
def eqB (e₁ e₂ : EncodedRegex α) : Bool :=
  (List.range (eqBound e₁ e₂)).all fun n =>
    (EncodedDFA.wordsOfLength n).all fun w => e₁.memB w == e₂.memB w

/-- **The equivalence test is correct.** -/
theorem eqB_iff {e₁ e₂ : EncodedRegex α} :
    eqB e₁ e₂ = true ↔ e₁.toRegex.matches' = e₂.toRegex.matches' := by
  rw [eqB, matches'_eq_iff_forall_length_lt]
  simp only [List.all_eq_true, List.mem_range, EncodedDFA.mem_wordsOfLength, beq_iff_eq]
  refine ⟨fun h w hw => ?_, fun h n hn w hw => ?_⟩
  · rw [← memB_iff, ← memB_iff, h _ hw w rfl]
  · rw [Bool.eq_iff_iff, memB_iff, memB_iff]
    exact h w (hw ▸ hn)

end Decide

/-! ## Computability -/

section Computable

variable [Primcodable α]

/-- The count of one node is primitive recursive in the counts before it and the node. -/
theorem primrec_stepStates : Primrec₂ (stepStates (α := α)) := by
  have get : Primrec₂ fun (acc : List ℕ) (i : ℕ) => acc.getD i 0 := Primrec.list_getD 0
  have sum₂ : ∀ {γ : Type _} [Primcodable γ],
      Primrec₂ fun (q : List ℕ × γ) (p : ℕ × ℕ) => q.1.getD p.1 0 + q.1.getD p.2 0 :=
    Primrec.nat_add.comp
      (get.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (get.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
  have h5 : Primrec₂ fun (acc : List ℕ) (s : (ℕ × ℕ) ⊕ ℕ) =>
      Sum.elim (fun p => acc.getD p.1 0 + acc.getD p.2 0) (fun i => acc.getD i 0 + 1) s :=
    (Primrec.sumCasesOn Primrec.snd sum₂
      (Primrec.succ.comp (get.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂).of_eq
      fun p => by rcases p with ⟨acc, _ | _⟩ <;> rfl
  have h4 : Primrec₂ fun (acc : List ℕ) (s : (ℕ × ℕ) ⊕ (ℕ × ℕ) ⊕ ℕ) =>
      Sum.elim (fun p => acc.getD p.1 0 + acc.getD p.2 0)
        (Sum.elim (fun p => acc.getD p.1 0 + acc.getD p.2 0) (fun i => acc.getD i 0 + 1)) s :=
    (Primrec.sumCasesOn Primrec.snd sum₂
      (h5.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq
      fun p => by rcases p with ⟨acc, _ | _⟩ <;> rfl
  have h3 : Primrec₂ fun (acc : List ℕ) (s : α ⊕ (ℕ × ℕ) ⊕ (ℕ × ℕ) ⊕ ℕ) =>
      Sum.elim (fun _ => 2)
        (Sum.elim (fun p => acc.getD p.1 0 + acc.getD p.2 0)
          (Sum.elim (fun p => acc.getD p.1 0 + acc.getD p.2 0)
            (fun i => acc.getD i 0 + 1))) s :=
    (Primrec.sumCasesOn Primrec.snd (Primrec₂.const 2)
      (h4.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq
      fun p => by rcases p with ⟨acc, _ | _⟩ <;> rfl
  have h2 : Primrec₂ fun (acc : List ℕ) (s : Unit ⊕ α ⊕ (ℕ × ℕ) ⊕ (ℕ × ℕ) ⊕ ℕ) =>
      Sum.elim (fun _ => 1)
        (Sum.elim (fun _ => 2)
          (Sum.elim (fun p => acc.getD p.1 0 + acc.getD p.2 0)
            (Sum.elim (fun p => acc.getD p.1 0 + acc.getD p.2 0)
              (fun i => acc.getD i 0 + 1)))) s :=
    (Primrec.sumCasesOn Primrec.snd (Primrec₂.const 1)
      (h3.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq
      fun p => by rcases p with ⟨acc, _ | _⟩ <;> rfl
  have he : Primrec (nodeEquiv (α := α)) := Primrec.of_equiv
  exact (Primrec.sumCasesOn (he.comp Primrec.snd) (Primrec₂.const 0)
    (h2.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq fun p => by
      obtain ⟨acc, n⟩ := p
      cases n <;> rfl

/-- The pass over the nodes is primitive recursive. -/
theorem primrec_stateCounts : Primrec (stateCounts (α := α)) :=
  (Primrec.list_foldl Primrec.id (Primrec.const [])
    (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.list_cons.comp (primrec_stepStates.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)) (Primrec.const []))).to₂).of_eq fun _ => rfl

/-- The number of Thompson states of an encoding is primitive recursive. -/
theorem primrec_numThompsonStates : Primrec (numThompsonStates (α := α)) :=
  ((Primrec.list_getD 0).comp (primrec_stateCounts.comp primrec_nodes)
    (Primrec.pred.comp (Primrec.list_length.comp primrec_nodes))).of_eq fun e => by
      simp only [numThompsonStates, Nat.pred_eq_sub_one]

/-- The search bound is primitive recursive. -/
theorem primrec_eqBound : Primrec₂ (eqBound (α := α)) :=
  (Primrec₂.unpaired'.1 Nat.Primrec.pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ)).comp
    (Primrec.const 2)
    (Primrec.nat_add.comp (primrec_numThompsonStates.comp Primrec.fst)
      (primrec_numThompsonStates.comp Primrec.snd))

/-- The equivalence test is primitive recursive. -/
theorem primrec_eqB [DecidableEq α] [FinEnum α] : Primrec₂ (eqB (α := α)) :=
  primrec_list_all
    (primrec_list_all
      (Primrec.beq.comp₂
        (primrec_memB.comp₂ (Primrec.fst.comp₂ (Primrec.fst.comp₂ Primrec₂.left))
          Primrec₂.right)
        (primrec_memB.comp₂ (Primrec.snd.comp₂ (Primrec.fst.comp₂ Primrec₂.left))
          Primrec₂.right))
      (EncodedDFA.primrec_wordsOfLength.comp Primrec.snd)).to₂
    (Primrec.list_range.comp primrec_eqBound)

/-- **EQ_REX is decidable**: equivalence of regular expressions over a finite alphabet is
decidable by a multi-stack machine (the regular-expression analogue of Sipser, Theorem 4.5),
by bounded search with the A_REX decider. -/
theorem tm2Decidable_matches_eq [Finite α] :
    TM2Decidable fun p : EncodedRegex α × EncodedRegex α =>
      p.1.toRegex.matches' = p.2.toRegex.matches' := by
  classical
  let _ : Fintype α := Fintype.ofFinite α
  let _ : FinEnum α := FinEnum.ofList Finset.univ.toList fun a => by simp
  exact tm2Decidable_iff_computablePred.2
    (computablePred_of_primrec_bool primrec_eqB fun _ => eqB_iff)

end Computable

end Cslib.Language.EncodedRegex
