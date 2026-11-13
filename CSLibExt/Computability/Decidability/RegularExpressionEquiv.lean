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

/-- **Short distinguishing words.** Two regular expressions $r$ and $s$ denote the same language if
and only if every word of length less than $2^{n(r) + n(s)}$, where $n$ denotes the Thompson state
count, is matched by $r$ exactly when it is matched by $s$.

The bound is the number of states of the product of the subset-construction DFAs of the Thompson
automata. -/
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

/-- **One step of the Thompson state count.** Let $c = (c_0, \dots, c_{m-1})$ be a list of
natural numbers, and read $c_i$ as $0$ when $i \ge m$. The Thompson state count of a
regular-expression node from $c$ is $0$ for the node $0$, $1$ for the node $\varepsilon$, $2$ for
a letter, $c_i + c_j$ for a sum node and for a concatenation node with arguments $i$ and $j$, and
$c_i + 1$ for a star node with argument $i$.

When $c$ holds the counts of the nodes before the node, this is the number of states of
Thompson's automaton of its expression; an argument that is not an earlier node counts $0$, as
the expression $0$ does. -/
def stepStates (acc : List ℕ) : RegexNode α → ℕ
  | .zero => 0
  | .epsilon => 1
  | .char _ => 2
  | .plus i j => acc.getD i 0 + acc.getD j 0
  | .comp i j => acc.getD i 0 + acc.getD j 0
  | .star i => acc.getD i 0 + 1

/-- **Thompson state counts of a node list.** For a list $l$ of regular-expression nodes, the
list of Thompson state counts of $l$ is computed in one left-to-right pass: starting from the
empty list, each node $n$ of $l$ in turn appends the count of $n$ computed from the list of
counts built so far. -/
def stateCounts (l : List (RegexNode α)) : List ℕ :=
  l.foldl (fun acc n => acc ++ [stepStates acc n]) []

/-- **Thompson state count of an encoding.** The number of Thompson states of an encoded regular
expression $e$ is the entry of the state counts of the nodes of $e$ at the last node, the root
(read as $0$ when $e$ has no nodes).

It equals the number of states of Thompson's automaton of the expression that $e$ denotes. -/
def numThompsonStates (e : EncodedRegex α) : ℕ :=
  (stateCounts e.nodes).getD (e.nodes.length - 1) 0

/-- **One state count per node.** For every list $l$ of nodes of encoded regular expressions, the
list of state counts of $l$ has the same length as $l$. -/
theorem length_stateCounts (l : List (RegexNode α)) : (stateCounts l).length = l.length := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l n ih =>
      rw [stateCounts, List.foldl_append, ← stateCounts]
      simp [ih]

/-- **Appending a node appends its count.** For every list $l$ of regular-expression nodes and
every node $n$, let $l'$ be the list $l$ with $n$ appended at the end. Then the list of Thompson
state counts of $l'$ is the list of counts of $l$ followed by one more entry, the count of $n$
computed from the counts of $l$. -/
theorem stateCounts_append_singleton (l : List (RegexNode α)) (n : RegexNode α) :
    stateCounts (l ++ [n]) = stateCounts l ++ [stepStates (stateCounts l) n] := by
  rw [stateCounts, List.foldl_append, ← stateCounts]
  rfl

/-- **The pass computes the Thompson state count of every node.** For every list $l$ of nodes and
every index $k$, the entry at index $k$ of the state counts of $l$ (read as $0$ past the end of the
list) equals the Thompson state count of the regular expression at node $k$ of the encoding with
nodes $l$ when $k$ is less than the length of $l$, and $0$ otherwise. -/
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

/-- **The pass counts the states of Thompson's automaton.** For every encoded regular expression
$e$, the number of Thompson states of $e$ computed by the pass over its nodes equals the Thompson
state count of the regular expression that $e$ denotes.

This holds even when the expression tree is exponentially larger than the node list. -/
theorem numThompsonStates_eq (e : EncodedRegex α) :
    e.numThompsonStates = Thompson.numStates e.toRegex := by
  rw [numThompsonStates, getD_stateCounts, toRegex]
  rcases Nat.lt_or_ge (e.nodes.length - 1) e.nodes.length with hk | hk
  · simp only [hk, ↓reduceIte]
  · have hk' : ¬ e.nodes.length - 1 < e.nodes.length := by omega
    simp only [hk', ↓reduceIte, regexAt_of_zero (node_of_le hk)]

/-- **Search bound for equivalence.** For encoded regular expressions $e_1$ and $e_2$, the search
bound is $2^{m + n}$, where $m$ and $n$ are the numbers of Thompson states of $e_1$ and $e_2$, each
computed by one pass over the nodes of the encoding. -/
def eqBound (e₁ e₂ : EncodedRegex α) : ℕ :=
  2 ^ (e₁.numThompsonStates + e₂.numThompsonStates)

/-- **Short distinguishing words for encoded regular expressions.** Let $e_1$ and $e_2$ be encoded
regular expressions over an alphabet $\alpha$, and let $B$ be their search bound for equivalence.
The regular expressions denoted by $e_1$ and $e_2$ match the same language if and only if every
word $w$ over $\alpha$ of length less than $B$ is matched by the expression denoted by $e_1$
exactly when it is matched by the expression denoted by $e_2$. -/
theorem matches'_eq_iff_forall_length_lt {e₁ e₂ : EncodedRegex α} :
    e₁.toRegex.matches' = e₂.toRegex.matches' ↔ ∀ w : List α, w.length < eqBound e₁ e₂ →
      (w ∈ e₁.toRegex.matches' ↔ w ∈ e₂.toRegex.matches') := by
  rw [eqBound, numThompsonStates_eq, numThompsonStates_eq]
  exact Thompson.matches'_eq_iff_forall_length_lt

/-! ## The decision procedure -/

section Decide

variable [DecidableEq α] [FinEnum α]

/-- **Equivalence test.** Over a finite alphabet with decidable equality and a fixed enumeration of
its letters, the equivalence test of two encoded regular expressions $e_1$ and $e_2$ returns true
exactly when, for every length $n$ less than the search bound of $e_1$ and $e_2$ and every word $w$
of length $n$, the membership test gives the same answer for $e_1$ on $w$ as for $e_2$ on $w$. -/
def eqB (e₁ e₂ : EncodedRegex α) : Bool :=
  (List.range (eqBound e₁ e₂)).all fun n =>
    (EncodedDFA.wordsOfLength n).all fun w => e₁.memB w == e₂.memB w

/-- **The equivalence test is correct.** Over a finite alphabet with decidable equality and a fixed
enumeration of its letters, for all encoded regular expressions $e_1$ and $e_2$, the equivalence
test returns true on $e_1$ and $e_2$ if and only if the regular expressions that $e_1$ and $e_2$
denote have the same language. -/
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

/-- **One step of the Thompson state count is primitive recursive.** For an alphabet $\alpha$
with a primitive recursive encoding, the map sending a list $c$ of natural numbers and a
regular-expression node over $\alpha$ to the Thompson state count of the node computed from $c$
is primitive recursive. -/
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

/-- **The pass of Thompson state counts is primitive recursive.** For an alphabet $\alpha$ with a
primitive recursive encoding, the map sending a list of regular-expression nodes over $\alpha$ to
the list of their Thompson state counts, computed in one left-to-right pass, is primitive
recursive. -/
theorem primrec_stateCounts : Primrec (stateCounts (α := α)) :=
  (Primrec.list_foldl Primrec.id (Primrec.const [])
    (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.list_cons.comp (primrec_stepStates.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)) (Primrec.const []))).to₂).of_eq fun _ => rfl

/-- **The Thompson state count of an encoding is primitive recursive.** For an alphabet $\alpha$
with a primitive recursive encoding, the number of states of Thompson's automaton of an encoded
regular expression over $\alpha$, computed by one pass over its nodes, is a primitive recursive
function of the encoding. -/
theorem primrec_numThompsonStates : Primrec (numThompsonStates (α := α)) :=
  ((Primrec.list_getD 0).comp (primrec_stateCounts.comp primrec_nodes)
    (Primrec.pred.comp (Primrec.list_length.comp primrec_nodes))).of_eq fun e => by
      simp only [numThompsonStates, Nat.pred_eq_sub_one]

/-- **The equivalence search bound is primitive recursive.** For an alphabet $\alpha$ with a
primitive recursive encoding, the search bound $2^{m+n}$ for equivalence of two encoded regular
expressions over $\alpha$, where $m$ and $n$ are the numbers of states of Thompson's automata of
the two expressions, is a primitive recursive function of the pair of encoded expressions. -/
theorem primrec_eqBound : Primrec₂ (eqBound (α := α)) :=
  (Primrec₂.unpaired'.1 Nat.Primrec.pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ)).comp
    (Primrec.const 2)
    (Primrec.nat_add.comp (primrec_numThompsonStates.comp Primrec.fst)
      (primrec_numThompsonStates.comp Primrec.snd))

/-- **The equivalence test is primitive recursive.** Over a primitively encodable finite alphabet
with decidable equality and a fixed enumeration of its letters, the equivalence test, as a function
of two encoded regular expressions, is primitive recursive. -/
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

/-- **EQ_REX is decidable.** Let $\alpha$ be a finite alphabet with a primitive recursive
encoding. Then equivalence of encoded regular expressions over $\alpha$ is decidable by a
multi-stack machine: some multi-stack machine decides, for a pair $(e_1, e_2)$ of encoded
regular expressions over $\alpha$, whether the regular expressions that $e_1$ and $e_2$ denote
have the same language.

This is the regular-expression analogue of Sipser, Theorem 4.5 (EQ_DFA). It is proved by
bounded search: the membership decider is run on both expressions for every word shorter than
a bound computed from them, and the answers are compared. -/
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
