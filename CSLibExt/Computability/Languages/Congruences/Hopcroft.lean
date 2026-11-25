/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hopcroft's minimization algorithm
-/
module

public import CSLibExt.Computability.Languages.Congruences.Moore
public import Mathlib.Data.FinEnum
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

/-!
# Hopcroft's minimization algorithm

J. E. Hopcroft, *An `n log n` algorithm for minimizing states in a finite automaton*, Theory of
Machines and Computations, 1971; the presentation follows Berstel, Boasson, Carton and Fagnot,
*Minimization of automata* (2010). For a Mathlib `DFA` with finitely many states over a finite,
enumerated alphabet, Hopcroft's algorithm refines the partition `{F, Q \ F}` of the states into
accepting and rejecting ones. It keeps a waiting list of splitters `(C, a)`, a block `C` and a
letter `a`: it pops one, splits every block `D` into the states whose `a`-successor is in `C` and
the others, and updates the waiting list. When a split block `D` is waiting with a letter `b`, both
halves replace it; otherwise only the **smaller half** is added (Hopcroft's rule, the source of
his `O(n log n)` bound). It stops when the waiting list is empty.

## Main definitions

* `DFA.hopcroftLoop`: the refinement loop on a partition `P` (a list of blocks) and a waiting list
  `W`, for a given number of rounds.
* `DFA.hopcroftPartition M`: the final partition, after at most `|Σ| (|Q| + 1)` rounds from
  `{F, Q \ F}` with the smaller of the two blocks waiting with every letter.
* `DFA.hopcroftRel M`: the pairs of states in a common final block.

## Main results

* `DFA.hopcroftLoop_waiting_eq_nil`: the waiting list is empty after `|Σ| (|Q| + 1)` rounds.
  Each round lowers `|W| + |Σ| (|Q| - |P|)` by at least one.
* `DFA.mem_hopcroftRel_iff`: two states are in a common final block exactly when they accept the
  same continuation languages (`DFA.acceptsFrom`).
* `DFA.hopcroftRel_eq_mooreRel`: **Hopcroft's partition is Moore's relation**, so the quotient of
  the reachable states by it is Moore's automaton `DFA.mooreDFA`, which `DFA.reindex_mooreDFA`
  identifies with `Cslib.Language.minimizedDFA M`; `DFA.mooreClass_eq_iff_mem_hopcroftRel`
  states this on classes.
* `DFA.mem_block_iff`: each final block is a class of states with one continuation language.

The proof keeps five invariants (`DFA.Hopcroft.Inv`): `P` is a partition into nonempty blocks;
every waiting set is a block; states with one continuation language share a block; blocks agree on
acceptance; and, for every letter `b`, two states in one block whose `b`-successors agree on every
set waiting with `b` have `b`-successors in one block. The last holds with the smaller-half rule
because a waiting half and its parent block determine the other half. With an empty waiting list it
says that the partition is a right congruence, so every block has one continuation language.

## Cost model

No cost bound beyond the round count: the `O(|Σ| n log n)` analysis of the smaller-half rule is not
formalized. Each round scans the partition and the waiting list.
-/

@[expose] public section

namespace DFA

variable {α σ : Type*} [Fintype α] [FinEnum α] [Fintype σ] [DecidableEq σ] (M : DFA α σ)
  [DecidablePred (· ∈ M.accept)]

namespace Hopcroft

/-- **Preimage of a set under a letter.** For a DFA $M$ with transition function $\delta$, a set
$C$ of states and a letter $a$, the preimage of $C$ under $a$ is the set of states $q$ with
$\delta(q, a) \in C$. -/
def preimage (C : Finset σ) (a : α) : Finset σ :=
  Finset.univ.filter fun q => M.step q a ∈ C

omit [Fintype α] [FinEnum α] [DecidablePred (· ∈ M.accept)] in
@[simp]
theorem mem_preimage {C : Finset σ} {a : α} {q : σ} : q ∈ preimage M C a ↔ M.step q a ∈ C := by
  simp [preimage]

/-- **A set of states split by another.** A set $D$ of states is split by a set $P$ of states
when $D$ contains both a state in $P$ and a state not in $P$, that is, when $D \cap P$ and
$D \setminus P$ are both nonempty. -/
def Splits (pre D : Finset σ) : Prop :=
  (D.filter (· ∈ pre)).Nonempty ∧ (D.filter (· ∉ pre)).Nonempty

instance (pre D : Finset σ) : Decidable (Splits pre D) := by
  unfold Splits
  infer_instance

/-- **Splitting a block by a set.** For sets $P$ and $D$ of states, splitting $D$ by $P$ gives
the two-element list $[D \cap P,\ D \setminus P]$ if both of these sets are nonempty, and the
one-element list $[D]$ otherwise. -/
def splitBlock (pre D : Finset σ) : List (Finset σ) :=
  if Splits pre D then [D.filter (· ∈ pre), D.filter (· ∉ pre)] else [D]

/-- **Smaller of two finite sets of states.** For finite sets $A$ and $B$ of states, the
smaller one is $A$ if $|A| \le |B|$ and $B$ otherwise; on a tie in cardinality it is $A$. -/
def smaller (A B : Finset σ) : Finset σ := if A.card ≤ B.card then A else B

/-- **New splitters for a split block.** Given a waiting list $W$ of pairs of a set of states and a
letter and sets $S$ and $D$ of states, write $D_1 = D \cap S$ and $D_2 = D \setminus S$. The new
waiting entries for $D$ consist, for each letter $b$ in the enumeration order of the alphabet,
of both $(D_1, b)$ and $(D_2, b)$ if $(D, b)$ is in $W$, and otherwise of the single entry
$(E, b)$, where $E$ is the smaller of $D_1$ and $D_2$ by cardinality ($D_1$ on a tie). -/
def newSplitters (W : List (Finset σ × α)) (pre D : Finset σ) : List (Finset σ × α) :=
  (FinEnum.toList α).flatMap fun b =>
    if (D, b) ∈ W then [(D.filter (· ∈ pre), b), (D.filter (· ∉ pre), b)]
    else [(smaller (D.filter (· ∈ pre)) (D.filter (· ∉ pre)), b)]

/-- **One refinement round of the partition.** For a DFA $M$ with transition function $\delta$, a
list $P$ of blocks of states, a set $C$ of states and a letter $a$, let
$S = \{q : \delta(q, a) \in C\}$ be the preimage of $C$ under $a$. The partition after the
splitter $(C, a)$ replaces each block $D$ of $P$, in order, by the two blocks $D \cap S$ and
$D \setminus S$ when both are nonempty, and keeps $D$ otherwise. -/
def roundP (P : List (Finset σ)) (C : Finset σ) (a : α) : List (Finset σ) :=
  P.flatMap (splitBlock (preimage M C a))

/-- **One update of the waiting list.** For a DFA $M$ with transition function $\delta$, a list $P$
of blocks of states, a list $W$ of pairs of a set of states and a letter, a set $C$ of states and a
letter $a$, let $S = \{q : \delta(q, a) \in C\}$ be the preimage of $C$ under $a$, and say that $S$
splits a set $D$ when $D$ meets both $S$ and its complement. The waiting list after the splitter
$(C, a)$, from the rest $W$ of the waiting list, consists of the entries of $W$ whose set is not
split by $S$, followed, for each block $D$ of $P$ split by $S$ in order, by the new splitters for
$D$: for each letter $b$ in the enumeration order of the alphabet, both $(D \cap S, b)$ and
$(D \setminus S, b)$ if $(D, b)$ is in $W$, and otherwise the single entry $(E, b)$, where $E$ is
the smaller of $D \cap S$ and $D \setminus S$ by cardinality ($D \cap S$ on a tie). -/
def roundW (P : List (Finset σ)) (W : List (Finset σ × α)) (C : Finset σ) (a : α) :
    List (Finset σ × α) :=
  W.filter (fun cb => !decide (Splits (preimage M C a) cb.1)) ++
    (P.filter fun D => decide (Splits (preimage M C a) D)).flatMap
      (newSplitters W (preimage M C a))

/-- **Block of accepting states.** For a DFA $M$ with finite state set $Q$, this is the set
$F \subseteq Q$ of accepting states of $M$, as a finite set. -/
def accBlock : Finset σ := Finset.univ.filter (· ∈ M.accept)

/-- **Rejecting states.** For a DFA $M$ with state set $Q$ and set of accepting states $F$, the
rejecting block is the set $Q \setminus F$ of states of $M$ that are not accepting. -/
def rejBlock : Finset σ := Finset.univ.filter (· ∉ M.accept)

/-- **Hopcroft's initial partition.** For a DFA $M$ with finite state set $Q$ and set of accepting
states $F$, the initial partition is the list of blocks $F$, $Q \setminus F$, in this order, with
any empty block removed. -/
def initP : List (Finset σ) := [accBlock M, rejBlock M].filter (·.Nonempty)

/-- **Hopcroft's initial waiting list.** Let $M$ be a DFA with finite state set $Q$, set of
accepting states $F$ and finite alphabet $\Sigma$. If $F$ and $Q \setminus F$ are both nonempty,
the initial waiting list consists of the splitters $(S, b)$ for every letter $b \in \Sigma$, where
$S = F$ if $|F| \le |Q \setminus F|$ and $S = Q \setminus F$ otherwise; if one of $F$ and
$Q \setminus F$ is empty, the initial waiting list is empty. -/
def initW : List (Finset σ × α) :=
  if (accBlock M).Nonempty ∧ (rejBlock M).Nonempty then
    (FinEnum.toList α).map fun b => (smaller (accBlock M) (rejBlock M), b)
  else []

end Hopcroft

open Hopcroft

/-- **Hopcroft's refinement loop.** Let $M$ be a DFA. Given a round budget $k$, a partition $P$
of the states of $M$ (a list of blocks) and a waiting list $W$ of splitters $(C, a)$, each a block
$C$ with a letter $a$, the loop returns the pair $(P, W)$ unchanged if $k = 0$ or $W$ is empty.
Otherwise it removes the first splitter $(C, a)$ from $W$, replaces $P$ by the partition after the
splitter $(C, a)$ and the remaining waiting list by the waiting list after the splitter $(C, a)$,
and continues with budget $k - 1$. -/
def hopcroftLoop : ℕ → List (Finset σ) → List (Finset σ × α) →
    List (Finset σ) × List (Finset σ × α)
  | 0, P, W => (P, W)
  | _ + 1, P, [] => (P, [])
  | k + 1, P, (C, a) :: W => hopcroftLoop k (roundP M P C a) (roundW M P W C a)

/-- **Hopcroft's partition.** Let $M$ be a DFA with finite state set $Q$ over a finite alphabet
$\Sigma$. Hopcroft's partition of $M$ is the partition returned by Hopcroft's loop run from the
initial partition and the initial waiting list with a budget of $|\Sigma| \cdot (|Q| + 1)$
rounds. -/
def hopcroftPartition : List (Finset σ) :=
  (M.hopcroftLoop (Fintype.card α * (Fintype.card σ + 1)) (initP M) (initW M)).1

/-- **Hopcroft's relation.** For a DFA $M$ with finitely many states, Hopcroft's relation is the
set of pairs $(p, q)$ of states of $M$ such that $p$ and $q$ lie in a common block of Hopcroft's
partition. -/
def hopcroftRel : Finset (σ × σ) :=
  Finset.univ.filter fun pq => ∃ D ∈ M.hopcroftPartition, pq.1 ∈ D ∧ pq.2 ∈ D

/-! ## Partitions -/

namespace Hopcroft

variable {M}

/-- **Partitions of the states.** A list $P$ of sets of states is a partition into nonempty
blocks when entries of $P$ at different positions are disjoint, every entry of $P$ is nonempty,
and every state lies in some entry of $P$. -/
structure IsPartition (P : List (Finset σ)) : Prop where
  disjoint : P.Pairwise Disjoint
  nonempty : ∀ D ∈ P, D.Nonempty
  cover : ∀ q, ∃ D ∈ P, q ∈ D

/-- **Lying in a common block.** For a list $P$ of sets of states, two states $p$ and $q$ are
related by $P$ when some block $D$ of $P$ contains both $p$ and $q$. -/
def Rel (P : List (Finset σ)) (p q : σ) : Prop := ∃ D ∈ P, p ∈ D ∧ q ∈ D

omit [Fintype σ] [DecidableEq σ] in
theorem disjoint_of_mem {P : List (Finset σ)} (h : P.Pairwise Disjoint) {D D' : Finset σ}
    (hD : D ∈ P) (hD' : D' ∈ P) (hne : D ≠ D') : Disjoint D D' :=
  h.forall hD hD' hne

omit [Fintype σ] [DecidableEq σ] in
theorem IsPartition.eq_of_mem {P : List (Finset σ)} (hP : IsPartition P) {D D' : Finset σ}
    (hD : D ∈ P) (hD' : D' ∈ P) {q : σ} (hq : q ∈ D) (hq' : q ∈ D') : D = D' := by
  by_contra hne
  exact Finset.disjoint_left.1 (disjoint_of_mem hP.disjoint hD hD' hne) hq hq'

omit [Fintype σ] [DecidableEq σ] in
theorem IsPartition.rel_refl {P : List (Finset σ)} (hP : IsPartition P) (q : σ) : Rel P q q := by
  obtain ⟨D, hD, hq⟩ := hP.cover q
  exact ⟨D, hD, hq, hq⟩

omit [Fintype σ] [DecidableEq σ] in
theorem IsPartition.rel_trans {P : List (Finset σ)} (hP : IsPartition P) {p q r : σ}
    (h₁ : Rel P p q) (h₂ : Rel P q r) : Rel P p r := by
  obtain ⟨D, hD, hp, hq⟩ := h₁
  obtain ⟨D', hD', hq', hr⟩ := h₂
  obtain rfl := hP.eq_of_mem hD hD' hq hq'
  exact ⟨D, hD, hp, hr⟩

omit [Fintype σ] [DecidableEq σ] in
/-- **A block contains both or neither of two related states.** Let $P$ be a list of sets of
states that is a partition into nonempty blocks, let $C$ be an entry of $P$, and let $p$ and $q$
be states lying in a common entry of $P$. Then $p \in C$ if and only if $q \in C$. -/
theorem IsPartition.mem_iff_of_rel {P : List (Finset σ)} (hP : IsPartition P) {C : Finset σ}
    (hC : C ∈ P) {p q : σ} (h : Rel P p q) : p ∈ C ↔ q ∈ C := by
  obtain ⟨D, hD, hp, hq⟩ := h
  constructor
  · intro hpC
    rw [hP.eq_of_mem hC hD hpC hp]
    exact hq
  · intro hqC
    rw [hP.eq_of_mem hC hD hqC hq]
    exact hp

omit [Fintype σ] [DecidableEq σ] in
theorem IsPartition.nodup {P : List (Finset σ)} (hP : IsPartition P) : P.Nodup := by
  unfold List.Nodup
  refine hP.disjoint.imp_of_mem fun {D D'} hD _ hdis h => ?_
  subst h
  obtain ⟨x, hx⟩ := hP.nonempty D hD
  exact Finset.disjoint_left.1 hdis hx hx

omit [DecidableEq σ] in
/-- **A partition has at most as many blocks as there are states.** If a list $P$ of sets of
states is a partition into nonempty blocks, then the length of $P$ is at most the number $|Q|$ of
states. -/
theorem IsPartition.length_le {P : List (Finset σ)} (hP : IsPartition P) :
    P.length ≤ Fintype.card σ := by
  classical
  rw [← List.toFinset_card_of_nodup hP.nodup]
  calc P.toFinset.card ≤ (P.toFinset.biUnion id).card :=
        Finset.card_le_card_biUnion (fun D hD D' hD' hne =>
          disjoint_of_mem hP.disjoint (List.mem_toFinset.1 hD) (List.mem_toFinset.1 hD') hne)
          (fun D hD => hP.nonempty D (List.mem_toFinset.1 hD))
    _ ≤ Fintype.card σ := Finset.card_le_univ _

/-! ## One round -/

omit [Fintype σ] in
theorem subset_of_mem_splitBlock {pre D D' : Finset σ} (h : D' ∈ splitBlock pre D) : D' ⊆ D := by
  unfold splitBlock at h
  split_ifs at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> exact Finset.filter_subset _ _
  · simp only [List.mem_singleton] at h
    exact h ▸ subset_rfl

omit [Fintype σ] in
/-- **Pieces of a split block lie on one side.** Let $S$ and $D$ be sets of states. Every piece of
$D$ split by $S$ (the two sets $D \cap S$ and $D \setminus S$ if $D$ meets both $S$ and its
complement, and $D$ itself otherwise) is contained in $S$ or disjoint from $S$: any two states
$x$ and $y$ of the piece satisfy $x \in S \iff y \in S$. -/
theorem side_of_mem_splitBlock {pre D D' : Finset σ} (h : D' ∈ splitBlock pre D) {x y : σ}
    (hx : x ∈ D') (hy : y ∈ D') : x ∈ pre ↔ y ∈ pre := by
  unfold splitBlock at h
  split_ifs at h with hs
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · simp only [Finset.mem_filter] at hx hy
      exact iff_of_true hx.2 hy.2
    · simp only [Finset.mem_filter] at hx hy
      exact iff_of_false hx.2 hy.2
  · simp only [List.mem_singleton] at h
    subst h
    by_contra hne
    apply hs
    rcases Classical.em (x ∈ pre) with hxp | hxp
    · have hyp : y ∉ pre := fun hyp => hne (iff_of_true hxp hyp)
      exact ⟨⟨x, by simp [hx, hxp]⟩, ⟨y, by simp [hy, hyp]⟩⟩
    · have hyp : y ∈ pre := by
        by_contra hyp
        exact hne (iff_of_false hxp hyp)
      exact ⟨⟨y, by simp [hy, hyp]⟩, ⟨x, by simp [hx, hxp]⟩⟩

omit [Fintype α] [FinEnum α] [DecidablePred (· ∈ M.accept)] in
/-- **Effect of one splitter on the common-block relation.** Let $M$ be a DFA with transition
function $\delta$, $P$ a list of blocks of states, $C$ a set of states and $a$ a letter. Two states
$p$ and $q$ lie in a common block after the splitter $(C, a)$ is applied to $P$ if and only if
they lie in a common block of $P$ and $\delta(p, a) \in C \iff \delta(q, a) \in C$. -/
theorem rel_roundP_iff {P : List (Finset σ)} {C : Finset σ} {a : α} {p q : σ} :
    Rel (roundP M P C a) p q ↔ Rel P p q ∧ (p ∈ preimage M C a ↔ q ∈ preimage M C a) := by
  constructor
  · rintro ⟨D', hD', hp, hq⟩
    obtain ⟨D, hD, hD'D⟩ := List.mem_flatMap.1 hD'
    exact ⟨⟨D, hD, subset_of_mem_splitBlock hD'D hp, subset_of_mem_splitBlock hD'D hq⟩,
      side_of_mem_splitBlock hD'D hp hq⟩
  · rintro ⟨⟨D, hD, hp, hq⟩, hside⟩
    by_cases hs : Splits (preimage M C a) D
    · by_cases hpp : p ∈ preimage M C a
      · exact ⟨D.filter (· ∈ preimage M C a),
          List.mem_flatMap.2 ⟨D, hD, by simp [splitBlock, hs]⟩,
          Finset.mem_filter.2 ⟨hp, hpp⟩, Finset.mem_filter.2 ⟨hq, hside.1 hpp⟩⟩
      · exact ⟨D.filter (· ∉ preimage M C a),
          List.mem_flatMap.2 ⟨D, hD, by simp [splitBlock, hs]⟩,
          Finset.mem_filter.2 ⟨hp, hpp⟩, Finset.mem_filter.2 ⟨hq, fun h => hpp (hside.2 h)⟩⟩
    · exact ⟨D, List.mem_flatMap.2 ⟨D, hD, by simp [splitBlock, hs]⟩, hp, hq⟩

omit [Fintype α] [FinEnum α] [DecidablePred (· ∈ M.accept)] in
theorem IsPartition.roundP {P : List (Finset σ)} (hP : IsPartition P) (C : Finset σ) (a : α) :
    IsPartition (roundP M P C a) where
  disjoint := by
    rw [Hopcroft.roundP, List.pairwise_flatMap]
    refine ⟨fun D _ => ?_, hP.disjoint.imp_of_mem fun {D D'} _ _ hdis x hx y hy =>
      hdis.mono (subset_of_mem_splitBlock hx) (subset_of_mem_splitBlock hy)⟩
    unfold splitBlock
    split_ifs
    · refine List.pairwise_pair.2 (Finset.disjoint_left.2 fun x hx hx' => ?_)
      simp only [Finset.mem_filter] at hx hx'
      exact hx'.2 hx.2
    · simp
  nonempty := by
    intro D' hD'
    obtain ⟨D, hD, hD'D⟩ := List.mem_flatMap.1 hD'
    unfold splitBlock at hD'D
    split_ifs at hD'D with hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hD'D
      rcases hD'D with rfl | rfl
      · exact hs.1
      · exact hs.2
    · simp only [List.mem_singleton] at hD'D
      exact hD'D ▸ hP.nonempty D hD
  cover q := by
    obtain ⟨D', hD', hq, -⟩ := rel_roundP_iff.2 ⟨hP.rel_refl q, Iff.rfl⟩
    exact ⟨D', hD', hq⟩

omit [Fintype α] [FinEnum α] [DecidablePred (· ∈ M.accept)] in
/-- **Number of blocks after one round.** Let $M$ be a DFA with transition function $\delta$, let
$P$ be a list of sets of states, $C$ a set of states and $a$ a letter, and let
$\mathrm{pre} = \{q : \delta(q, a) \in C\}$. The partition after the splitter $(C, a)$, which
replaces each entry $D$ of $P$ meeting both $\mathrm{pre}$ and its complement by
$D \cap \mathrm{pre}$ and $D \setminus \mathrm{pre}$, has length equal to the length of $P$ plus
the number of entries of $P$ (counted with repetition) that meet both $\mathrm{pre}$ and its
complement. -/
theorem length_roundP {P : List (Finset σ)} {C : Finset σ} {a : α} :
    (roundP M P C a).length =
      P.length + (P.filter fun D => decide (Splits (preimage M C a) D)).length := by
  unfold Hopcroft.roundP
  induction P with
  | nil => simp
  | cons D P ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.filter_cons]
    unfold splitBlock
    by_cases h : Splits (preimage M C a) D <;> simp [h] <;> omega

omit [Fintype α] [FinEnum α] [DecidableEq σ] [Fintype σ] in
theorem length_flatMap_ite {β : Type*} (L : List α) (r : α → Prop) [DecidablePred r]
    (f g h : α → β) :
    (L.flatMap fun b => if r b then [f b, g b] else [h b]).length =
      L.length + (L.filter fun b => decide (r b)).length := by
  induction L with
  | nil => simp
  | cons b L ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.filter_cons]
    by_cases hb : r b <;> simp [hb] <;> omega

theorem length_toList : (FinEnum.toList α).length = Fintype.card α := by
  classical
  rw [← List.toFinset_card_of_nodup FinEnum.nodup_toList, ← Finset.card_univ]
  congr 1
  ext b
  simp [FinEnum.mem_toList]

omit [DecidablePred (· ∈ M.accept)] in
/-- **Growth of the waiting list in one round.** Let $M$ be a DFA with transition function
$\delta$ over a finite alphabet $\Sigma$, let $P$ be a list of sets of states with no repeated
entries, let $W$ be a list of pairs of a set of states and a letter, let $C$ be a set of states
and $a$ a letter, and let $S = \{q : \delta(q, a) \in C\}$ be the preimage of $C$ under $a$. Then
the waiting list after the splitter $(C, a)$, computed from the blocks $P$ and the rest $W$ of the
waiting list, has length at most $|W| + |\Sigma| \cdot k$, where $k$ is the number of entries of
$P$ split by $S$, that is, meeting both $S$ and its complement. -/
theorem length_roundW_le {P : List (Finset σ)} (hnd : P.Nodup) {W : List (Finset σ × α)}
    {C : Finset σ} {a : α} :
    (roundW M P W C a).length ≤
      W.length +
        Fintype.card α * (P.filter fun D => decide (Splits (preimage M C a) D)).length := by
  set pre := preimage M C a with hpre
  set SP := P.filter fun D => decide (Splits pre D) with hSP
  set L := FinEnum.toList α with hL
  set X := SP.flatMap fun D => (L.filter fun b => decide ((D, b) ∈ W)).map (D, ·) with hX
  have hnew : (SP.flatMap (newSplitters W pre)).length = SP.length * L.length + X.length := by
    rw [hX]
    clear_value pre
    induction SP with
    | nil => simp
    | cons D SP ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_map, ih]
      rw [newSplitters, ← hL, length_flatMap_ite]
      rw [Nat.succ_mul]
      linarith
  have hXnd : X.Nodup := by
    rw [hX, List.nodup_flatMap]
    refine ⟨fun D _ => ((FinEnum.nodup_toList).filter _).map (Prod.mk_right_injective D), ?_⟩
    refine (hnd.filter _).imp fun {D D'} hne => ?_
    simp only [List.disjoint_left, List.mem_map, List.mem_filter]
    rintro x ⟨b, -, rfl⟩ ⟨b', -, h⟩
    exact hne (Prod.mk.inj h).1.symm
  have hXsub : X ⊆ W.filter fun cb => decide (Splits pre cb.1) := by
    intro x hx
    rw [hX, List.mem_flatMap] at hx
    obtain ⟨D, hD, hx⟩ := hx
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hx
    obtain ⟨b, ⟨-, hb⟩, rfl⟩ := hx
    rw [hSP, List.mem_filter, decide_eq_true_eq] at hD
    exact List.mem_filter.2 ⟨hb, by simpa using hD.2⟩
  have hXle := (hXnd.subperm hXsub).length_le
  have hsplit := List.length_eq_length_filter_add (l := W) fun cb => decide (Splits pre cb.1)
  have hlen : L.length = Fintype.card α := length_toList
  rw [roundW, ← hpre, List.length_append, hnew, hlen]
  rw [hlen] at hnew
  linarith

/-! ## The invariants -/

omit [Fintype α] [FinEnum α] [Fintype σ] [DecidableEq σ] [DecidablePred (· ∈ M.accept)] in
theorem acceptsFrom_step_eq {p q : σ} (h : M.acceptsFrom p = M.acceptsFrom q) (a : α) :
    M.acceptsFrom (M.step p a) = M.acceptsFrom (M.step q a) := by
  ext w
  have h' : a :: w ∈ M.acceptsFrom p ↔ a :: w ∈ M.acceptsFrom q := by rw [h]
  rwa [mem_acceptsFrom, mem_acceptsFrom, evalFrom_cons, evalFrom_cons, ← mem_acceptsFrom,
    ← mem_acceptsFrom] at h'

variable (M) in
/-- **Invariants of Hopcroft's loop.** Let $M$ be a DFA with transition function $\delta$. A list
$P$ of sets of states and a waiting list $W$ of pairs $(C, b)$ of a set of states $C$ and a letter
$b$ satisfy the invariants when: (i) $P$ is a partition of the states into nonempty blocks;
(ii) for every $(C, b)$ in $W$, $C$ is an entry of $P$; (iii) for every letter $b$ and all states
$p$, $q$ lying in a common entry of $P$, if for every $C$ with $(C, b)$ in $W$ the states
$\delta(p, b)$ and $\delta(q, b)$ are both in $C$ or both outside $C$, then $\delta(p, b)$ and
$\delta(q, b)$ lie in a common entry of $P$; (iv) any two states lying in a common entry of $P$
are both accepting or both rejecting; and (v) any two states from which $M$ accepts the same
language lie in a common entry of $P$. -/
structure Inv (P : List (Finset σ)) (W : List (Finset σ × α)) : Prop where
  /-- `P` is a partition into nonempty blocks. -/
  part : IsPartition P
  /-- Every waiting set is a block. -/
  mem : ∀ cb ∈ W, cb.1 ∈ P
  /-- Two states in one block whose `b`-successors agree on every set waiting with `b` have
  `b`-successors in one block. -/
  stable : ∀ b p q, Rel P p q → (∀ C, (C, b) ∈ W → (M.step p b ∈ C ↔ M.step q b ∈ C)) →
    Rel P (M.step p b) (M.step q b)
  /-- Blocks agree on acceptance. -/
  accept : ∀ p q, Rel P p q → (p ∈ M.accept ↔ q ∈ M.accept)
  /-- States with one continuation language share a block. -/
  coarse : ∀ p q, M.acceptsFrom p = M.acceptsFrom q → Rel P p q

omit [Fintype α] [DecidablePred (· ∈ M.accept)] in
/-- **One round preserves the invariants.** Let $M$ be a DFA, $P$ a list of blocks of states, $W$
a list of pairs of a set of states and a letter, $C$ a set of states and $a$ a letter. If $P$ and
the waiting list obtained by putting $(C, a)$ in front of $W$ satisfy the invariants of
Hopcroft's loop, then so do the partition after the splitter $(C, a)$ and the waiting list after
the splitter $(C, a)$ from the rest $W$. -/
theorem Inv.round {P : List (Finset σ)} {C : Finset σ} {a : α} {W : List (Finset σ × α)}
    (h : Inv M P ((C, a) :: W)) : Inv M (roundP M P C a) (roundW M P W C a) where
  part := h.part.roundP C a
  mem := by
    intro cb hcb
    rw [roundW, List.mem_append] at hcb
    rcases hcb with hcb | hcb
    · obtain ⟨hcbW, hns⟩ := List.mem_filter.1 hcb
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hns
      exact List.mem_flatMap.2 ⟨cb.1, h.mem cb (List.mem_cons_of_mem _ hcbW),
        by simp [splitBlock, hns]⟩
    · obtain ⟨D, hD, hcb⟩ := List.mem_flatMap.1 hcb
      obtain ⟨hDP, hDs⟩ := List.mem_filter.1 hD
      rw [decide_eq_true_eq] at hDs
      refine List.mem_flatMap.2 ⟨D, hDP, ?_⟩
      simp only [splitBlock, hDs, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false]
      rw [newSplitters, List.mem_flatMap] at hcb
      obtain ⟨b, -, hcb⟩ := hcb
      split_ifs at hcb
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcb
        rcases hcb with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · simp only [List.mem_singleton] at hcb
        subst hcb
        unfold smaller
        split_ifs
        · exact Or.inl rfl
        · exact Or.inr rfl
  stable := by
    intro b p q hpq hagree
    rw [rel_roundP_iff] at hpq ⊢
    obtain ⟨hpqP, hside⟩ := hpq
    set pre := preimage M C a with hpre
    -- a split block is replaced by its halves when waiting, by its smaller half otherwise
    have hnew : ∀ D ∈ P, Splits pre D → ∀ X, (X = D.filter (· ∈ pre) ∨ X = D.filter (· ∉ pre)) →
        ((D, b) ∈ W ∨ X = smaller (D.filter (· ∈ pre)) (D.filter (· ∉ pre))) →
        (X, b) ∈ roundW M P W C a := by
      intro D hD hs X hX hwait
      rw [roundW, List.mem_append]
      refine Or.inr (List.mem_flatMap.2 ⟨D, List.mem_filter.2 ⟨hD, by simpa using hs⟩, ?_⟩)
      rw [newSplitters, List.mem_flatMap]
      refine ⟨b, FinEnum.mem_toList b, ?_⟩
      split_ifs with hDb
      · rcases hX with rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
      · rcases hwait with hwait | rfl
        · exact absurd hwait hDb
        · exact List.mem_singleton_self _
    have hrs : Rel P (M.step p b) (M.step q b) := by
      refine h.stable b p q hpqP fun C' hC' => ?_
      rcases List.mem_cons.1 hC' with hC' | hC'
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hC'
        simpa [hpre] using hside
      · have hC'P : C' ∈ P := h.mem (C', b) (List.mem_cons_of_mem _ hC')
        by_cases hs : Splits pre C'
        · have h₁ := hagree _ (hnew C' hC'P hs _ (Or.inl rfl) (Or.inl hC'))
          have h₂ := hagree _ (hnew C' hC'P hs _ (Or.inr rfl) (Or.inl hC'))
          simp only [Finset.mem_filter] at h₁ h₂
          constructor
          · intro hp
            by_cases hpp : M.step p b ∈ pre
            · exact (h₁.1 ⟨hp, hpp⟩).1
            · exact (h₂.1 ⟨hp, hpp⟩).1
          · intro hq
            by_cases hqp : M.step q b ∈ pre
            · exact (h₁.2 ⟨hq, hqp⟩).1
            · exact (h₂.2 ⟨hq, hqp⟩).1
        · refine hagree C' ?_
          rw [roundW, List.mem_append]
          exact Or.inl (List.mem_filter.2 ⟨hC', by simpa using hs⟩)
    refine ⟨hrs, ?_⟩
    obtain ⟨D, hD, hrD, hsD⟩ := hrs
    by_cases hs : Splits pre D
    · -- the halves are separated by a waiting entry
      have hX : ∃ X, (X = D.filter (· ∈ pre) ∨ X = D.filter (· ∉ pre)) ∧
          (X, b) ∈ roundW M P W C a := by
        by_cases hDb : (D, b) ∈ W
        · exact ⟨_, Or.inl rfl, hnew D hD hs _ (Or.inl rfl) (Or.inl hDb)⟩
        · refine ⟨smaller (D.filter (· ∈ pre)) (D.filter (· ∉ pre)), ?_,
            hnew D hD hs _ ?_ (Or.inr rfl)⟩ <;>
          · unfold smaller
            split_ifs
            · exact Or.inl rfl
            · exact Or.inr rfl
      obtain ⟨X, hXeq, hXw⟩ := hX
      have hag := hagree X hXw
      rcases hXeq with rfl | rfl
      · simpa [hrD, hsD] using hag
      · exact not_iff_not.1 (by simpa [hrD, hsD] using hag)
    · -- an unsplit block lies on one side
      by_contra hne
      apply hs
      rcases Classical.em (M.step p b ∈ pre) with hr | hr
      · have hs' : M.step q b ∉ pre := fun h' => hne (iff_of_true hr h')
        exact ⟨⟨_, Finset.mem_filter.2 ⟨hrD, hr⟩⟩, ⟨_, Finset.mem_filter.2 ⟨hsD, hs'⟩⟩⟩
      · have hs' : M.step q b ∈ pre := by
          by_contra h'
          exact hne (iff_of_false hr h')
        exact ⟨⟨_, Finset.mem_filter.2 ⟨hsD, hs'⟩⟩, ⟨_, Finset.mem_filter.2 ⟨hrD, hr⟩⟩⟩
  accept p q hpq := h.accept p q (rel_roundP_iff.1 hpq).1
  coarse p q hpq := by
    refine rel_roundP_iff.2 ⟨h.coarse p q hpq, ?_⟩
    simp only [mem_preimage]
    exact h.part.mem_iff_of_rel (h.mem (C, a) List.mem_cons_self)
      (h.coarse _ _ (acceptsFrom_step_eq hpq a))

omit [Fintype α] [FinEnum α] [Fintype σ] [DecidableEq σ] [DecidablePred (· ∈ M.accept)] in
/-- **With an empty waiting list, blocks are the classes of equal continuation languages.** Let
$M$ be a DFA and $P$ a list of blocks of states such that $P$ with the empty waiting list
satisfies the invariants of Hopcroft's loop. Then two states $p$ and $q$ lie in a common block of
$P$ if and only if they accept the same continuation languages, that is, $M$ accepts a word from
$p$ exactly when it accepts it from $q$.

With an empty waiting list the invariants say that $P$ is a right congruence refining acceptance. -/
theorem Inv.rel_iff {P : List (Finset σ)} (h : Inv M P []) {p q : σ} :
    Rel P p q ↔ M.acceptsFrom p = M.acceptsFrom q := by
  constructor
  · intro hpq
    ext w
    induction w generalizing p q with
    | nil =>
      rw [mem_acceptsFrom, mem_acceptsFrom, evalFrom_nil, evalFrom_nil]
      exact h.accept p q hpq
    | cons a w ih =>
      rw [mem_acceptsFrom, mem_acceptsFrom, evalFrom_cons, evalFrom_cons, ← mem_acceptsFrom,
        ← mem_acceptsFrom]
      exact ih (h.stable a p q hpq (by simp))
  · exact h.coarse p q

omit [Fintype α] [FinEnum α] [DecidableEq σ] in
theorem rel_initP_iff {x y : σ} : Rel (initP M) x y ↔ (x ∈ M.accept ↔ y ∈ M.accept) := by
  constructor
  · rintro ⟨D, hD, hx, hy⟩
    simp only [initP, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD.1 with rfl | rfl
    · simp only [accBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      exact iff_of_true hx hy
    · simp only [rejBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      exact iff_of_false hx hy
  · intro hxy
    by_cases hx : x ∈ M.accept
    · refine ⟨accBlock M, List.mem_filter.2 ⟨by simp, ?_⟩, by simp [accBlock, hx],
        by simp [accBlock, hxy.1 hx]⟩
      rw [decide_eq_true_eq]
      exact ⟨x, by simp [accBlock, hx]⟩
    · refine ⟨rejBlock M, List.mem_filter.2 ⟨by simp, ?_⟩, by simp [rejBlock, hx],
        by simp only [rejBlock, Finset.mem_filter, Finset.mem_univ, true_and]
           exact fun h' => hx (hxy.2 h')⟩
      rw [decide_eq_true_eq]
      exact ⟨x, by simp [rejBlock, hx]⟩

omit [Fintype α] [DecidableEq σ] in
variable (M) in
/-- **The invariants hold initially.** For every DFA $M$ with finitely many states over a finite
alphabet, Hopcroft's initial partition and initial waiting list satisfy the invariants of
Hopcroft's loop. -/
theorem inv_init : Inv M (initP M) (initW M) where
  part :=
    { disjoint := by
        refine (List.pairwise_pair.2 (Finset.disjoint_left.2 fun x hx hx' => ?_)).filter _
        simp only [accBlock, rejBlock, Finset.mem_filter] at hx hx'
        exact hx'.2 hx.2
      nonempty := fun D hD => by
        simp only [initP, List.mem_filter, decide_eq_true_eq] at hD
        exact hD.2
      cover := fun q => by
        obtain ⟨D, hD, hq, -⟩ := rel_initP_iff.2 (Iff.rfl : q ∈ M.accept ↔ q ∈ M.accept)
        exact ⟨D, hD, hq⟩ }
  mem := by
    intro cb hcb
    unfold initW at hcb
    split_ifs at hcb with hne
    · simp only [List.mem_map] at hcb
      obtain ⟨b, -, rfl⟩ := hcb
      simp only [initP, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false,
        decide_eq_true_eq]
      unfold smaller
      split_ifs
      · exact ⟨Or.inl rfl, hne.1⟩
      · exact ⟨Or.inr rfl, hne.2⟩
    · simp at hcb
  stable := by
    intro b p q _ hagree
    rw [rel_initP_iff]
    unfold initW at hagree
    split_ifs at hagree with hne
    · have hS := hagree (smaller (accBlock M) (rejBlock M)) (by simp [FinEnum.mem_toList])
      unfold smaller at hS
      split_ifs at hS
      · simpa [accBlock] using hS
      · simp only [rejBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hS
        exact not_iff_not.1 hS
    · -- one block is empty: all states agree on acceptance
      simp only [not_and_or, Finset.not_nonempty_iff_eq_empty] at hne
      rcases hne with hne | hne
      · have h₁ : M.step p b ∉ M.accept := fun h' => by
          simpa [hne] using (show M.step p b ∈ accBlock M by simp [accBlock, h'])
        have h₂ : M.step q b ∉ M.accept := fun h' => by
          simpa [hne] using (show M.step q b ∈ accBlock M by simp [accBlock, h'])
        exact iff_of_false h₁ h₂
      · have h₁ : M.step p b ∈ M.accept := by
          by_contra h'
          simpa [hne] using (show M.step p b ∈ rejBlock M by simp [rejBlock, h'])
        have h₂ : M.step q b ∈ M.accept := by
          by_contra h'
          simpa [hne] using (show M.step q b ∈ rejBlock M by simp [rejBlock, h'])
        exact iff_of_true h₁ h₂
  accept p q hpq := rel_initP_iff.1 hpq
  coarse p q hpq := by
    rw [rel_initP_iff]
    have h' : [] ∈ M.acceptsFrom p ↔ [] ∈ M.acceptsFrom q := by rw [hpq]
    rwa [mem_acceptsFrom, mem_acceptsFrom, evalFrom_nil, evalFrom_nil] at h'

end Hopcroft

open Hopcroft

omit [DecidablePred (· ∈ M.accept)] in
/-- **Termination of Hopcroft's loop.** Let $M$ be a DFA with finite state set $Q$ over a finite
alphabet $\Sigma$, let $P$ be a partition of the states given as a list of blocks, let $W$ be a
waiting list of splitters, and let $k$ be a natural number. If $P$ and $W$ satisfy the invariants
of Hopcroft's loop and $|W| + |\Sigma| \cdot (|Q| - |P|) \le k$, where $|P|$ and $|W|$ are the
lengths of the lists, then Hopcroft's loop run from $(P, W)$ with a budget of $k$ rounds ends with
an empty waiting list, and the partition and waiting list it returns again satisfy the invariants.

The invariants make $P$ a partition into nonempty blocks, so $|P| \le |Q|$ and the difference
$|Q| - |P|$ is not truncated. -/
theorem hopcroftLoop_spec : ∀ (k : ℕ) (P : List (Finset σ)) (W : List (Finset σ × α)),
    Inv M P W → W.length + Fintype.card α * (Fintype.card σ - P.length) ≤ k →
    (M.hopcroftLoop k P W).2 = [] ∧ Inv M (M.hopcroftLoop k P W).1 (M.hopcroftLoop k P W).2
  | 0, P, W, hI, hk => by
    have hW : W = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hW
    exact ⟨rfl, hI⟩
  | k + 1, P, [], hI, _ => ⟨rfl, hI⟩
  | k + 1, P, (C, a) :: W, hI, hk => by
    have hI' := hI.round
    refine hopcroftLoop_spec k _ _ hI' ?_
    have hlenP := length_roundP (M := M) (P := P) (C := C) (a := a)
    have hlenW := length_roundW_le (M := M) hI.part.nodup (W := W) (C := C) (a := a)
    have hle := hI'.part.length_le
    rw [hlenP] at hle ⊢
    simp only [List.length_cons] at hk
    set s := (P.filter fun D => decide (Splits (preimage M C a) D)).length
    have e : Fintype.card α * (Fintype.card σ - (P.length + s)) + Fintype.card α * s =
        Fintype.card α * (Fintype.card σ - P.length) := by
      rw [← Nat.mul_add]
      congr 1
      omega
    linarith

/-- **Hopcroft's waiting list is exhausted.** Let $M$ be a DFA with finite state set $Q$ over a
finite alphabet $\Sigma$. Hopcroft's loop, run from the initial partition and the initial waiting
list with a budget of $|\Sigma| \cdot (|Q| + 1)$ rounds, ends with an empty waiting list. -/
theorem hopcroftLoop_waiting_eq_nil :
    (M.hopcroftLoop (Fintype.card α * (Fintype.card σ + 1)) (initP M) (initW M)).2 = [] := by
  refine (hopcroftLoop_spec M _ _ _ (inv_init M) ?_).1
  have hW : (initW M).length ≤ Fintype.card α := by
    unfold initW
    split_ifs
    · simp [length_toList]
    · simp
  have h₂ : Fintype.card α * (Fintype.card σ - (initP M).length) ≤
      Fintype.card α * Fintype.card σ := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  rw [Nat.mul_succ]
  omega

theorem inv_hopcroftPartition : Inv M M.hopcroftPartition [] := by
  have h := hopcroftLoop_spec M (Fintype.card α * (Fintype.card σ + 1)) (initP M) (initW M)
    (inv_init M) (by
      have hW : (initW M).length ≤ Fintype.card α := by
        unfold initW
        split_ifs
        · simp [length_toList]
        · simp
      have h₂ : Fintype.card α * (Fintype.card σ - (initP M).length) ≤
          Fintype.card α * Fintype.card σ := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      rw [Nat.mul_succ]
      omega)
  rw [h.1] at h
  exact h.2

/-- **Hopcroft's final partition is a partition.** For a DFA $M$, Hopcroft's final partition of
$M$ is a partition of the states of $M$ into nonempty blocks. -/
theorem isPartition_hopcroftPartition : IsPartition M.hopcroftPartition :=
  (inv_hopcroftPartition M).part

/-- **Correctness of Hopcroft's algorithm.** For a DFA $M$, two states $p$ and $q$ share a block
of Hopcroft's final partition of $M$ exactly when the language accepted by $M$ from $p$ equals the
language accepted by $M$ from $q$. -/
theorem mem_hopcroftRel_iff {p q : σ} :
    (p, q) ∈ M.hopcroftRel ↔ M.acceptsFrom p = M.acceptsFrom q := by
  rw [← (inv_hopcroftPartition M).rel_iff]
  simp [hopcroftRel, Hopcroft.Rel]

/-- **Hopcroft's partition is Moore's relation.** For every DFA $M$ with finitely many states over
a finite alphabet, Hopcroft's relation of $M$, the set of pairs of states lying in a common block
of Hopcroft's partition, equals Moore's state equivalence of $M$ as a set of pairs of states. -/
theorem hopcroftRel_eq_mooreRel : M.hopcroftRel = M.mooreRel := by
  ext ⟨p, q⟩
  rw [mem_hopcroftRel_iff, mem_mooreRel_iff]

/-- **Moore classes are Hopcroft blocks.** For a DFA $M$ and reachable states $p$ and $q$ of $M$,
the classes of $p$ and $q$ under Moore's equivalence on reachable states (the states of Moore's
minimal automaton) are equal if and only if $p$ and $q$ share a block of Hopcroft's final
partition of $M$. -/
theorem mooreClass_eq_iff_mem_hopcroftRel {p q : {s // s ∈ M.reachable}} :
    M.mooreClass p = M.mooreClass q ↔ (p.1, q.1) ∈ M.hopcroftRel := by
  rw [mooreClass_eq_iff, mem_hopcroftRel_iff]

/-- **Blocks of Hopcroft's partition are language classes.** Let $M$ be a DFA, $D$ a block of
Hopcroft's final partition of $M$ and $p$ a state in $D$. Then a state $q$ lies in $D$ if and only
if the language accepted by $M$ from $q$ equals the language accepted by $M$ from $p$. -/
theorem mem_block_iff {D : Finset σ} (hD : D ∈ M.hopcroftPartition) {p : σ} (hp : p ∈ D)
    {q : σ} : q ∈ D ↔ M.acceptsFrom q = M.acceptsFrom p := by
  rw [← (inv_hopcroftPartition M).rel_iff]
  constructor
  · intro hq
    exact ⟨D, hD, hq, hp⟩
  · intro h
    exact ((isPartition_hopcroftPartition M).mem_iff_of_rel hD h).2 hp

end DFA
