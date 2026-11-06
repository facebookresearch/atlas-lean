/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Combinatorics.Matroid.Rank.ENat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.List.TakeWhile

/-!
# The greedy algorithm on a matroid

`GREEDY(M, w)` from CLRS, third edition, Section 16.4: scan the elements in nonincreasing order
of weight and keep an element whenever adding it to the kept set leaves it independent.
CLRS Theorem 16.11 (Edmonds; Rado): for a weighted matroid with nonnegative weights the result is
an optimal subset, an independent set of maximum weight.

The matroid is Mathlib's `Matroid α`. The algorithm reaches it only through an independence
oracle `indep : Finset α → Bool` that agrees with `M.Indep` (`hind`). The input `es` lists the
elements in nonincreasing weight order (CLRS sorts first; any sort can produce the order), and
weights are natural numbers.

* `matroidGreedy_indep`: the result is independent and drawn from `es`.
* `matroidGreedy_optimal`: every independent set drawn from `es` weighs at most the result.
* `matroidGreedy_isBase`: if `es` lists exactly the ground set, the result is a base, so it is a
  maximum-weight base.

The optimality proof is the layer-cake argument rather than CLRS's exchange argument: the weight
of a set is `∑_t |{x : w x > t}|`, the greedy state after the elements heavier than `t` is a
maximal independent subset of them, and augmentation (`Matroid.Indep.exists_insert_of_encard_lt`)
shows that no independent set has more elements heavier than `t`.

## Cost model

One unit per element scanned: one oracle query on the kept set plus the element. Building the
kept set is free; the oracle's own cost is not modeled. A list of `n` elements costs exactly `n`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

universe u

variable {α : Type u} [DecidableEq α]

/-- **Greedy scan with an independence oracle.** Given an oracle $O$ that accepts or rejects each
finite subset of a type $\alpha$, a finite set $S \subseteq \alpha$ and a list $e_1, \dots, e_n$ of
elements of $\alpha$, the greedy scan processes $e_1, \dots, e_n$ in order, starting with $S$ as
the current set: it replaces the current set $T$ by $T \cup \{e_i\}$ if $O$ accepts
$T \cup \{e_i\}$, and leaves it unchanged otherwise. It returns the final current set and charges
one unit of time per element processed. -/
def matroidGreedyScan (indep : Finset α → Bool) (S : Finset α) : List α → TimeM ℕ (Finset α)
  | [] => pure S
  | e :: es => do
      ✓
      if indep (insert e S) then matroidGreedyScan indep (insert e S) es
      else matroidGreedyScan indep S es

/-- **Greedy algorithm on a matroid.** Given an oracle $O$ that accepts or rejects each finite
subset of a type $\alpha$ and a list $L$ of elements of $\alpha$, the greedy algorithm starts from
the empty set, processes the elements of $L$ in order, adds an element $e$ to the current set $T$
when $O$ accepts $T \cup \{e\}$ and leaves $T$ unchanged otherwise, and returns the final set. It
charges one unit of time per element processed.

Source: CLRS, third edition, Section 16.4, procedure GREEDY, without its sorting step. -/
def matroidGreedy (indep : Finset α → Bool) (es : List α) : TimeM ℕ (Finset α) :=
  matroidGreedyScan indep ∅ es

/-! ## Cost -/

/-- **Running time of the greedy scan.** For every oracle $O$ on finite subsets of a type
$\alpha$, every finite set $S \subseteq \alpha$ and every list $L$ of elements of $\alpha$, the
greedy scan with oracle $O$ from $S$ over $L$ takes time exactly the length of $L$. -/
@[simp]
theorem matroidGreedyScan_time (indep : Finset α → Bool) (S : Finset α) (es : List α) :
    (matroidGreedyScan indep S es).time = es.length := by
  induction es generalizing S with
  | nil => simp [matroidGreedyScan]
  | cons e es ih =>
      by_cases h : indep (insert e S) <;> simp [matroidGreedyScan, h, ih, Nat.add_comm]

/-- **Running time of the matroid greedy algorithm.** For every oracle $O$ on finite subsets of a
type $\alpha$ and every list $L$ of elements of $\alpha$, the greedy algorithm with oracle $O$ on
$L$ takes time exactly the length of $L$, one oracle query per element. -/
@[simp]
theorem matroidGreedy_time (indep : Finset α → Bool) (es : List α) :
    (matroidGreedy indep es).time = es.length :=
  matroidGreedyScan_time indep ∅ es

/-! ## The scan invariant -/

/-- **The greedy scan over a concatenation.** For every oracle $O$ on finite subsets of a type
$\alpha$, every finite set $S \subseteq \alpha$ and all lists $P$ and $Q$ of elements of $\alpha$,
the set returned by the greedy scan with oracle $O$ from $S$ over $P$ followed by $Q$ equals the
set returned by the greedy scan with oracle $O$ over $Q$ starting from the set that the scan with
oracle $O$ from $S$ over $P$ returns. -/
theorem matroidGreedyScan_append (indep : Finset α → Bool) (S : Finset α) (P Q : List α) :
    (matroidGreedyScan indep S (P ++ Q)).ret =
      (matroidGreedyScan indep (matroidGreedyScan indep S P).ret Q).ret := by
  induction P generalizing S with
  | nil => simp [matroidGreedyScan]
  | cons e P ih =>
      by_cases h : indep (insert e S) <;> simp [matroidGreedyScan, h, ih]

theorem subset_matroidGreedyScan (indep : Finset α → Bool) (S : Finset α) (es : List α) :
    S ⊆ (matroidGreedyScan indep S es).ret := by
  induction es generalizing S with
  | nil => simp [matroidGreedyScan]
  | cons e es ih =>
      by_cases h : indep (insert e S)
      · simpa [matroidGreedyScan, h] using (Finset.subset_insert e S).trans (ih _)
      · simpa [matroidGreedyScan, h] using ih S

theorem mem_matroidGreedyScan (indep : Finset α → Bool) (S : Finset α) (es : List α) {x : α}
    (hx : x ∈ (matroidGreedyScan indep S es).ret) : x ∈ S ∨ x ∈ es := by
  induction es generalizing S with
  | nil => simpa [matroidGreedyScan] using hx
  | cons e es ih =>
      by_cases h : indep (insert e S)
      · simp only [matroidGreedyScan, h, ite_true, ret_bind] at hx
        rcases ih _ hx with hx | hx
        · rcases Finset.mem_insert.1 hx with rfl | hx
          · exact Or.inr List.mem_cons_self
          · exact Or.inl hx
        · exact Or.inr (List.mem_cons_of_mem _ hx)
      · simp only [matroidGreedyScan, h, ret_bind] at hx
        rcases ih _ hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (List.mem_cons_of_mem _ hx)

variable {M : Matroid α} {indep : Finset α → Bool}

/-- **Invariant of the greedy scan.** Let $M$ be a matroid on a type $\alpha$, let $O$ be an oracle
that accepts a finite set $A \subseteq \alpha$ exactly when $A$ is independent in $M$, let $S$ be a
finite independent set of $M$ and $L$ a list of elements of $\alpha$, and let $T$ be the set
returned by the greedy scan with oracle $O$ from $S$ over $L$. Then $T$ is independent in $M$, and
for every element $e$ of $L$ with $e \notin T$, the set $T \cup \{e\}$ is not independent in $M$. -/
theorem matroidGreedyScan_spec (hind : ∀ S, indep S = true ↔ M.Indep ↑S) {S : Finset α}
    (hS : M.Indep ↑S) (es : List α) :
    M.Indep ↑(matroidGreedyScan indep S es).ret ∧
      ∀ e ∈ es, e ∉ (matroidGreedyScan indep S es).ret →
        ¬ M.Indep (insert e ↑(matroidGreedyScan indep S es).ret) := by
  induction es generalizing S with
  | nil => simpa [matroidGreedyScan] using hS
  | cons e es ih =>
      by_cases h : indep (insert e S)
      · have hS' : M.Indep ↑(insert e S) := (hind _).1 h
        obtain ⟨hI, hmax⟩ := ih hS'
        simp only [matroidGreedyScan, h, ite_true, ret_bind]
        refine ⟨hI, fun e' he' hnot => ?_⟩
        rcases List.mem_cons.1 he' with rfl | he'
        · exact absurd (subset_matroidGreedyScan indep _ es (Finset.mem_insert_self _ _)) hnot
        · exact hmax e' he' hnot
      · obtain ⟨hI, hmax⟩ := ih hS
        simp only [matroidGreedyScan, h, ret_bind]
        refine ⟨hI, fun e' he' hnot => ?_⟩
        rcases List.mem_cons.1 he' with rfl | he'
        · intro hdep
          have hsub : insert e' (S : Set α) ⊆ insert e' ↑(matroidGreedyScan indep S es).ret :=
            Set.insert_subset_insert (subset_matroidGreedyScan indep S es)
          have := (hind (insert e' S)).2 (by simpa using hdep.subset hsub)
          simp [this] at h
        · exact hmax e' he' hnot

/-- **The matroid greedy result is independent.** Let $M$ be a matroid on a type $\alpha$ and let
$O$ be an oracle that accepts a finite set $A \subseteq \alpha$ exactly when $A$ is independent in
$M$. For every list $L$ of elements of $\alpha$, the set returned by the greedy algorithm with
oracle $O$ on $L$ is independent in $M$, and each of its elements occurs in $L$. -/
theorem matroidGreedy_indep (hind : ∀ S, indep S = true ↔ M.Indep ↑S) (es : List α) :
    M.Indep ↑(matroidGreedy indep es).ret ∧ ∀ x ∈ (matroidGreedy indep es).ret, x ∈ es := by
  refine ⟨(matroidGreedyScan_spec hind (by simp) es).1, fun x hx => ?_⟩
  simpa using mem_matroidGreedyScan indep ∅ es hx

/-- **The matroid greedy result is a base.** Let $M$ be a matroid on a type $\alpha$ with ground set
$E$, and let $O$ be an oracle that accepts a finite set $A \subseteq \alpha$ exactly when $A$ is
independent in $M$. For every list $L$ in which an element of $\alpha$ occurs if and only if it lies
in $E$, the set returned by the greedy algorithm with oracle $O$ on $L$ is a base of $M$. -/
theorem matroidGreedy_isBase (hind : ∀ S, indep S = true ↔ M.Indep ↑S) (es : List α)
    (hground : ∀ x, x ∈ M.E ↔ x ∈ es) : M.IsBase ↑(matroidGreedy indep es).ret := by
  obtain ⟨hI, hmax⟩ := matroidGreedyScan_spec hind (S := ∅) (by simp) es
  exact hI.isBase_of_forall_insert fun e he => hmax e ((hground e).1 he.1) he.2

/-! ## Optimality -/

omit [DecidableEq α] in
/-- Layer cake: a weight sum counts, for each threshold `t < W`, the elements heavier than `t`. -/
private theorem sum_eq_sum_card_filter (w : α → ℕ) (S : Finset α) {W : ℕ} (hW : ∀ x ∈ S, w x ≤ W) :
    ∑ x ∈ S, w x = ∑ t ∈ Finset.range W, (S.filter fun x => t < w x).card := by
  have h : ∀ x ∈ S, w x = ∑ t ∈ Finset.range W, if t < w x then 1 else 0 := by
    intro x hx
    rw [← Finset.card_filter]
    have : (Finset.range W).filter (fun t => t < w x) = Finset.range (w x) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_range]
      have := hW x hx
      omega
    rw [this, Finset.card_range]
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.card_filter]

omit [DecidableEq α] in
/-- In a list sorted by nonincreasing weight, everything after the elements heavier than `t` has
weight at most `t`. -/
private theorem mem_dropWhile_le (w : α → ℕ) (t : ℕ) {l : List α}
    (hsorted : l.Pairwise fun a b => w b ≤ w a) :
    ∀ x ∈ l.dropWhile (fun x => decide (t < w x)), w x ≤ t := by
  induction l with
  | nil => simp
  | cons a l ih =>
      intro x hx
      by_cases ha : t < w a
      · simp only [List.dropWhile_cons, ha, decide_true] at hx
        exact ih hsorted.of_cons x hx
      · simp only [List.dropWhile_cons, ha, decide_false] at hx
        rcases List.mem_cons.1 hx with rfl | hx
        · omega
        · have := List.rel_of_pairwise_cons hsorted hx
          omega

/-- **Threshold counts of the matroid greedy result.** Let $M$ be a matroid on a type $\alpha$, let
$O$ be an oracle that accepts a finite set $A \subseteq \alpha$ exactly when $A$ is independent in
$M$, and let $w : \alpha \to \mathbb{N}$ be a weight function. Let $L$ be a list of elements of
$\alpha$ in nonincreasing order of weight (whenever $a$ occurs before $b$ in $L$, $w(b) \le w(a)$),
and let $G$ be the set returned by the greedy algorithm with oracle $O$ on $L$. Then for every
finite independent set $I$ of $M$ whose elements all occur in $L$ and every $t \in \mathbb{N}$, the
number of $x \in I$ with $w(x) > t$ is at most the number of $x \in G$ with $w(x) > t$. -/
theorem card_filter_le_matroidGreedy (hind : ∀ S, indep S = true ↔ M.Indep ↑S) (w : α → ℕ)
    {es : List α} (hsorted : es.Pairwise fun a b => w b ≤ w a) {I : Finset α}
    (hI : M.Indep ↑I) (hIes : ∀ x ∈ I, x ∈ es) (t : ℕ) :
    (I.filter fun x => t < w x).card ≤
      ((matroidGreedy indep es).ret.filter fun x => t < w x).card := by
  set P := es.takeWhile fun x => decide (t < w x)
  set Q := es.dropWhile fun x => decide (t < w x)
  have hPQ : P ++ Q = es := List.takeWhile_append_dropWhile
  have hP : ∀ x ∈ P, t < w x := fun x hx => by simpa using List.mem_takeWhile_imp hx
  have hQ : ∀ x ∈ Q, w x ≤ t := mem_dropWhile_le w t hsorted
  set SP := (matroidGreedyScan indep ∅ P).ret
  obtain ⟨hSP, hmax⟩ := matroidGreedyScan_spec hind (S := ∅) (by simp) P
  have hG : (matroidGreedy indep es).ret = (matroidGreedyScan indep SP Q).ret := by
    rw [matroidGreedy, ← hPQ, matroidGreedyScan_append]
  -- the greedy result keeps all of `SP`, whose elements are heavier than `t`
  have hSPsub : SP ⊆ (matroidGreedy indep es).ret.filter fun x => t < w x := by
    intro x hx
    refine Finset.mem_filter.2 ⟨hG ▸ subset_matroidGreedyScan indep SP Q hx, ?_⟩
    rcases mem_matroidGreedyScan indep ∅ P hx with h | h
    · simp at h
    · exact hP x h
  refine le_trans ?_ (Finset.card_le_card hSPsub)
  -- augmentation against the maximal independent subset `SP` of `P`
  by_contra hlt
  replace hlt := Nat.lt_of_not_le hlt
  set J := I.filter fun x => t < w x
  have hJ : M.Indep ↑J := hI.subset (fun x hx => (Finset.mem_filter.1 hx).1)
  have hcard : (SP : Set α).encard < (J : Set α).encard := by
    simpa [Set.encard_coe_eq_coe_finsetCard] using hlt
  obtain ⟨e, ⟨heJ, heSP⟩, hins⟩ := hSP.exists_insert_of_encard_lt hJ hcard
  have heJ' := Finset.mem_filter.1 (Finset.mem_coe.1 heJ)
  have heP : e ∈ P := by
    have hees := hIes e heJ'.1
    rw [← hPQ] at hees
    rcases List.mem_append.1 hees with h | h
    · exact h
    · exact absurd (hQ e h) (by omega)
  exact hmax e heP heSP hins

/-- **Optimality of the matroid greedy algorithm.** Let $M$ be a matroid on a type $\alpha$, let $O$
be an oracle that accepts a finite set $A \subseteq \alpha$ exactly when $A$ is independent in $M$,
and let $w : \alpha \to \mathbb{N}$ be a weight function. Let $L$ be a list of elements of $\alpha$
in nonincreasing order of weight (whenever $a$ occurs before $b$ in $L$, $w(b) \le w(a)$), and let
$G$ be the set returned by the greedy algorithm with oracle $O$ on $L$. Then every finite
independent set $I$ of $M$ whose elements all occur in $L$ satisfies
$\sum_{x \in I} w(x) \le \sum_{x \in G} w(x)$.

Source: CLRS, third edition, Theorem 16.11. -/
theorem matroidGreedy_optimal (hind : ∀ S, indep S = true ↔ M.Indep ↑S) (w : α → ℕ)
    {es : List α} (hsorted : es.Pairwise fun a b => w b ≤ w a) {I : Finset α}
    (hI : M.Indep ↑I) (hIes : ∀ x ∈ I, x ∈ es) :
    ∑ x ∈ I, w x ≤ ∑ x ∈ (matroidGreedy indep es).ret, w x := by
  set W := (es.map w).sum
  have hW : ∀ x ∈ es, w x ≤ W := fun x hx =>
    List.le_sum_of_mem (List.mem_map_of_mem hx)
  rw [sum_eq_sum_card_filter w I (W := W) (fun x hx => hW x (hIes x hx)),
    sum_eq_sum_card_filter w _ (W := W)
      (fun x hx => hW x ((matroidGreedy_indep hind es).2 x hx))]
  exact Finset.sum_le_sum fun t _ =>
    card_filter_le_matroidGreedy hind w hsorted hI hIes t

end Cslib.Algorithms.Lean.TimeM
