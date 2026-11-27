/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Greedy.MatroidGreedy
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.Ring

/-!
# Greedy optimality characterizes matroids

The converse of CLRS Theorem 16.11 (Rado 1957; Edmonds 1971; Korte and Vygen,
*Combinatorial Optimization*, Theorem 13.20): an independence system on a finite ground set on
which the greedy algorithm is optimal for every nonnegative weight function is a matroid.

An *independence system* is an oracle `indep : Finset α → Bool` under which `∅` is independent
and subsets of independent sets are independent (`IsIndepSystem`). `GreedyOptimal indep` says
that for every weight `w : α → ℕ` and every listing of all elements in nonincreasing weight order,
`matroidGreedy` (`CSLibExt.Algorithms.Lean.Greedy.MatroidGreedy`) weighs at least as much as
every independent set.

* `augment_of_greedyOptimal`: greedy optimality gives the augmentation axiom. If `|I| < |J|` and
  no element of `J \ I` extends `I`, weight `I` by `|I| + 2` and `J \ I` by `|I| + 1`: greedy
  takes `I`, then nothing of weight above `0`, for `|I|(|I| + 2)`, while `J` weighs at least
  `(|I| + 1)²`.
* `exists_matroid_of_greedyOptimal`: the oracle is the independence predicate of a Mathlib
  `Matroid` on the whole type.
* `greedyOptimal_iff_exists_matroid`: with `matroidGreedy_optimal`, an independence system is
  greedy-optimal exactly when it is a matroid.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

universe u

variable {α : Type u} [DecidableEq α]

/-- **Independence system.** A predicate $\mathrm{indep}$ on the finite subsets of a type
$\alpha$ is an independence system when the empty set is independent and every subset of an
independent set is independent. -/
structure IsIndepSystem (indep : Finset α → Bool) : Prop where
  empty : indep ∅ = true
  subset : ∀ ⦃S T : Finset α⦄, T ⊆ S → indep S = true → indep T = true

/-! ## Greedy runs on an independence system -/

/-- **A scan inside an independent set keeps everything.** Let $\alpha$ be a type, let
$\mathrm{indep}$ be an independence system on the finite subsets of $\alpha$ and let $I$ be an
independent set. For every list $L$ of elements of $I$ and every finite set $S \subseteq I$, the
greedy scan of $L$ starting from $S$ returns $S$ together with all elements of $L$. -/
theorem matroidGreedyScan_of_subset {indep : Finset α → Bool} (hsys : IsIndepSystem indep)
    {I : Finset α} (hI : indep I = true) :
    ∀ (L : List α) (S : Finset α), S ⊆ I → (∀ e ∈ L, e ∈ I) →
      (matroidGreedyScan indep S L).ret = S ∪ L.toFinset
  | [], S, _, _ => by simp [matroidGreedyScan]
  | e :: L, S, hS, hL => by
      have he : e ∈ I := hL e List.mem_cons_self
      have hins : insert e S ⊆ I := Finset.insert_subset he hS
      simp only [matroidGreedyScan, hsys.subset hins hI, ite_true, ret_bind]
      rw [matroidGreedyScan_of_subset hsys hI L (insert e S) hins
        (fun x hx => hL x (List.mem_cons_of_mem _ hx))]
      ext x
      simp

/-- **A scan that accepts nothing.** Let $\alpha$ be a type, let $\mathrm{indep}$ be an
independence oracle on the finite subsets of $\alpha$, let $S$ be a finite subset of $\alpha$
and let $L$ be a list of elements of $\alpha$ such that $\mathrm{indep}$ rejects $S \cup \{e\}$
for every $e$ in $L$. Then the greedy scan of $L$ starting from $S$ returns $S$. -/
theorem matroidGreedyScan_of_forall_not {indep : Finset α → Bool} (S : Finset α) :
    ∀ L : List α, (∀ e ∈ L, indep (insert e S) = false) → (matroidGreedyScan indep S L).ret = S
  | [], _ => by simp [matroidGreedyScan]
  | e :: L, hL => by
      simp only [matroidGreedyScan, hL e List.mem_cons_self, Bool.false_eq_true, ite_false,
        ret_bind]
      exact matroidGreedyScan_of_forall_not S L fun x hx => hL x (List.mem_cons_of_mem _ hx)

/-! ## The converse -/

/-- **Greedy optimality.** Let $\alpha$ be a finite type and let $\mathrm{indep}$ be an
independence oracle on the finite subsets of $\alpha$. The greedy algorithm is optimal for
$\mathrm{indep}$ when, for every weight function $w : \alpha \to \mathbb{N}$ and every list $L$
that contains every element of $\alpha$ exactly once, in nonincreasing order of $w$, the set $T$
returned by the matroid greedy algorithm on $L$ with oracle $\mathrm{indep}$ satisfies
$\sum_{x \in I} w(x) \le \sum_{x \in T} w(x)$ for every finite set $I$ independent under
$\mathrm{indep}$.

Finiteness of $\alpha$ keeps this from holding vacuously: on an infinite type no list contains
every element. -/
@[nolint unusedArguments]
def GreedyOptimal [Finite α] (indep : Finset α → Bool) : Prop :=
  ∀ (w : α → ℕ) (es : List α), es.Nodup → (∀ x, x ∈ es) →
    (es.Pairwise fun a b => w b ≤ w a) →
      ∀ I, indep I = true → ∑ x ∈ I, w x ≤ ∑ x ∈ (matroidGreedy indep es).ret, w x

variable [Finite α]

/-- **Greedy optimality gives the augmentation axiom.** Let $\alpha$ be a finite type and let
$\mathrm{indep}$ be an independence system on the finite subsets of $\alpha$ for which the greedy
algorithm is optimal. If $I$ and $J$ are independent sets with $|I| < |J|$, then some element
$e \in J$ with $e \notin I$ makes $I \cup \{e\}$ independent. -/
theorem augment_of_greedyOptimal {indep : Finset α → Bool} (hsys : IsIndepSystem indep)
    (hopt : GreedyOptimal indep) {I J : Finset α} (hI : indep I = true) (hJ : indep J = true)
    (hlt : I.card < J.card) : ∃ e ∈ J, e ∉ I ∧ indep (insert e I) = true := by
  let := Fintype.ofFinite α
  by_contra hno
  push Not at hno
  have hfalse : ∀ e ∈ J \ I, indep (insert e I) = false := fun e he => by
    rw [Finset.mem_sdiff] at he
    simpa using hno e he.1 he.2
  set k := I.card
  let w : α → ℕ := fun e => if e ∈ I then k + 2 else if e ∈ J then k + 1 else 0
  let rest : Finset α := Finset.univ \ (I ∪ J)
  let es : List α := I.toList ++ (J \ I).toList ++ rest.toList
  -- `es` lists every element once, heaviest first
  have hnodup : es.Nodup := by
    refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨I.nodup_toList, (J \ I).nodup_toList, ?_⟩,
      rest.nodup_toList, ?_⟩
    · intro a ha b hb hab
      subst hab
      simp only [Finset.mem_toList, Finset.mem_sdiff] at ha hb
      exact hb.2 ha
    · intro a ha b hb hab
      subst hab
      simp only [List.mem_append, Finset.mem_toList, Finset.mem_sdiff, rest,
        Finset.mem_univ, Finset.mem_union, true_and] at ha hb
      tauto
  have hcover : ∀ x, x ∈ es := fun x => by
    by_cases hxI : x ∈ I
    · simp [es, hxI]
    · by_cases hxJ : x ∈ J
      · simp [es, hxI, hxJ]
      · simp [es, rest, hxI, hxJ]
  have hsorted : es.Pairwise fun a b => w b ≤ w a := by
    simp only [es, List.pairwise_append, List.mem_append, Finset.mem_toList]
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · exact List.Pairwise.imp_of_mem (fun {a b} ha hb _ => by
        simp only [Finset.mem_toList] at ha hb
        simp [w, ha, hb]) (List.pairwise_of_forall (fun _ _ => trivial))
    · exact List.Pairwise.imp_of_mem (fun {a b} ha hb _ => by
        simp only [Finset.mem_toList, Finset.mem_sdiff] at ha hb
        simp [w, ha.2, hb.2, ha.1, hb.1]) (List.pairwise_of_forall (fun _ _ => trivial))
    · intro a ha b hb
      simp only [Finset.mem_sdiff] at hb
      simp [w, ha, hb.2, hb.1]
    · exact List.Pairwise.imp_of_mem (fun {a b} ha hb _ => by
        simp only [Finset.mem_toList, rest, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union,
          true_and, not_or] at ha hb
        simp [w, ha.1, hb.1, ha.2, hb.2]) (List.pairwise_of_forall (fun _ _ => trivial))
    · intro a ha b hb
      simp only [rest, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and,
        not_or] at hb
      simp [w, hb.1, hb.2]
  -- the greedy run: all of `I`, then nothing from `J \ I`, then weight-zero elements
  have hG1 : (matroidGreedyScan indep ∅ I.toList).ret = I := by
    rw [matroidGreedyScan_of_subset hsys hI I.toList ∅ (Finset.empty_subset _)
      (fun e he => Finset.mem_toList.1 he)]
    simp
  have hG2 : (matroidGreedyScan indep I (J \ I).toList).ret = I :=
    matroidGreedyScan_of_forall_not I _ fun e he => hfalse e (Finset.mem_toList.1 he)
  set G := (matroidGreedy indep es).ret with hG
  have hGeq : G = (matroidGreedyScan indep I rest.toList).ret := by
    rw [hG, matroidGreedy, matroidGreedyScan_append, matroidGreedyScan_append, hG1, hG2]
  have hIG : I ⊆ G := hGeq ▸ subset_matroidGreedyScan indep I rest.toList
  have hgreedy : ∑ x ∈ G, w x = ∑ x ∈ I, w x := by
    refine (Finset.sum_subset hIG fun x hxG hxI => ?_).symm
    rw [hGeq] at hxG
    rcases mem_matroidGreedyScan indep I rest.toList hxG with h | h
    · exact absurd h hxI
    · simp only [Finset.mem_toList, rest, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union,
        true_and, not_or] at h
      simp [w, h.1, h.2]
  have hIw : ∑ x ∈ I, w x = k * (k + 2) := by
    rw [Finset.sum_congr rfl (fun x hx => show w x = k + 2 by simp [w, hx]), Finset.sum_const,
      smul_eq_mul]
  have hJw : J.card * (k + 1) ≤ ∑ x ∈ J, w x := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun x hx => ?_
    by_cases hxI : x ∈ I
    · simp [w, hxI]
    · simp [w, hxI, hx]
  have hle := hopt w es hnodup hcover hsorted J hJ
  rw [← hG, hgreedy, hIw] at hle
  have h1 : (k + 1) * (k + 1) ≤ k * (k + 2) :=
    (Nat.mul_le_mul_right _ hlt).trans (hJw.trans hle)
  have h2 : (k + 1) * (k + 1) = k * (k + 2) + 1 := by ring
  omega

/-- **Greedy-optimal independence systems are matroids.** Let $\alpha$ be a finite type and let
$\mathrm{indep}$ be an independence system on the finite subsets of $\alpha$ for which the greedy
algorithm is optimal. Then there is a matroid $M$ on $\alpha$ whose ground set is all of
$\alpha$ such that a finite set $S \subseteq \alpha$ is independent in $M$ exactly when $S$ is
independent under $\mathrm{indep}$. -/
theorem exists_matroid_of_greedyOptimal {indep : Finset α → Bool} (hsys : IsIndepSystem indep)
    (hopt : GreedyOptimal indep) :
    ∃ M : Matroid α, M.E = Set.univ ∧ ∀ S : Finset α, M.Indep ↑S ↔ indep S = true := by
  refine ⟨(IndepMatroid.ofFinset Set.univ (fun S => indep S = true) hsys.empty
    (fun _ _ hJ hIJ => hsys.subset hIJ hJ)
    (fun _ _ hI hJ hlt => augment_of_greedyOptimal hsys hopt hI hJ hlt)
    (fun _ _ => Set.subset_univ _)).matroid, rfl, fun S => ?_⟩
  simp only [IndepMatroid.matroid_Indep, IndepMatroid.ofFinset_indep]

/-- **Rado–Edmonds theorem.** Let $\alpha$ be a finite type and let $\mathrm{indep}$ be an
independence system on the finite subsets of $\alpha$. The greedy algorithm is optimal for
$\mathrm{indep}$ if and only if there is a matroid $M$ on $\alpha$ whose ground set is all of
$\alpha$ such that a finite set $S \subseteq \alpha$ is independent in $M$ exactly when $S$ is
independent under $\mathrm{indep}$. -/
theorem greedyOptimal_iff_exists_matroid {indep : Finset α → Bool} (hsys : IsIndepSystem indep) :
    GreedyOptimal indep ↔
      ∃ M : Matroid α, M.E = Set.univ ∧ ∀ S : Finset α, M.Indep ↑S ↔ indep S = true := by
  refine ⟨exists_matroid_of_greedyOptimal hsys, ?_⟩
  rintro ⟨M, -, hM⟩ w es _ hcover hsorted I hI
  exact matroidGreedy_optimal (fun S => (hM S).symm) w hsorted ((hM I).2 hI)
    (fun x _ => hcover x)

end Cslib.Algorithms.Lean.TimeM
