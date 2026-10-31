/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.CausalBayesNet
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The global Markov property of Bayesian networks

For a Bayesian network (`BayesNet`, nodes in a topological order, finite state space), d-separation
in its graph implies conditional independence under its joint law: **the global Markov
property** (Geiger, Verma & Pearl 1990; Lauritzen, Dawid, Larsen & Leimer 1990; Pearl 2009,
Theorem 1.2.4). d-separation `BayesNet.DSeparated` and conditional independence `CondIndep` are
those of `CSLibExt/MachineLearning/GraphicalModels/CausalBayesNet.lean`.

## Main definitions

* `BayesNet.IsAncestral b A`: `A` contains the parents of each of its nodes.
* `BayesNet.ancProd b A`: the product of the tables of the nodes of `A`, with the uniform law on
  the other nodes.

## Main results

* `margProb_eq_sum_insert`, `margProb_le_of_subset`, and the semi-graphoid properties
  `CondIndep.symm`, `CondIndep.mono_left` (decomposition) and `CondIndep.weak_union`.
* `BayesNet.margProb_joint_eq_ancProd`: the law of an ancestral set depends only on the tables
  of its nodes.
* `BayesNet.condIndep_of_dSeparated`: **the global Markov property**.

## Proof

By induction over ancestral sets `A`, removing the last node `s` of `A` (a sink of the subgraph
on `A`), for d-separation in the subgraph on `A`. When `s` is in the conditioning set, one of the
two sides absorbs all its parents outside the conditioning set; otherwise a path through `s`
gives an active walk, and active walks shorten to active paths. The probabilistic steps use
decomposition and weak union of `CondIndep`.

## References

* D. Geiger, T. Verma and J. Pearl, *Identifying independence in Bayesian networks*, Networks
  20(5) (1990), 507–534.
* S. L. Lauritzen, A. P. Dawid, B. N. Larsen and H.-G. Leimer, *Independence properties of
  directed Markov fields*, Networks 20(5) (1990), 491–505.
* J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed., Cambridge University Press
  (2009), §1.2.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset Convexity

variable {α : Type*}

/-! ### Properties of `margProb` and `CondIndep` -/

section CondIndep

variable {n : ℕ} [Fintype α] [DecidableEq α]

/-- `margProb P S x'` depends only on the values of `x'` on `S`. -/
theorem margProb_congr (P : (Fin n → α) → ℝ) (S : Finset (Fin n)) {x y : Fin n → α}
    (h : ∀ i ∈ S, x i = y i) : margProb P S x = margProb P S y := by
  unfold margProb
  congr 1
  exact Finset.filter_congr fun z _ => forall₂_congr fun i hi => by rw [h i hi]

/-- Marginal probabilities of a nonnegative law are nonnegative. -/
theorem margProb_nonneg {P : (Fin n → α) → ℝ} (hP : ∀ x, 0 ≤ P x) (S : Finset (Fin n))
    (x' : Fin n → α) : 0 ≤ margProb P S x' := by
  exact sum_nonneg fun x _ => hP x

/-- Fixing more variables decreases the probability. -/
theorem margProb_le_of_subset {P : (Fin n → α) → ℝ} (hP : ∀ x, 0 ≤ P x)
    {S T : Finset (Fin n)} (hST : S ⊆ T) (x' : Fin n → α) :
    margProb P T x' ≤ margProb P S x' := by
  refine sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) fun x _ _ => hP x
  simp only [mem_filter, mem_univ, true_and] at hx ⊢
  exact fun i hi => hx i (hST hi)

/-- Summing out one more variable `i ∉ S`. -/
theorem margProb_eq_sum_insert (P : (Fin n → α) → ℝ) {S : Finset (Fin n)} {i : Fin n}
    (hi : i ∉ S) (x' : Fin n → α) :
    margProb P S x' = ∑ a, margProb P (insert i S) (Function.update x' i a) := by
  unfold margProb
  rw [← Finset.sum_fiberwise (univ.filter fun x : Fin n → α => ∀ j ∈ S, x j = x' j)
    (fun x => x i)]
  refine sum_congr rfl fun a _ => ?_
  rw [Finset.filter_filter]
  refine sum_congr (Finset.filter_congr fun x _ => ?_) fun _ _ => rfl
  simp only [Finset.mem_insert, forall_eq_or_imp, Function.update_self]
  have hne : ∀ j ∈ S, j ≠ i := fun j hj h => hi (h ▸ hj)
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, fun j hj => by rw [h1 j hj, Function.update_of_ne (hne j hj)]⟩
  · rintro ⟨h2, h1⟩
    exact ⟨fun j hj => by rw [h1 j hj, Function.update_of_ne (hne j hj)], h2⟩

/-- Conditional independence is symmetric. -/
theorem CondIndep.symm {P : (Fin n → α) → ℝ} {X Y Z : Finset (Fin n)}
    (h : CondIndep P X Y Z) : CondIndep P Y X Z := by
  intro x'
  have := h x'
  rw [Finset.union_comm Y X, mul_comm (margProb P (Y ∪ Z) x')]
  exact this

/-- Removing one variable `i ∉ Y` from the first set preserves conditional independence. -/
private lemma condIndep_of_insert {P : (Fin n → α) → ℝ} {X Y Z : Finset (Fin n)} {i : Fin n}
    (hiY : i ∉ Y) (h : CondIndep P (insert i X) Y Z) : CondIndep P X Y Z := by
  by_cases hiX : i ∈ X
  · rwa [Finset.insert_eq_of_mem hiX] at h
  by_cases hiZ : i ∈ Z
  · intro x'
    have := h x'
    rwa [insert_union, insert_union, insert_eq_of_mem (mem_union_right _ hiZ), insert_union,
      insert_eq_of_mem (mem_union_right _ hiZ)] at this
  intro x'
  have hi1 : i ∉ X ∪ Y ∪ Z := by simp [hiX, hiY, hiZ]
  have hi2 : i ∉ X ∪ Z := by simp [hiX, hiZ]
  rw [margProb_eq_sum_insert P hi1, margProb_eq_sum_insert P hi2, sum_mul, sum_mul]
  refine sum_congr rfl fun a _ => ?_
  have := h (Function.update x' i a)
  rw [insert_union, insert_union, insert_union] at this
  have hz : margProb P Z (Function.update x' i a) = margProb P Z x' :=
    margProb_congr P Z fun j hj => Function.update_of_ne (fun h => hiZ (by rwa [h] at hj)) _ _
  have hyz : margProb P (Y ∪ Z) (Function.update x' i a) = margProb P (Y ∪ Z) x' :=
    margProb_congr P _ fun j hj => Function.update_of_ne (fun h => by
      subst h; rcases mem_union.1 hj with h | h <;> contradiction) _ _
  rw [← hz, ← hyz]
  exact this

/-- **Decomposition**: if `X ⫫ Y | Z` then `X' ⫫ Y | Z` for `X' ⊆ X`. -/
theorem CondIndep.mono_left {P : (Fin n → α) → ℝ} {X X' Y Z : Finset (Fin n)}
    (h : CondIndep P X Y Z) (hX' : X' ⊆ X) (hXY : Disjoint X Y) : CondIndep P X' Y Z := by
  have key : ∀ (D X' : Finset (Fin n)), CondIndep P (X' ∪ D) Y Z → Disjoint (X' ∪ D) Y →
      CondIndep P X' Y Z := by
    intro D
    induction D using Finset.induction_on with
    | empty => intro X' h _; simpa using h
    | insert i D hiD ih =>
      intro X' h hd
      rw [union_insert] at h
      have hiY : i ∉ Y := fun hy =>
        Finset.disjoint_left.1 hd (mem_union_right _ (mem_insert_self i D)) hy
      exact ih X' (condIndep_of_insert hiY h)
        (hd.mono_left (union_subset_union_right (subset_insert i D)))
  rw [← union_sdiff_of_subset hX'] at h hXY
  exact key _ _ h hXY

/-- **Weak union**: if `X ∪ W ⫫ Y | Z` then `X ⫫ Y | Z ∪ W` (for a nonnegative law). -/
theorem CondIndep.weak_union {P : (Fin n → α) → ℝ} (hP : ∀ x, 0 ≤ P x)
    {X W Y Z : Finset (Fin n)} (h : CondIndep P (X ∪ W) Y Z) (hXY : Disjoint (X ∪ W) Y) :
    CondIndep P X Y (Z ∪ W) := by
  have hW : CondIndep P W Y Z := h.mono_left subset_union_right hXY
  intro x'
  have e1 : X ∪ Y ∪ (Z ∪ W) = X ∪ W ∪ Y ∪ Z := by ext; simp only [mem_union]; tauto
  have e2 : X ∪ (Z ∪ W) = X ∪ W ∪ Z := by ext; simp only [mem_union]; tauto
  have e3 : Y ∪ (Z ∪ W) = W ∪ Y ∪ Z := by ext; simp only [mem_union]; tauto
  rw [e1, e2, e3, union_comm Z W]
  have h1 := h x'
  have h2 := hW x'
  by_cases hz : margProb P Z x' = 0
  · have z1 : margProb P (W ∪ Z) x' = 0 := le_antisymm
      (hz ▸ margProb_le_of_subset hP subset_union_right x') (margProb_nonneg hP _ _)
    have z2 : margProb P (X ∪ W ∪ Z) x' = 0 := le_antisymm
      (hz ▸ margProb_le_of_subset hP subset_union_right x') (margProb_nonneg hP _ _)
    rw [z1, z2, mul_zero, zero_mul]
  · apply mul_left_cancel₀ hz
    linear_combination margProb P (W ∪ Z) x' * h1 - margProb P (X ∪ W ∪ Z) x' * h2

end CondIndep

section Split

variable {n : ℕ}

/-- Sums over assignments split at the coordinate `s`. -/
private lemma sum_split_at [Fintype α] (s : Fin n) (g : (Fin n → α) → ℝ) :
    ∑ x, g x = ∑ y : {j // j ≠ s} → α, ∑ a, g ((Equiv.funSplitAt s α).symm (a, y)) := by
  rw [← (Equiv.funSplitAt s α).symm.sum_comp, Fintype.sum_prod_type, sum_comm]

private lemma funSplitAt_symm_self (s : Fin n) (a : α) (y : {j // j ≠ s} → α) :
    (Equiv.funSplitAt s α).symm (a, y) s = a := by
  simp [Equiv.funSplitAt, Equiv.piSplitAt]

private lemma funSplitAt_symm_of_ne (s : Fin n) (a : α) (y : {j // j ≠ s} → α)
    {j : Fin n} (h : j ≠ s) : (Equiv.funSplitAt s α).symm (a, y) j = y ⟨j, h⟩ := by
  simp [Equiv.funSplitAt, Equiv.piSplitAt, h]

end Split

namespace BayesNet

section Graph

variable {n : ℕ} (b : BayesNet α n)

/-- A set of nodes is ancestral if it contains the parents of each of its nodes. -/
def IsAncestral (A : Finset (Fin n)) : Prop :=
  ∀ ⦃i j : Fin n⦄, b.Edge i j → j ∈ A → i ∈ A

/-! ### d-separation inside an ancestral set -/

/-- `j` is a descendant of `i` through nodes of `A`. -/
private def DescIn (A : Finset (Fin n)) (i j : Fin n) : Prop :=
  Relation.ReflTransGen (fun u v => b.Edge u v ∧ v ∈ A) i j

/-- The consecutive nodes `u, m, w` are blocked by `Z` in the subgraph on `A`. -/
private def BlockedIn (A Z : Finset (Fin n)) (u m w : Fin n) : Prop :=
  (b.Edge u m ∧ b.Edge w m ∧ ∀ d, b.DescIn A m d → d ∉ Z) ∨
    (¬(b.Edge u m ∧ b.Edge w m) ∧ m ∈ Z)

/-- An active walk given `Z` in the subgraph on `A`: consecutive nodes adjacent, all nodes in
`A`, no three consecutive nodes blocked. Nodes may repeat. -/
private def ActiveIn (A Z : Finset (Fin n)) (p : List (Fin n)) : Prop :=
  p.IsChain b.Adj ∧ (∀ v ∈ p, v ∈ A) ∧
    ∀ (i : ℕ) (h : i + 2 < p.length), ¬b.BlockedIn A Z p[i] p[i + 1] p[i + 2]

/-- d-separation in the subgraph on `A`: no path from `X` to `Y` is active given `Z`. -/
private def DSepIn (A X Y Z : Finset (Fin n)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, ∀ p, b.IsPath x y p → b.ActiveIn A Z p → False

private lemma descIn_mono {A A' : Finset (Fin n)} (hA : A' ⊆ A) {i j : Fin n}
    (h : b.DescIn A' i j) : b.DescIn A i j := by
  unfold DescIn at h ⊢
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail ⟨hst.1, hA hst.2⟩

private lemma blockedIn_comm {A Z : Finset (Fin n)} {u m w : Fin n} :
    b.BlockedIn A Z u m w ↔ b.BlockedIn A Z w m u := by
  unfold BlockedIn
  constructor <;> rintro (⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
  · exact Or.inl ⟨h2, h1, h3⟩
  · exact Or.inr ⟨fun h => h1 ⟨h.2, h.1⟩, h2⟩
  · exact Or.inl ⟨h2, h1, h3⟩
  · exact Or.inr ⟨fun h => h1 ⟨h.2, h.1⟩, h2⟩

/-- Activity transfers to a larger subgraph and a conditioning set that agrees on the smaller
subgraph. -/
private lemma activeIn_mono {A A' Z Z' : Finset (Fin n)} (hA : A' ⊆ A) (hZ' : Z' ⊆ Z)
    (hZ : ∀ m ∈ A', m ∈ Z → m ∈ Z') {p : List (Fin n)} (h : b.ActiveIn A' Z' p) :
    b.ActiveIn A Z p := by
  refine ⟨h.1, fun v hv => hA (h.2.1 v hv), fun i hi hb => h.2.2 i hi ?_⟩
  have hm : p[i + 1] ∈ A' := h.2.1 _ (List.getElem_mem _)
  rcases hb with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2, fun d hd hdZ => h3 d (b.descIn_mono hA hd) (hZ' hdZ)⟩
  · exact Or.inr ⟨h1, hZ _ hm h2⟩

private lemma activeIn_tail {A Z : Finset (Fin n)} {v : Fin n} {l : List (Fin n)}
    (h : b.ActiveIn A Z (v :: l)) : b.ActiveIn A Z l :=
  ⟨h.1.tail, fun u hu => h.2.1 u (List.mem_cons_of_mem _ hu), fun i hi =>
    h.2.2 (i + 1) (by simp; omega)⟩

private lemma activeIn_cons {A Z : Finset (Fin n)} {v w : Fin n} {l : List (Fin n)}
    (h : b.ActiveIn A Z (w :: l)) (hv : v ∈ A) (hvw : b.Adj v w)
    (h0 : ∀ hl : 0 < l.length, ¬b.BlockedIn A Z v w l[0]) : b.ActiveIn A Z (v :: w :: l) := by
  refine ⟨List.IsChain.cons_cons hvw h.1, ?_, ?_⟩
  · intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    exacts [hv, h.2.1 u hu]
  · intro i hi
    cases i with
    | zero => exact h0 (by simp at hi; omega)
    | succ i => exact h.2.2 i (by simp at hi ⊢; omega)

private lemma activeIn_reverse {A Z : Finset (Fin n)} {p : List (Fin n)}
    (h : b.ActiveIn A Z p) : b.ActiveIn A Z p.reverse := by
  refine ⟨List.isChain_reverse.2 (h.1.imp fun a b hab => hab.symm),
    fun v hv => h.2.1 v (List.mem_reverse.1 hv), fun i hi hb => ?_⟩
  simp only [List.length_reverse] at hi
  refine h.2.2 (p.length - 3 - i) (by omega) ?_
  rw [blockedIn_comm]
  simp only [List.getElem_reverse] at hb
  have e0 : p.length - 1 - (i + 2) = p.length - 3 - i := by omega
  have e1 : p.length - 1 - (i + 1) = p.length - 3 - i + 1 := by omega
  have e2 : p.length - 1 - i = p.length - 3 - i + 2 := by omega
  simp only [e0, e1, e2] at hb
  exact hb

private lemma activeIn_append {A Z : Finset (Fin n)} {m : Fin n} {l₂ : List (Fin n)} :
    ∀ {l₁ : List (Fin n)}, b.ActiveIn A Z (l₁ ++ [m]) → b.ActiveIn A Z (m :: l₂) →
      (∀ u w, l₁.getLast? = some u → l₂.head? = some w → ¬b.BlockedIn A Z u m w) →
      b.ActiveIn A Z (l₁ ++ m :: l₂)
  | [], _, h2, _ => by simpa using h2
  | v :: l₁, h1, h2, hj => by
    have ih : b.ActiveIn A Z (l₁ ++ m :: l₂) :=
      activeIn_append (b.activeIn_tail h1) h2 fun u w hu hw => hj u w (by
        cases l₁ with
        | nil => simp at hu
        | cons a l => simpa [List.getLast?_cons_cons] using hu) hw
    have hv : v ∈ A := h1.2.1 v (by simp)
    cases l₁ with
    | nil =>
      refine b.activeIn_cons h2 hv (by simpa using h1.1) fun hl => ?_
      exact hj v l₂[0] (by simp) (by rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hl])
    | cons w l₁ =>
      refine b.activeIn_cons ih hv (List.isChain_cons_cons.1 (by simpa using h1.1)).1 fun hl => ?_
      have := h1.2.2 0 (by simp)
      cases l₁ <;> simpa using this

private lemma activeIn_forward {α : Type*} {n : ℕ} (b : BayesNet α n)
    {A Z : Finset (Fin n)} {p : List (Fin n)} (hp : b.ActiveIn A Z p)
    {i : ℕ} (hi : i + 1 < p.length) (he : b.Edge p[i] p[i + 1])
    (hz : ∀ d, b.DescIn A p[i] d → d ∉ Z) (k : ℕ) (hik : i ≤ k)
    (hk : k + 1 < p.length) : b.DescIn A p[i] p[k] ∧ b.Edge p[k] p[k + 1] := by
  induction k, hik using Nat.le_induction with
  | base => exact ⟨Relation.ReflTransGen.refl, he⟩
  | succ k hik ih =>
    obtain ⟨hd, he⟩ := ih (by omega)
    have hd' : b.DescIn A p[i] p[k + 1] :=
      hd.tail ⟨he, hp.2.1 _ (List.getElem_mem (by omega))⟩
    refine ⟨hd', ?_⟩
    obtain hforward | hback := List.isChain_iff_getElem.1 hp.1 (k + 1) hk
    · exact hforward
    · exact False.elim (hp.2.2 k (by omega)
        (Or.inl ⟨he, hback, fun d hd => hz d (hd'.trans hd)⟩))

private lemma activeIn_junction {α : Type*} {n : ℕ} (b : BayesNet α n)
    {A Z : Finset (Fin n)} {p : List (Fin n)} (hp : b.ActiveIn A Z p)
    {i j : ℕ} (hi : 0 < i) (hij : i < j) (hj : j + 1 < p.length)
    (heq : p[i] = p[j]) : ¬b.BlockedIn A Z p[i - 1] p[j] p[j + 1] := by
  have hbi : ¬b.BlockedIn A Z p[i - 1] p[i] p[i + 1] := by
    simpa only [show i - 1 + 1 = i by omega, show i - 1 + 2 = i + 1 by omega]
      using hp.2.2 (i - 1) (by omega)
  have hbj : ¬b.BlockedIn A Z p[j - 1] p[j] p[j + 1] := by
    simpa only [show j - 1 + 1 = j by omega, show j - 1 + 2 = j + 1 by omega]
      using hp.2.2 (j - 1) (by omega)
  rintro (⟨hl, hr, hz⟩ | ⟨hc, hz⟩)
  · have hz' : ∀ d, b.DescIn A p[i] d → d ∉ Z := by simpa only [heq] using hz
    have he : b.Edge p[i] p[i + 1] := by
      obtain he | he := List.isChain_iff_getElem.1 hp.1 i (by omega)
      · exact he
      · exact False.elim (hbi (Or.inl ⟨by simpa only [heq] using hl, he, hz'⟩))
    have hlast := (activeIn_forward b hp (by omega) he hz' (j - 1) (by omega)
      (by omega)).2
    have hlast' : b.Edge p[j - 1] p[j] := by
      simpa only [show j - 1 + 1 = j by omega] using hlast
    exact hbj (Or.inl ⟨hlast', hr, hz⟩)
  · have hci : b.Edge p[i - 1] p[i] ∧ b.Edge p[i + 1] p[i] := by
      by_contra h
      exact hbi (Or.inr ⟨h, by simpa only [heq] using hz⟩)
    have hcj : b.Edge p[j - 1] p[j] ∧ b.Edge p[j + 1] p[j] := by
      by_contra h
      exact hbj (Or.inr ⟨h, hz⟩)
    exact hc ⟨by simpa only [heq] using hci.1, hcj.2⟩

private lemma shortcut_get_left {β : Type*} (p : List β) {i j k : ℕ}
    (hi : i ≤ p.length) (hk : k < i)
    (h : k < (p.take i ++ p.drop j).length) : (p.take i ++ p.drop j)[k] = p[k] := by
  rw [List.getElem_append_left (by simpa [List.length_take, Nat.min_eq_left hi] using hk)]
  exact List.getElem_take

private lemma shortcut_get_right {β : Type*} (p : List β) {i j k : ℕ}
    (hi : i ≤ p.length) (hk : i ≤ k)
    (h : k < (p.take i ++ p.drop j).length) :
    (p.take i ++ p.drop j)[k] = p[j + (k - i)]'(by
      simp only [List.length_append, List.length_take, List.length_drop,
        Nat.min_eq_left hi] at h
      omega) := by
  rw [List.getElem_append_right (by simpa [List.length_take, Nat.min_eq_left hi] using hk)]
  simp only [List.getElem_drop, List.length_take, Nat.min_eq_left hi]

private lemma activeIn_shortcut {α : Type*} {n : ℕ} (b : BayesNet α n)
    {A Z : Finset (Fin n)} {p : List (Fin n)} (hp : b.ActiveIn A Z p)
    {i j : ℕ} (hij : i < j) (hj : j < p.length) (heq : p[i] = p[j]) :
    b.ActiveIn A Z (p.take i ++ p.drop j) := by
  have hi : i ≤ p.length := by omega
  have hlen : (p.take i ++ p.drop j).length = i + (p.length - j) := by
    simp [List.length_take, Nat.min_eq_left hi]
  refine ⟨List.isChain_iff_getElem.2 ?_, ?_, ?_⟩
  · intro k hk
    rw [hlen] at hk
    by_cases hki : k + 1 < i
    · rw [shortcut_get_left p hi (by omega), shortcut_get_left p hi hki]
      exact List.isChain_iff_getElem.1 hp.1 k (by omega)
    · by_cases hki' : k < i
      · have hnext : k + 1 = i := by omega
        rw [shortcut_get_left p hi hki', shortcut_get_right p hi (by omega)]
        simp only [hnext, Nat.sub_self, Nat.add_zero, ← heq]
        simpa only [hnext] using List.isChain_iff_getElem.1 hp.1 k (by omega)
      · rw [shortcut_get_right p hi (by omega), shortcut_get_right p hi (by omega)]
        simp only [show j + (k + 1 - i) = j + (k - i) + 1 by omega]
        exact List.isChain_iff_getElem.1 hp.1 (j + (k - i)) (by omega)
  · intro v hv
    apply hp.2.1 v
    obtain hv | hv := List.mem_append.1 hv
    · exact List.mem_of_mem_take hv
    · exact List.mem_of_mem_drop hv
  · intro k hk
    rw [hlen] at hk
    by_cases hki : k + 2 < i
    · rw [shortcut_get_left p hi (by omega), shortcut_get_left p hi (by omega),
        shortcut_get_left p hi hki]
      exact hp.2.2 k (by omega)
    · by_cases hki' : k + 1 < i
      · have hnext : k + 2 = i := by omega
        rw [shortcut_get_left p hi (by omega), shortcut_get_left p hi hki',
          shortcut_get_right p hi (by omega)]
        simp only [hnext, Nat.sub_self, Nat.add_zero, ← heq]
        simpa only [hnext] using hp.2.2 k (by omega)
      · by_cases hki'' : k < i
        · rw [shortcut_get_left p hi hki'', shortcut_get_right p hi (by omega),
            shortcut_get_right p hi (by omega)]
          simp only [show j + (k + 1 - i) = j by omega,
            show j + (k + 2 - i) = j + 1 by omega]
          simp only [show k = i - 1 by omega]
          exact activeIn_junction b hp (by omega) hij (by omega) heq
        · rw [shortcut_get_right p hi (by omega), shortcut_get_right p hi (by omega),
            shortcut_get_right p hi (by omega)]
          simp only [show j + (k + 1 - i) = j + (k - i) + 1 by omega,
            show j + (k + 2 - i) = j + (k - i) + 2 by omega]
          exact hp.2.2 (j + (k - i)) (by omega)

/-- An active walk from `x` to `y` can be shortened to an active path (no repeated node). -/
private theorem exists_path_of_activeIn {A Z : Finset (Fin n)} {p : List (Fin n)}
    {x y : Fin n} (hp : b.ActiveIn A Z p) (hx : p.head? = some x) (hy : p.getLast? = some y) :
    ∃ q, b.IsPath x y q ∧ b.ActiveIn A Z q := by
  classical
  induction hlen : p.length using Nat.strong_induction_on generalizing p with
  | h l ih =>
    by_cases hn : p.Nodup
    · exact ⟨p, ⟨hn, hp.1, hx, hy⟩, hp⟩
    · have hrepeated : ∃ i j : ℕ, ∃ hi : i < p.length, ∃ hj : j < p.length,
          i < j ∧ p[i] = p[j] := by
        rw [List.nodup_iff_injective_getElem] at hn
        simp only [Function.Injective, not_forall] at hn
        obtain ⟨i, j, heq, hne⟩ := hn
        have hne' : i.val ≠ j.val := fun h => hne (Fin.ext h)
        obtain hij | hji := lt_or_gt_of_ne hne'
        · exact ⟨i.val, j.val, i.isLt, j.isLt, hij, heq⟩
        · exact ⟨j.val, i.val, j.isLt, i.isLt, hji, heq.symm⟩
      obtain ⟨i, j, hi, hj, hij, heq⟩ := hrepeated
      let q := p.take i ++ p.drop j
      have hq : b.ActiveIn A Z q := activeIn_shortcut b hp hij hj heq
      have hshort : q.length < l := by
        simp only [q, List.length_append, List.length_take, List.length_drop,
          Nat.min_eq_left hi.le]
        omega
      have hxq : q.head? = some x := by
        dsimp [q]
        by_cases hi0 : i = 0
        · subst i
          rw [List.take_zero, List.nil_append, List.head?_drop,
            List.getElem?_eq_getElem hj, ← heq]
          simpa only [List.head?_eq_getElem?, List.getElem?_eq_getElem hi] using hx
        · rw [List.head?_append, List.head?_take, ite_eq_right hi0, hx]
          rfl
      have hyq : q.getLast? = some y := by
        dsimp [q]
        rw [List.getLast?_append, List.getLast?_drop, ite_eq_right (Nat.not_le_of_lt hj), hy]
        rfl
      exact ih q.length hshort hq hxq hyq rfl

private lemma dSepIn_mono {A A' X X' Y Y' Z Z' : Finset (Fin n)} (hA : A' ⊆ A) (hZ' : Z' ⊆ Z)
    (hZ : ∀ m ∈ A', m ∈ Z → m ∈ Z') (hX : X' ⊆ X) (hY : Y' ⊆ Y) (h : b.DSepIn A X Y Z) :
    b.DSepIn A' X' Y' Z' :=
  fun x hx y hy p hp ha => h x (hX hx) y (hY hy) p hp (b.activeIn_mono hA hZ' hZ ha)

private lemma dSepIn_symm {A X Y Z : Finset (Fin n)} (h : b.DSepIn A X Y Z) :
    b.DSepIn A Y X Z :=
  fun y hy x hx p hp ha => h x hx y hy p.reverse (b.isPath_reverse hp) (b.activeIn_reverse ha)

/-- d-separation forces disjointness: a node of `X ∩ Y` is a one-node active path. -/
private lemma dSepIn_disjoint {A X Y Z : Finset (Fin n)} (hX : X ⊆ A) (h : b.DSepIn A X Y Z) :
    Disjoint X Y :=
  Finset.disjoint_left.2 fun x hx hy => h x hx x hy [x]
    ⟨List.nodup_singleton x, List.isChain_singleton x, rfl, rfl⟩
    ⟨List.isChain_singleton x, fun v hv => by
      rw [List.mem_singleton] at hv; exact hv ▸ hX hx,
      fun i hi => by simp at hi⟩

/-- The step of the global Markov property removing a sink `s ∈ X`. -/
private lemma dSepIn_erase_of_mem {A X Y Z Ps : Finset (Fin n)} {s : Fin n} (hs : s ∈ A)
    (hch : ∀ j ∈ A, ¬b.Edge s j) (hsX : s ∈ X) (hPs : ∀ i ∈ Ps, b.Edge i s ∧ i ∉ Z)
    (h : b.DSepIn A X Y Z) : b.DSepIn (A.erase s) (X.erase s ∪ Ps) Y Z := by
  intro x hx y hy p hp ha
  have ha' := b.activeIn_mono (erase_subset s A) subset_rfl (fun _ _ h => h) ha
  rcases mem_union.1 hx with hx | hx
  · exact h x (mem_of_mem_erase hx) y hy p hp ha'
  obtain ⟨hxs, hxZ⟩ := hPs x hx
  obtain ⟨hnd, hch', hhead, hlast⟩ := hp
  cases p with
  | nil => simp at hhead
  | cons x0 rest =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    have hsp : s ∉ x0 :: rest := fun hm => by simpa using ha.2.1 s hm
    have hxA : x0 ∈ A := mem_of_mem_erase (ha.2.1 x0 (by simp))
    refine h s hsX y hy (s :: x0 :: rest) ⟨List.nodup_cons.2 ⟨hsp, hnd⟩,
      List.IsChain.cons_cons (Or.inr hxs) hch', rfl, by simpa using hlast⟩
      (b.activeIn_cons ha' hs (Or.inr hxs) fun _ hb => ?_)
    rcases hb with ⟨h1, -, -⟩ | ⟨-, h2⟩
    exacts [hch x0 hxA h1, hxZ h2]

/-- The step of the global Markov property removing a sink `s ∈ Z`: one side absorbs all the
parents of `s` outside `Z`. -/
private lemma dSepIn_erase_of_mem_cond {A X Y Z Ps : Finset (Fin n)} {s : Fin n} (hs : s ∈ A)
    (hch : ∀ j ∈ A, ¬b.Edge s j) (hsZ : s ∈ Z) (hPsA : Ps ⊆ A)
    (hPs : ∀ i ∈ Ps, b.Edge i s ∧ i ∉ Z) (h : b.DSepIn A X Y Z) :
    b.DSepIn (A.erase s) (X ∪ Ps) Y (Z.erase s) ∨
      b.DSepIn (A.erase s) X (Y ∪ Ps) (Z.erase s) := by
  have hmono : ∀ {p}, b.ActiveIn (A.erase s) (Z.erase s) p → b.ActiveIn A Z p := fun ha =>
    b.activeIn_mono (erase_subset s A) (erase_subset s Z)
      (fun m hm hmZ => mem_erase.2 ⟨ne_of_mem_erase hm, hmZ⟩) ha
  by_contra hcon
  obtain ⟨h1, h2⟩ := not_or.1 hcon
  simp only [DSepIn, not_forall] at h1 h2
  obtain ⟨u, hu, y, hy, π, hπ, hπa, -⟩ := h1
  rcases mem_union.1 hu with hu | hu
  · exact h u hu y hy π hπ (hmono hπa)
  obtain ⟨x, hx, w, hw, σ, hσ, hσa, -⟩ := h2
  rcases mem_union.1 hw with hw | hw
  · exact h x hx w hw σ hσ (hmono hσa)
  obtain ⟨hus, huZ⟩ := hPs u hu
  obtain ⟨hws, hwZ⟩ := hPs w hw
  have hσA := hmono hσa
  have hπA := hmono hπa
  obtain ⟨-, -, hσh, hσl⟩ := hσ
  obtain ⟨-, -, hπh, hπl⟩ := hπ
  -- the walk `σ ++ s :: π`
  have hrev : b.ActiveIn A Z (s :: σ.reverse) := by
    have hr : σ.reverse.head? = some w := by simpa using hσl
    have hσr := b.activeIn_reverse hσA
    cases hσ' : σ.reverse with
    | nil => simp [hσ'] at hr
    | cons w' t =>
      rw [hσ'] at hr hσr
      simp only [List.head?_cons, Option.some.injEq] at hr
      subst hr
      refine b.activeIn_cons hσr hs (Or.inr hws) fun _ hb => ?_
      rcases hb with ⟨h1, -, -⟩ | ⟨-, h2⟩
      exacts [hch w' (hPsA hw) h1, hwZ h2]
  have h1' : b.ActiveIn A Z (σ ++ [s]) := by simpa using b.activeIn_reverse hrev
  have h2' : b.ActiveIn A Z (s :: π) := by
    cases π with
    | nil => simp at hπh
    | cons u' t =>
      simp only [List.head?_cons, Option.some.injEq] at hπh
      subst hπh
      refine b.activeIn_cons hπA hs (Or.inr hus) fun _ hb => ?_
      rcases hb with ⟨h1, -, -⟩ | ⟨-, h2⟩
      exacts [hch u' (hPsA hu) h1, huZ h2]
  have hW := b.activeIn_append h1' h2' fun u' w' hu' hw' hb => by
    rw [hσl, Option.some.injEq] at hu'
    rw [hπh, Option.some.injEq] at hw'
    subst hu' hw'
    rcases hb with ⟨-, -, h3⟩ | ⟨h3, -⟩
    exacts [h3 s .refl hsZ, h3 ⟨hws, hus⟩]
  have hWh : (σ ++ s :: π).head? = some x := by
    cases σ with
    | nil => simp at hσh
    | cons a l => simpa using hσh
  have hWl : (σ ++ s :: π).getLast? = some y := by
    cases π with
    | nil => simp at hπl
    | cons a l => simpa [List.getLast?_append] using hπl
  obtain ⟨q, hq, hqa⟩ := b.exists_path_of_activeIn hW hWh hWl
  exact h x hx y hy q hq hqa

end Graph

variable {n : ℕ} [Nonempty α] (b : BayesNet α n)


/-- The product of the tables of the nodes in `A`, with the uniform distribution on the other
nodes. For an ancestral `A` it has the same marginals on `A` as the joint
(`margProb_joint_eq_ancProd`). -/
noncomputable def ancProd [Fintype α] (A : Finset (Fin n)) (x : Fin n → α) : ℝ :=
  ∏ j, if j ∈ A then (b.cpt j (b.paVal j x)).weights (x j) else (Fintype.card α : ℝ)⁻¹

/-- On all nodes, `ancProd` is the joint. -/
theorem ancProd_univ [Fintype α] : b.ancProd univ = b.joint := by
  funext x
  rw [ancProd, joint_eq_prod]
  simp only [mem_univ, ite_true]
  rfl

/-- Removing from `B` a node `s` with no child in `B` does not change the marginals of `ancProd`
on sets not containing `s`: the factor of `s` sums to one either way. -/
private lemma margProb_ancProd_erase [Fintype α] [DecidableEq α] {B : Finset (Fin n)}
    {s : Fin n} (hch : ∀ j ∈ B, ¬b.Edge s j) {S : Finset (Fin n)} (hsS : s ∉ S)
    (x' : Fin n → α) :
    margProb (b.ancProd B) S x' = margProb (b.ancProd (B.erase s)) S x' := by
  unfold margProb
  rw [sum_filter, sum_filter, sum_split_at s, sum_split_at s]
  refine sum_congr rfl fun y _ => ?_
  set e := (Equiv.funSplitAt s α).symm with he
  have hcond : ∀ a a', (∀ i ∈ S, e (a, y) i = x' i) ↔ (∀ i ∈ S, e (a', y) i = x' i) := by
    intro a a'
    refine forall₂_congr fun i hi => ?_
    have hi' : i ≠ s := fun h => hsS (h ▸ hi)
    rw [he, funSplitAt_symm_of_ne s a y hi', funSplitAt_symm_of_ne s a' y hi']
  set c : ℝ := (Fintype.card α : ℝ)⁻¹
  have hfac : ∀ (C : Finset (Fin n)) (a : α), b.ancProd C (e (a, y)) =
      (if s ∈ C then (b.cpt s (b.paVal s (e (a, y)))).weights a else c) *
        ∏ j ∈ univ.erase s,
          (if j ∈ C then (b.cpt j (b.paVal j (e (a, y)))).weights (e (a, y) j) else c) := by
    intro C a
    rw [ancProd, ← mul_prod_erase univ _ (mem_univ s), he, funSplitAt_symm_self]
  have hrest : ∀ a a', (∏ j ∈ univ.erase s,
      (if j ∈ B then (b.cpt j (b.paVal j (e (a, y)))).weights (e (a, y) j) else c)) =
      ∏ j ∈ univ.erase s,
      (if j ∈ B.erase s then (b.cpt j (b.paVal j (e (a', y)))).weights (e (a', y) j) else c) := by
    intro a a'
    refine prod_congr rfl fun j hj => ?_
    have hjs := ne_of_mem_erase hj
    simp only [mem_erase, hjs, ne_eq, not_false_eq_true, true_and]
    split_ifs with hjB
    · have hpa : b.paVal j (e (a, y)) = b.paVal j (e (a', y)) := by
        funext i
        have hi : Fin.castLE j.2.le i ≠ s := by
          intro h
          have hv : (i : Fin j).val = s.val := by simpa using congrArg Fin.val h
          refine hch j hjB ⟨by rw [← hv]; exact i.1.2, ?_⟩
          convert i.2 using 1
          exact Fin.ext hv.symm
        simp only [paVal, he, funSplitAt_symm_of_ne s _ y hi]
      rw [hpa, he, funSplitAt_symm_of_ne s a y hjs, funSplitAt_symm_of_ne s a' y hjs]
    · rfl
  have hpas : ∀ a a', b.paVal s (e (a, y)) = b.paVal s (e (a', y)) := by
    intro a a'
    funext i
    have hi : Fin.castLE s.2.le i ≠ s := fun h => by
      have : (i : Fin s).val = s.val := by simpa using congrArg Fin.val h
      exact absurd this (Nat.ne_of_lt i.1.2)
    simp only [paVal, he, funSplitAt_symm_of_ne s _ y hi]
  obtain ⟨a₀⟩ := (inferInstance : Nonempty α)
  by_cases hc : ∀ i ∈ S, e (a₀, y) i = x' i
  · have hc' : ∀ a, ∀ i ∈ S, e (a, y) i = x' i := fun a => (hcond a a₀).2 hc
    rw [sum_congr rfl fun a _ => ite_eq_left (hc' a), sum_congr rfl fun a _ => ite_eq_left (hc' a)]
    simp_rw [hfac]
    have hsB : s ∉ B.erase s := by simp
    simp only [hsB, ite_false]
    by_cases hsB' : s ∈ B
    · simp only [hsB', ite_true]
      have hrest' : ∀ a, (∏ j ∈ univ.erase s,
          (if j ∈ B.erase s then (b.cpt j (b.paVal j (e (a, y)))).weights (e (a, y) j)
            else c)) = ∏ j ∈ univ.erase s,
          (if j ∈ B.erase s then (b.cpt j (b.paVal j (e (a₀, y)))).weights (e (a₀, y) j)
            else c) := fun a => (hrest a₀ a).symm.trans (hrest a₀ a₀)
      simp_rw [hrest _ a₀, hpas _ a₀]
      rw [← sum_mul, (b.cpt s _).total_of_fintype, one_mul,
        sum_congr rfl fun a _ => congrArg (c * ·) (hrest' a), sum_const, card_univ, nsmul_eq_mul,
        ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]
    · have hBe : B.erase s = B := erase_eq_of_notMem hsB'
      simp only [hsB', ite_false, hBe]
  · have hc' : ∀ a, ¬∀ i ∈ S, e (a, y) i = x' i := fun a h => hc ((hcond a a₀).1 h)
    rw [sum_congr rfl fun a _ => ite_eq_right (hc' a),
      sum_congr rfl fun a _ => ite_eq_right (hc' a)]

/-- Fixing in addition the value of a node `s ∈ A` with no child in `A`, whose parents are in
`S`, multiplies the marginal by the table of `s`. -/
private lemma margProb_ancProd_insert [Fintype α] [DecidableEq α] {A : Finset (Fin n)}
    {s : Fin n} (hs : s ∈ A) (hch : ∀ j ∈ A, ¬b.Edge s j) {S : Finset (Fin n)} (hsS : s ∉ S)
    (hpa : ∀ i, b.Edge i s → i ∈ S) (x' : Fin n → α) :
    margProb (b.ancProd A) (insert s S) x' =
      (b.cpt s (b.paVal s x')).weights (x' s) * margProb (b.ancProd (A.erase s)) S x' := by
  unfold margProb
  rw [sum_filter, sum_filter, sum_split_at s, sum_split_at s, mul_sum]
  refine sum_congr rfl fun y _ => ?_
  set e := (Equiv.funSplitAt s α).symm with he
  have hcond : ∀ a a', (∀ i ∈ S, e (a, y) i = x' i) ↔ (∀ i ∈ S, e (a', y) i = x' i) := by
    intro a a'
    refine forall₂_congr fun i hi => ?_
    have hi' : i ≠ s := fun h => hsS (h ▸ hi)
    rw [he, funSplitAt_symm_of_ne s a y hi', funSplitAt_symm_of_ne s a' y hi']
  set c : ℝ := (Fintype.card α : ℝ)⁻¹
  have hfac : ∀ (C : Finset (Fin n)) (a : α), b.ancProd C (e (a, y)) =
      (if s ∈ C then (b.cpt s (b.paVal s (e (a, y)))).weights a else c) *
        ∏ j ∈ univ.erase s,
          (if j ∈ C then (b.cpt j (b.paVal j (e (a, y)))).weights (e (a, y) j) else c) := by
    intro C a
    rw [ancProd, ← mul_prod_erase univ _ (mem_univ s), he, funSplitAt_symm_self]
  have hrest : ∀ a a', (∏ j ∈ univ.erase s,
      (if j ∈ A then (b.cpt j (b.paVal j (e (a, y)))).weights (e (a, y) j) else c)) =
      ∏ j ∈ univ.erase s,
      (if j ∈ A.erase s then (b.cpt j (b.paVal j (e (a', y)))).weights (e (a', y) j) else c) := by
    intro a a'
    refine prod_congr rfl fun j hj => ?_
    have hjs := ne_of_mem_erase hj
    simp only [mem_erase, hjs, ne_eq, not_false_eq_true, true_and]
    split_ifs with hjB
    · have hpa : b.paVal j (e (a, y)) = b.paVal j (e (a', y)) := by
        funext i
        have hi : Fin.castLE j.2.le i ≠ s := by
          intro h
          have hv : (i : Fin j).val = s.val := by simpa using congrArg Fin.val h
          refine hch j hjB ⟨by rw [← hv]; exact i.1.2, ?_⟩
          convert i.2 using 1
          exact Fin.ext hv.symm
        simp only [paVal, he, funSplitAt_symm_of_ne s _ y hi]
      rw [hpa, he, funSplitAt_symm_of_ne s a y hjs, funSplitAt_symm_of_ne s a' y hjs]
    · rfl
  obtain ⟨a₀⟩ := (inferInstance : Nonempty α)
  have hrest' : ∀ a, (∏ j ∈ univ.erase s,
      (if j ∈ A.erase s then (b.cpt j (b.paVal j (e (a, y)))).weights (e (a, y) j)
        else c)) = ∏ j ∈ univ.erase s,
      (if j ∈ A.erase s then (b.cpt j (b.paVal j (e (a₀, y)))).weights (e (a₀, y) j)
        else c) := fun a => (hrest a₀ a).symm.trans (hrest a₀ a₀)
  by_cases hc : ∀ i ∈ S, e (a₀, y) i = x' i
  · have hc' : ∀ a, ∀ i ∈ S, e (a, y) i = x' i := fun a => (hcond a a₀).2 hc
    have hins : ∀ a, (∀ i ∈ insert s S, e (a, y) i = x' i) ↔ a = x' s := by
      intro a
      rw [forall_mem_insert, he, funSplitAt_symm_self]
      exact ⟨fun h => h.1, fun h => ⟨h, hc' a⟩⟩
    simp_rw [hins]
    rw [sum_ite_eq' univ (x' s), ite_eq_left (mem_univ _)]
    rw [sum_congr rfl fun a _ => ite_eq_left (hc' a)]
    simp_rw [hfac]
    have hsA : s ∉ A.erase s := by simp
    simp only [hs, hsA, ite_true, ite_false]
    have hpas : b.paVal s (e (x' s, y)) = b.paVal s x' := by
      funext i
      have hi : Fin.castLE s.2.le i ∈ S := hpa _ ⟨by simp, by simp⟩
      exact hc' (x' s) _ hi
    rw [hpas, hrest (x' s) a₀,
      sum_congr rfl fun a _ => congrArg (c * ·) (hrest' a), sum_const, card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    rw [← mul_assoc (Fintype.card α : ℝ) c,
      mul_inv_cancel₀ hcard, one_mul]
  · have hc' : ∀ a, ¬∀ i ∈ S, e (a, y) i = x' i := fun a h => hc ((hcond a a₀).1 h)
    have hins : ∀ a, ¬∀ i ∈ insert s S, e (a, y) i = x' i := fun a h =>
      hc' a fun i hi => h i (mem_insert_of_mem hi)
    rw [sum_congr rfl fun a _ => ite_eq_right (hins a),
      sum_congr rfl fun a _ => ite_eq_right (hc' a)]
    simp

/-- One-node step of the global Markov property: if `B ⫫ Y | Z` for the tables on `A.erase s`
and the parents of `s` lie in `B ∪ Z`, then `insert s B ⫫ Y | Z` for the tables on `A`. -/
private lemma condIndep_ancProd_insert [Fintype α] [DecidableEq α] {A : Finset (Fin n)}
    {s : Fin n} (hs : s ∈ A) (hch : ∀ j ∈ A, ¬b.Edge s j) {B Y Z : Finset (Fin n)}
    (hsB : s ∉ B) (hsY : s ∉ Y) (hsZ : s ∉ Z) (hpa : ∀ i, b.Edge i s → i ∈ B ∪ Z)
    (h : CondIndep (b.ancProd (A.erase s)) B Y Z) : CondIndep (b.ancProd A) (insert s B) Y Z := by
  intro x'
  have h1 : s ∉ B ∪ Y ∪ Z := by simp [hsB, hsY, hsZ]
  have h2 : s ∉ B ∪ Z := by simp [hsB, hsZ]
  have h3 : s ∉ Y ∪ Z := by simp [hsY, hsZ]
  rw [insert_union, insert_union, insert_union,
    margProb_ancProd_insert b hs hch h1 (fun i hi => by
      rcases mem_union.1 (hpa i hi) with h | h <;> simp [h]) x',
    margProb_ancProd_insert b hs hch h2 hpa x',
    margProb_ancProd_erase b hch hsZ x', margProb_ancProd_erase b hch h3 x']
  have := h x'
  linear_combination (b.cpt s (b.paVal s x')).weights (x' s) * this

/-- **The law of an ancestral set depends only on its tables**: for an ancestral set `A` and
`S ⊆ A`, the marginals of the joint on `S` are those of `ancProd A`. -/
theorem margProb_joint_eq_ancProd [Fintype α] [DecidableEq α] {A : Finset (Fin n)}
    (hA : b.IsAncestral A) {S : Finset (Fin n)} (hS : S ⊆ A) (x' : Fin n → α) :
    margProb b.joint S x' = margProb (b.ancProd A) S x' := by
  have key : ∀ m : ℕ, ∀ B : Finset (Fin n), A ⊆ B → (B \ A).card = m →
      margProb (b.ancProd B) S x' = margProb (b.ancProd A) S x' := by
    intro m
    induction m with
    | zero =>
      intro B hAB hc
      rw [card_eq_zero, sdiff_eq_empty_iff_subset] at hc
      rw [subset_antisymm hc hAB]
    | succ m ih =>
      intro B hAB hc
      have hne : (B \ A).Nonempty := by rw [← card_pos, hc]; omega
      have hsBA : (B \ A).max' hne ∈ B \ A := max'_mem _ _
      set s := (B \ A).max' hne
      have hsA : s ∉ A := (mem_sdiff.1 hsBA).2
      have hch : ∀ j ∈ B, ¬b.Edge s j := by
        intro j hj hE
        by_cases hjA : j ∈ A
        · exact hsA (hA hE hjA)
        · have h1 : j ≤ s := le_max' _ j (mem_sdiff.2 ⟨hj, hjA⟩)
          obtain ⟨hlt, _⟩ := hE
          exact absurd h1 (not_le.2 hlt)
      rw [margProb_ancProd_erase b hch (fun h => hsA (hS h)) x']
      refine ih (B.erase s) (fun i hi => mem_erase.2 ⟨fun h => hsA (h ▸ hi), hAB hi⟩) ?_
      rw [erase_sdiff_comm, card_erase_of_mem hsBA, hc]
      rfl
  rw [← b.ancProd_univ]
  exact key _ univ (subset_univ A) rfl

/-- The global Markov property for the product of the tables on an ancestral set. -/
private theorem condIndep_ancProd [Fintype α] [DecidableEq α] (A : Finset (Fin n))
    (hA : b.IsAncestral A) (X Y Z : Finset (Fin n)) (hX : X ⊆ A) (hY : Y ⊆ A) (hZ : Z ⊆ A)
    (h : b.DSepIn A X Y Z) : CondIndep (b.ancProd A) X Y Z := by
  suffices key : ∀ (m : ℕ) (A : Finset (Fin n)), A.card = m → b.IsAncestral A →
      ∀ X Y Z : Finset (Fin n), X ⊆ A → Y ⊆ A → Z ⊆ A → Disjoint X Z → Disjoint Y Z →
        b.DSepIn A X Y Z → CondIndep (b.ancProd A) X Y Z by
    have hc := key _ A rfl hA (X \ Z) (Y \ Z) Z (sdiff_subset.trans hX) (sdiff_subset.trans hY)
      hZ disjoint_sdiff_self_left disjoint_sdiff_self_left
      (b.dSepIn_mono subset_rfl subset_rfl (fun _ _ h => h) sdiff_subset sdiff_subset h)
    intro x'
    have e1 : X \ Z ∪ Y \ Z ∪ Z = X ∪ Y ∪ Z := by
      ext i; simp only [mem_union, mem_sdiff]; tauto
    have := hc x'
    rwa [e1, sdiff_union_self_eq_union, sdiff_union_self_eq_union] at this
  intro m
  induction m with
  | zero =>
    intro A hcard _ X Y Z hX hY hZ _ _ _
    rw [card_eq_zero] at hcard
    subst hcard
    rw [subset_empty] at hX hY hZ
    subst hX hY hZ
    intro x'
    simp
  | succ m ih =>
    intro A hcard hA X Y Z hX hY hZ hXZ hYZ h
    classical
    have hne : A.Nonempty := by rw [← card_pos, hcard]; omega
    have hs : A.max' hne ∈ A := max'_mem A hne
    set s := A.max' hne
    have hch : ∀ j ∈ A, ¬b.Edge s j := fun j hj hE =>
      absurd (le_max' A j hj) (not_le.2 (Fin.lt_def.2 hE.1))
    have hA' : b.IsAncestral (A.erase s) := fun i j hE hj =>
      mem_erase.2 ⟨fun hi => hch j (mem_of_mem_erase hj) (hi ▸ hE), hA hE (mem_of_mem_erase hj)⟩
    have hcard' : (A.erase s).card = m := by rw [card_erase_of_mem hs, hcard]; rfl
    have IH := ih (A.erase s) hcard' hA'
    have hsub : ∀ T ⊆ A, s ∉ T → T ⊆ A.erase s := fun T hT hsT i hi =>
      mem_erase.2 ⟨fun h => hsT (h ▸ hi), hT hi⟩
    have hnn : ∀ x, 0 ≤ b.ancProd A x := fun x => prod_nonneg fun j _ => by
      split_ifs
      · exact (b.cpt j _).nonneg _
      · positivity
    have hss : ¬b.Edge s s := fun hE => lt_irrefl _ hE.1
    set Ps := univ.filter fun i => b.Edge i s ∧ i ∉ Z with hPsdef
    have hPs : ∀ i ∈ Ps, b.Edge i s ∧ i ∉ Z := fun i hi => (mem_filter.1 hi).2
    have hPsA : Ps ⊆ A.erase s := fun i hi => mem_erase.2
      ⟨fun h => hss (h ▸ (hPs i hi).1), hA (hPs i hi).1 hs⟩
    have hsPs : s ∉ Ps := fun h => hss (hPs s h).1
    have hpa : ∀ i, b.Edge i s → i ∈ Ps ∪ Z := fun i hi => by
      by_cases hiZ : i ∈ Z
      · exact mem_union_right _ hiZ
      · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hi, hiZ⟩)
    -- the case of a sink in the first set
    have caseX : ∀ X Y : Finset (Fin n), X ⊆ A → Y ⊆ A → Disjoint X Z → Disjoint Y Z →
        b.DSepIn A X Y Z → s ∈ X → CondIndep (b.ancProd A) X Y Z := by
      intro X Y hX hY hXZ hYZ h hsX
      have hsZ : s ∉ Z := disjoint_left.1 hXZ hsX
      have hsY : s ∉ Y := disjoint_left.1 (b.dSepIn_disjoint hX h) hsX
      have hB : b.DSepIn (A.erase s) (X.erase s ∪ Ps) Y Z :=
        b.dSepIn_erase_of_mem hs hch hsX hPs h
      have hBA : X.erase s ∪ Ps ⊆ A.erase s := union_subset (erase_subset_erase s hX) hPsA
      have hBZ : Disjoint (X.erase s ∪ Ps) Z := disjoint_union_left.2
        ⟨hXZ.mono_left (erase_subset s X), disjoint_left.2 fun i hi hiZ => (hPs i hi).2 hiZ⟩
      have hci := IH _ Y Z hBA (hsub Y hY hsY) (hsub Z hZ hsZ) hBZ hYZ hB
      have hsB : s ∉ X.erase s ∪ Ps := by simp [hsPs]
      have h2 := b.condIndep_ancProd_insert hs hch hsB hsY hsZ (fun i hi => by
        rcases mem_union.1 (hpa i hi) with h' | h'
        · exact mem_union_left _ (mem_union_right _ h')
        · exact mem_union_right _ h') hci
      refine h2.mono_left (fun i hi => ?_)
        (disjoint_insert_left.2 ⟨hsY, b.dSepIn_disjoint hBA hB⟩)
      by_cases his : i = s
      · exact his ▸ mem_insert_self _ _
      · exact mem_insert_of_mem (mem_union_left _ (mem_erase.2 ⟨his, hi⟩))
    by_cases hsX : s ∈ X
    · exact caseX X Y hX hY hXZ hYZ h hsX
    by_cases hsY : s ∈ Y
    · exact (caseX Y X hY hX hYZ hXZ (b.dSepIn_symm h) hsY).symm
    by_cases hsZ : s ∈ Z
    · have caseZ : ∀ X Y : Finset (Fin n), X ⊆ A → Y ⊆ A → s ∉ X → s ∉ Y → Disjoint X Z →
          Disjoint Y Z → b.DSepIn (A.erase s) (X ∪ Ps) Y (Z.erase s) →
          CondIndep (b.ancProd A) X Y Z := by
        intro X Y hX hY hsX hsY hXZ hYZ hd
        have hXPA : X ∪ Ps ⊆ A.erase s := union_subset (hsub X hX hsX) hPsA
        have hXPZ : Disjoint (X ∪ Ps) (Z.erase s) := by
          refine disjoint_left.2 fun i hi hiZ => ?_
          rcases mem_union.1 hi with hi | hi
          · exact disjoint_left.1 hXZ hi (mem_of_mem_erase hiZ)
          · exact (hPs i hi).2 (mem_of_mem_erase hiZ)
        have hci := IH (X ∪ Ps) Y (Z.erase s) hXPA (hsub Y hY hsY) (erase_subset_erase s hZ) hXPZ
          (hYZ.mono_right (erase_subset s Z)) hd
        have hsXP : s ∉ X ∪ Ps := by simp [hsX, hsPs]
        have h2 := b.condIndep_ancProd_insert hs hch hsXP hsY (by simp) (fun i hi => by
          rcases mem_union.1 (hpa i hi) with h' | h'
          · exact mem_union_left _ (mem_union_right _ h')
          · exact mem_union_right _ (mem_erase.2 ⟨fun h => hss (h ▸ hi), h'⟩)) hci
        have hdXY : Disjoint (insert s (X ∪ Ps)) Y :=
          disjoint_insert_left.2 ⟨hsY, b.dSepIn_disjoint hXPA hd⟩
        have hsub' : X ∪ {s} ⊆ insert s (X ∪ Ps) := fun i hi => by
          rcases mem_union.1 hi with hi | hi
          · exact mem_insert_of_mem (mem_union_left _ hi)
          · rw [mem_singleton.1 hi]; exact mem_insert_self _ _
        have h4 := (h2.mono_left hsub' hdXY).weak_union hnn (hdXY.mono_left hsub')
        have hZe : Z.erase s ∪ {s} = Z := by
          ext i
          by_cases his : i = s
          · subst his; simp [hsZ]
          · simp [his]
        rwa [hZe] at h4
      rcases b.dSepIn_erase_of_mem_cond hs hch hsZ (hPsA.trans (erase_subset s A)) hPs h with
        hd | hd
      · exact caseZ X Y hX hY hsX hsY hXZ hYZ hd
      · exact (caseZ Y X hY hX hsY hsX hYZ hXZ (b.dSepIn_symm hd)).symm
    · have hci := IH X Y Z (hsub X hX hsX) (hsub Y hY hsY) (hsub Z hZ hsZ) hXZ hYZ
        (b.dSepIn_mono (erase_subset s A) subset_rfl (fun _ _ h => h) subset_rfl subset_rfl h)
      intro x'
      have h1 : s ∉ X ∪ Y ∪ Z := by simp [hsX, hsY, hsZ]
      have h2 : s ∉ X ∪ Z := by simp [hsX, hsZ]
      have h3 : s ∉ Y ∪ Z := by simp [hsY, hsZ]
      rw [margProb_ancProd_erase b hch h1, margProb_ancProd_erase b hch h2,
        margProb_ancProd_erase b hch h3, margProb_ancProd_erase b hch hsZ]
      exact hci x'

/-- **The global Markov property** (soundness of d-separation: Geiger, Verma & Pearl 1990;
Lauritzen, Dawid, Larsen & Leimer 1990): if `Z` d-separates `X` from `Y` in the graph of a
Bayesian network, then `X` and `Y` are conditionally independent given `Z` under its joint
law. -/
theorem condIndep_of_dSeparated [Fintype α] [DecidableEq α] {X Y Z : Finset (Fin n)}
    (h : b.DSeparated (X : Set (Fin n)) (Y : Set (Fin n)) (Z : Set (Fin n))) :
    CondIndep b.joint X Y Z := by
  have hdesc : ∀ {i j : Fin n}, b.DescIn univ i j → b.IsDescendant i j := by
    intro i j hij
    unfold DescIn at hij
    induction hij with
    | refl => exact .refl
    | tail _ hst ih => exact ih.tail hst.1
  have hd : b.DSepIn univ X Y Z := fun x hx y hy p hp ha => by
    obtain ⟨i, hi, hb⟩ := h x hx y hy p hp
    refine ha.2.2 i hi ?_
    rcases hb with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2, fun d hd hdZ => h3 d (hdesc hd) (mem_coe.2 hdZ)⟩
    · exact Or.inr ⟨h1, mem_coe.1 h2⟩
  rw [← b.ancProd_univ]
  exact b.condIndep_ancProd univ (fun _ _ _ _ => mem_univ _) X Y Z (subset_univ _)
    (subset_univ _) (subset_univ _) hd

end BayesNet

end Cslib.MachineLearning.GraphicalModels
