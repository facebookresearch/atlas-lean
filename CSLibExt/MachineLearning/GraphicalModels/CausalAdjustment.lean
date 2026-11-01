/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.GlobalMarkov
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Back-door and front-door adjustment

Graphical identification of causal effects in a causal Bayesian network (`BayesNet`, nodes in a
topological order, finite state space; the intervention `do(X_k = a)` is `BayesNet.intervene`).
The proofs combine the truncated factorization with the global Markov property
(`BayesNet.condIndep_of_dSeparated`) applied to networks with the arrows into the intervened
nodes removed.

## Main definitions

* `BayesNet.mutilateSet b W w`: the network of the intervention `do(X_W = w)` on a set `W` of
  nodes, with the arrows into `W` removed.

## Main results

* `BayesNet.joint_mutilateSet`: the truncated factorization for a set of nodes.
* `BayesNet.margProb_intervene_of_not_isDescendant`: an intervention does not change the law of the
  non-descendants of the intervened node.
* `BayesNet.backdoor_adjustment`: **the back-door adjustment** (Pearl 1995; Pearl 2009,
  Theorem 3.3.2): if `Z` contains no descendant of `k` and blocks every path from `k` to `y`
  that begins with an arrow into `k`, then
  `P(X_y = v | do(X_k = a)) = ∑_z P(Z = z) P(X_y = v | X_k = a, Z = z)`, assuming
  `P(X_k = a, Z = z) > 0` whenever `P(Z = z) > 0`. The adjustment set may contain nodes after
  `k` in the topological order.
* `BayesNet.frontdoor_adjustment`: **the front-door adjustment** (Pearl 1995; Pearl 2009,
  Theorem 3.3.4): if `M` intercepts every directed path from `k` to `y`, every path from `k` to
  a node of `M` beginning with an arrow into `k` is blocked by `∅`, and every path from a node
  of `M` to `y` beginning with an arrow into that node is blocked by `{k}`, then
  `P(X_y = v | do(X_k = a))` equals
  `∑_m P(M = m | X_k = a) ∑_{a'} P(X_y = v | X_k = a', M = m) P(X_k = a')`, assuming
  `P(X_k = a', M = m) > 0` for all `a'` and `m`.

Both formulas are stated for a single outcome node. The three rules of the do-calculus (Pearl
1995; Pearl 2009, Theorem 3.4.1) are not covered.

## References

* J. Pearl, *Causal diagrams for empirical research*, Biometrika 82(4) (1995), 669–688.
* J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed., Cambridge University Press
  (2009), §3.2–3.3.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset Convexity

variable {α : Type*}

/-- The assignment equal to `t` on `T` and to `x'` elsewhere. -/
private def fill {n : ℕ} (T : Finset (Fin n)) (x' : Fin n → α) (t : T → α) : Fin n → α :=
  fun i => if h : i ∈ T then t ⟨i, h⟩ else x' i

/-- Splitting a sum against `P` by the values `t` of the variables in `T` (disjoint from the
fixed set `S`), for a weight `g` depending only on the variables in `T ∪ S`. -/
private lemma sum_filter_mul_eq_sum_margProb {n : ℕ} [Fintype α] [DecidableEq α]
    (P : (Fin n → α) → ℝ) {S T : Finset (Fin n)} (hTS : Disjoint T S) (x' : Fin n → α)
    (g : (Fin n → α) → ℝ) (hg : ∀ x y, (∀ i ∈ T ∪ S, x i = y i) → g x = g y) :
    ∑ x with ∀ i ∈ S, x i = x' i, P x * g x =
      ∑ t : T → α, g (fill T x' t) * margProb P (T ∪ S) (fill T x' t) := by
  rw [← Finset.sum_fiberwise (univ.filter fun x : Fin n → α => ∀ i ∈ S, x i = x' i)
    (fun x => fun i : T => x i)]
  refine sum_congr rfl fun t _ => ?_
  rw [filter_filter, margProb, mul_sum]
  have hiff : ∀ x : Fin n → α, ((∀ i ∈ S, x i = x' i) ∧ (fun i : T => x i) = t) ↔
      ∀ i ∈ T ∪ S, x i = fill T x' t i := by
    intro x
    constructor
    · rintro ⟨h1, h2⟩ i hi
      by_cases hiT : i ∈ T
      · simp only [fill, hiT, dite_true]
        exact congrFun h2 ⟨i, hiT⟩
      · simp only [fill, hiT, dite_false]
        exact h1 i ((mem_union.1 hi).resolve_left hiT)
    · intro h
      refine ⟨fun i hi => ?_, funext fun i => ?_⟩
      · have hiT : i ∉ T := fun hiT => disjoint_left.1 hTS hiT hi
        rw [h i (mem_union_right _ hi)]
        simp [fill, hiT]
      · rw [h i (mem_union_left _ i.2)]
        simp [fill]
  refine sum_congr (filter_congr fun x _ => hiff x) fun x hx => ?_
  rw [mul_comm, hg x (fill T x' t) (mem_filter.1 hx).2]

namespace BayesNet

variable {n : ℕ} [Nonempty α] (b : BayesNet α n)

/-! ### Interventions on a set of nodes -/

/-- The network of the intervention `do(X_W = w)` with the arrows into `W` removed: every node
`j ∈ W` has no parents and the point mass at `w j` as its table. -/
noncomputable def mutilateSet (W : Finset (Fin n)) (w : Fin n → α) : BayesNet α n where
  pa j := if j ∈ W then ∅ else b.pa j
  cpt j z := if h : j ∈ W then StdSimplex.single (w j) else
    b.cpt j fun i => z ⟨i, by simp [h]⟩

/-- **The truncated factorization for a set of nodes**: after `do(X_W = w)`, the joint is the
product of the tables of the nodes outside `W` on assignments agreeing with `w` on `W`. -/
theorem joint_mutilateSet [DecidableEq α] (W : Finset (Fin n)) (w x : Fin n → α) :
    (b.mutilateSet W w).joint x = ∏ j, if j ∈ W then (if x j = w j then 1 else 0)
      else (b.cpt j (b.paVal j x)).weights (x j) := by
  rw [joint_eq_prod]
  refine prod_congr rfl fun j _ => ?_
  by_cases h : j ∈ W
  · simp only [mutilateSet, h, dite_true, ite_true]
    by_cases hx : x j = w j
    · simp [StdSimplex.single, hx]
    · simp [StdSimplex.single, hx]
  · simp only [mutilateSet, h, dite_false, ite_false]
    rfl

omit [Nonempty α] in
/-- The arrows of `b.mutilateSet W w` are those of `b` not pointing into `W`. -/
theorem edge_mutilateSet_iff (W : Finset (Fin n)) (w : Fin n → α) {i j : Fin n} :
    (b.mutilateSet W w).Edge i j ↔ b.Edge i j ∧ j ∉ W := by
  by_cases h : j ∈ W
  · simp [Edge, mutilateSet, h]
  · simp [Edge, mutilateSet, h]

omit [Nonempty α] in
/-- A descendant after removing the arrows into `W` is a descendant in `b`. -/
theorem IsDescendant.of_mutilateSet {W : Finset (Fin n)} {w : Fin n → α} {i j : Fin n}
    (h : (b.mutilateSet W w).IsDescendant i j) : b.IsDescendant i j := by
  unfold IsDescendant at h ⊢
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail ((b.edge_mutilateSet_iff W w).1 hst).1

omit [Nonempty α] in
/-- After removing the arrows into `W`, a node of `W` is a descendant only of itself. -/
theorem eq_of_isDescendant_mutilateSet {W : Finset (Fin n)} {w : Fin n → α} {i j : Fin n}
    (h : (b.mutilateSet W w).IsDescendant i j) (hj : j ∈ W) : i = j := by
  unfold IsDescendant at h
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, -, hc⟩
  · exact h.symm
  · exact absurd hj ((b.edge_mutilateSet_iff W w).1 hc).2

/-- Two networks whose tables agree on an ancestral set (for both graphs) have the same law on
that set. -/
private lemma margProb_eq_of_tables [Fintype α] [DecidableEq α] (b' : BayesNet α n)
    {N : Finset (Fin n)} (hN : b.IsAncestral N) (hN' : b'.IsAncestral N)
    (htab : ∀ j ∈ N, ∀ x, (b.cpt j (b.paVal j x)).weights (x j) =
      (b'.cpt j (b'.paVal j x)).weights (x j))
    {S : Finset (Fin n)} (hS : S ⊆ N) (x' : Fin n → α) :
    margProb b.joint S x' = margProb b'.joint S x' := by
  rw [margProb_joint_eq_ancProd b hN hS, margProb_joint_eq_ancProd b' hN' hS]
  congr 1
  funext x
  refine prod_congr rfl fun j _ => ?_
  split_ifs with hj
  · exact htab j hj x
  · rfl

omit [Nonempty α] in
/-- d-separation in a network with the arrows into `W` removed, from back-door blocking in
`b`: parents of nodes of `W` are d-separated from `Ys` by `C`. -/
private lemma dSeparated_mutilateSet {W C Zb Ys Ps : Finset (Fin n)} (w : Fin n → α)
    (hWC : W ⊆ C) (hZC : Zb ⊆ C) (hCWZ : C ⊆ W ∪ Zb) (hYW : ∀ y ∈ Ys, y ∉ W)
    (hPs : ∀ p ∈ Ps, p ∉ C ∧ ∃ r ∈ W, b.Edge p r ∧ ∀ y ∈ Ys, ∀ l, b.IsPath r y l →
      (∃ h : 1 < l.length, b.Edge l[1] r) → b.PathBlocked (Zb : Set (Fin n)) l) :
    (b.mutilateSet W w).DSeparated (Ps : Set (Fin n)) (Ys : Set (Fin n)) (C : Set (Fin n)) := by
  intro p hp y hy π hπ
  rw [mem_coe] at hp hy
  obtain ⟨hpC, r, hrW, hpr, hbl⟩ := hPs p hp
  obtain ⟨hnd, hch, hh, hl⟩ := hπ
  cases π with
  | nil => simp at hh
  | cons q rest =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    by_cases hmeet : ∃ c ∈ q :: rest, c ∈ W
    · obtain ⟨c, hc, hcW⟩ := hmeet
      obtain ⟨t, ht, htc⟩ := List.mem_iff_getElem.1 hc
      cases t with
      | zero =>
        simp only [List.getElem_cons_zero] at htc
        subst htc
        exact absurd (hWC hcW) hpC
      | succ t =>
        have hlast : t + 1 ≠ (q :: rest).length - 1 := by
          intro h
          rw [List.getLast?_eq_getElem?] at hl
          simp only [← h, List.getElem?_eq_getElem ht, Option.some.injEq] at hl
          exact hYW y hy (hl ▸ htc ▸ hcW)
        refine ⟨t, by omega, Or.inr ⟨fun hc' => ?_, ?_⟩⟩
        · exact ((b.edge_mutilateSet_iff W w).1 hc'.1).2 (htc ▸ hcW)
        · rw [mem_coe]
          exact hWC (htc ▸ hcW)
    · simp only [not_exists, not_and] at hmeet
      have hrπ : r ∉ q :: rest := fun h => hmeet r h hrW
      have hpath : b.IsPath r y (r :: q :: rest) := by
        refine ⟨List.nodup_cons.2 ⟨hrπ, hnd⟩, List.IsChain.cons_cons (Or.inr hpr) ?_, rfl, ?_⟩
        · exact hch.imp fun u v huv => huv.imp
            (fun h => ((b.edge_mutilateSet_iff W w).1 h).1)
            (fun h => ((b.edge_mutilateSet_iff W w).1 h).1)
        · simpa using hl
      obtain ⟨i, hi, hb⟩ := hbl y hy _ hpath ⟨by simp, hpr⟩
      cases i with
      | zero =>
        rcases hb with ⟨h1, -, -⟩ | ⟨-, h2⟩
        · exact absurd (h1.1.trans hpr.1) (lt_irrefl _)
        · exact (hpC (hZC (mem_coe.1 h2))).elim
      | succ i =>
        simp only [List.getElem_cons_succ] at hb
        have hm : (q :: rest)[i + 1]'(by simp at hi ⊢; omega) ∉ W :=
          hmeet _ (List.getElem_mem _)
        refine ⟨i, by simp at hi ⊢; omega, ?_⟩
        rcases hb with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
        · refine Or.inl ⟨(b.edge_mutilateSet_iff W w).2 ⟨h1, hm⟩,
            (b.edge_mutilateSet_iff W w).2 ⟨h2, hm⟩, fun d hd hdC => ?_⟩
          rcases mem_union.1 (hCWZ (mem_coe.1 hdC)) with hdW | hdZ
          · exact hm (b.eq_of_isDescendant_mutilateSet hd hdW ▸ hdW)
          · exact h3 d (hd.of_mutilateSet b) (mem_coe.2 hdZ)
        · refine Or.inr ⟨fun hc => h1 ⟨((b.edge_mutilateSet_iff W w).1 hc.1).1,
            ((b.edge_mutilateSet_iff W w).1 hc.2).1⟩, ?_⟩
          rw [mem_coe] at h2 ⊢
          exact hZC h2

omit [Nonempty α] in
/-- Reweighting: if `L = L' · h` on the assignments fixing `C`, with `h` a function of the
variables in `T ∪ C` and `T ⫫ Ys | C` under `L'`, then
`L(Ys, C) L'(C) = L(C) L'(Ys, C)`. -/
private lemma margProb_reweight [Fintype α] [DecidableEq α] {L L' : (Fin n → α) → ℝ}
    {T Ys C : Finset (Fin n)} (hTY : Disjoint T Ys) (hTC : Disjoint T C) (xb : Fin n → α)
    (h : (Fin n → α) → ℝ) (hh : ∀ x y, (∀ i ∈ T ∪ C, x i = y i) → h x = h y)
    (hL : ∀ x, (∀ i ∈ C, x i = xb i) → L x = L' x * h x) (hci : CondIndep L' T Ys C) :
    margProb L (Ys ∪ C) xb * margProb L' C xb = margProb L C xb * margProb L' (Ys ∪ C) xb := by
  have e : ∀ S, C ⊆ S → Disjoint T S →
      margProb L S xb = ∑ t : T → α, h (fill T xb t) * margProb L' (T ∪ S) (fill T xb t) := by
    intro S hCS hTS
    rw [← sum_filter_mul_eq_sum_margProb L' hTS xb h fun x y hxy => hh x y fun i hi => hxy i
      (by rcases mem_union.1 hi with hi | hi
          · exact mem_union_left _ hi
          · exact mem_union_right _ (hCS hi))]
    unfold margProb
    exact sum_congr rfl fun x hx => hL x fun i hi => (mem_filter.1 hx).2 i (hCS hi)
  have agree : ∀ S, Disjoint T S → ∀ t, margProb L' S (fill T xb t) = margProb L' S xb :=
    fun S hS t => margProb_congr L' S fun i hi => by
      have hi' : i ∉ T := fun h => disjoint_left.1 hS h hi
      simp [fill, hi']
  have hTYC : Disjoint T (Ys ∪ C) := disjoint_union_right.2 ⟨hTY, hTC⟩
  rw [e (Ys ∪ C) subset_union_right hTYC, e C subset_rfl hTC, sum_mul, sum_mul]
  refine sum_congr rfl fun t _ => ?_
  have := hci (fill T xb t)
  rw [agree C hTC t, agree (Ys ∪ C) hTYC t, union_assoc] at this
  rw [mul_assoc, this, mul_assoc]

omit [Nonempty α] in
private lemma exists_isChain_of_reflTransGen {r : Fin n → Fin n → Prop} {a c : Fin n}
    (h : Relation.ReflTransGen r a c) :
    ∃ l : List (Fin n), (a :: l).IsChain r ∧ (a :: l).getLast? = some c ∧
      ∀ x ∈ l, ∃ u, r u x := by
  induction h with
  | refl => exact ⟨[], .singleton _, rfl, fun x hx => by cases hx⟩
  | @tail b' c' _ hbc ih =>
    obtain ⟨l, h1, h2, h3⟩ := ih
    refine ⟨l ++ [c'], ?_, ?_, ?_⟩
    · rw [← List.cons_append]
      refine h1.append (.singleton _) fun x hx y hy => ?_
      rw [h2] at hx
      simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at hx hy
      subst hx hy
      exact hbc
    · rw [show a :: (l ++ [c']) = (a :: l) ++ [c'] from rfl, List.getLast?_append]
      simp
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact h3 x hx
      · rw [List.mem_singleton] at hx
        exact ⟨b', hx ▸ hbc⟩

omit [Nonempty α] in
/-- If every directed path from `k` to `y` meets `M`, then `y` is not a descendant of `k` once
the arrows into `M` are removed. -/
private lemma not_isDescendant_mutilateSet {k y : Fin n} {M : Finset (Fin n)} (w : Fin n → α)
    (hkM : k ∉ M)
    (hdir : ∀ p : List (Fin n), p.IsChain b.Edge → p.head? = some k → p.getLast? = some y →
      ∃ m ∈ M, m ∈ p) :
    ¬(b.mutilateSet M w).IsDescendant k y := by
  intro h
  obtain ⟨l, h1, h2, h3⟩ := exists_isChain_of_reflTransGen h
  obtain ⟨m, hm, hml⟩ :=
    hdir (k :: l) (h1.imp fun u v huv => ((b.edge_mutilateSet_iff M w).1 huv).1) rfl h2
  rcases List.mem_cons.1 hml with rfl | hml
  · exact hkM hm
  · obtain ⟨u, hu⟩ := h3 m hml
    exact ((b.edge_mutilateSet_iff M w).1 hu).2 hm

omit [Nonempty α] in
/-- If every path from `k` to `m` beginning with an arrow into `k` is blocked by `∅`, then `k` is
not a descendant of `m`. -/
private lemma not_isDescendant_of_blocked {k m : Fin n} (hkm' : m ≠ k)
    (hkm : ∀ p, b.IsPath k m p → (∃ h : 1 < p.length, b.Edge p[1] k) → b.PathBlocked ∅ p) :
    ¬b.IsDescendant m k := by
  intro h
  obtain ⟨l, h1, h2, -⟩ := exists_isChain_of_reflTransGen h
  have hlt : (m :: l).IsChain (· < ·) := h1.imp fun u v huv => Fin.lt_def.2 huv.1
  have hnd : (m :: l).Nodup := (List.isChain_iff_pairwise.1 hlt).imp ne_of_lt
  have hq : (m :: l).reverse.IsChain fun u v => b.Edge v u := List.isChain_reverse.2 h1
  have hl : l ≠ [] := by
    rintro rfl
    simp only [List.getLast?_singleton, Option.some.injEq] at h2
    exact hkm' h2
  have hlen : 1 < (m :: l).reverse.length := by
    simp only [List.length_reverse, List.length_cons]
    have := List.length_pos_of_ne_nil hl
    omega
  have hhead : (m :: l).reverse.head? = some k := by rw [List.head?_reverse]; exact h2
  have h0 : (m :: l).reverse[0]'(by omega) = k := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hhead
    exact Option.some.inj hhead
  have hpath : b.IsPath k m (m :: l).reverse :=
    ⟨List.nodup_reverse.2 hnd, hq.imp fun u v huv => Or.inr huv, hhead,
      by rw [List.getLast?_reverse]; rfl⟩
  have he : b.Edge (m :: l).reverse[1] k := by
    have := List.isChain_iff_getElem.1 hq 0 hlen
    simpa only [h0] using this
  obtain ⟨i, hi, hb⟩ := hkm _ hpath ⟨hlen, he⟩
  rcases hb with ⟨h1', -, -⟩ | ⟨-, h2'⟩
  · have := List.isChain_iff_getElem.1 hq i (by omega)
    exact absurd (h1'.1.trans this.1) (lt_irrefl _)
  · exact h2'

/-- Relating two interventions `do(X_W = w)` and `do(X_{W'} = w)` for `W ⊆ W'` on assignments
agreeing with `w` on `W'`: the larger one drops the tables of `W' \ W`. -/
private lemma joint_mutilateSet_mul {W W' : Finset (Fin n)} (hWW' : W ⊆ W')
    (w : Fin n → α) {x : Fin n → α} (hx : ∀ j ∈ W', x j = w j) :
    (b.mutilateSet W w).joint x = (b.mutilateSet W' w).joint x *
      ∏ j ∈ W' \ W, (b.cpt j (b.paVal j x)).weights (x j) := by
  classical
  rw [joint_mutilateSet, joint_mutilateSet, ← univ_inter (W' \ W), ← prod_ite_mem univ (W' \ W),
    ← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  by_cases hj : j ∈ W
  · simp [hj, hWW' hj, hx j (hWW' hj)]
  · by_cases hj' : j ∈ W'
    · simp [hj, hj', hx j hj']
    · simp [hj, hj']

/-- Without intervened nodes, the joint is that of `b`. -/
private lemma joint_mutilateSet_empty (w : Fin n → α) :
    (b.mutilateSet ∅ w).joint = b.joint := by
  classical
  funext x
  rw [joint_mutilateSet, joint_eq_prod]
  simp only [notMem_empty, ite_false]
  rfl

/-- `do(X_k = a)` as an intervention on the set `{k}`. -/
private lemma joint_mutilateSet_singleton {k : Fin n} {w : Fin n → α} {a : α}
    (hw : w k = a) : (b.mutilateSet {k} w).joint = (b.intervene k a).joint := by
  classical
  funext x
  rw [joint_mutilateSet, joint_intervene, ← mul_prod_erase univ _ (mem_univ k)]
  have hrest : ∏ j ∈ univ.erase k, (if j ∈ ({k} : Finset (Fin n)) then
      (if x j = w j then (1 : ℝ) else 0) else (b.cpt j (b.paVal j x)).weights (x j)) =
      ∏ j ∈ univ.erase k, (b.cpt j (b.paVal j x)).weights (x j) :=
    prod_congr rfl fun j hj => by simp [ne_of_mem_erase hj]
  rw [hrest, hw]
  by_cases hx : x k = a <;> simp [hx]

/-- After `do(X_W = w)`, fixing in addition the nodes of `W` at their values `w` does not change
the probability. -/
private lemma margProb_mutilateSet_union [Fintype α] [DecidableEq α] (W : Finset (Fin n))
    (w : Fin n → α) (S : Finset (Fin n)) {x' : Fin n → α} (hx' : ∀ j ∈ W, x' j = w j) :
    margProb (b.mutilateSet W w).joint (S ∪ W) x' = margProb (b.mutilateSet W w).joint S x' := by
  unfold margProb
  symm
  rw [← sum_filter_of_ne (p := fun x => ∀ j ∈ W, x j = w j), filter_filter]
  · refine sum_congr (filter_congr fun x _ => ?_) fun _ _ => rfl
    simp only [mem_union]
    constructor
    · rintro ⟨h1, h2⟩ i (hi | hi)
      · exact h1 i hi
      · exact (h2 i hi).trans (hx' i hi).symm
    · intro h
      exact ⟨fun i hi => h i (Or.inl hi), fun j hj => (h j (Or.inr hj)).trans (hx' j hj)⟩
  · intro x _ hx j hj
    by_contra hne
    apply hx
    rw [joint_mutilateSet]
    exact prod_eq_zero (mem_univ j) (by simp [hj, hne])

/-- The joint of `do(X_W = w)` is a probability distribution concentrated on `W = w`. -/
private lemma margProb_mutilateSet_self [Fintype α] [DecidableEq α] (W : Finset (Fin n))
    (w : Fin n → α) {x' : Fin n → α} (hx' : ∀ j ∈ W, x' j = w j) :
    margProb (b.mutilateSet W w).joint W x' = 1 := by
  have := b.margProb_mutilateSet_union W w ∅ hx'
  rw [empty_union] at this
  rw [this]
  unfold margProb
  simp only [notMem_empty, IsEmpty.forall_iff, implies_true, filter_true_of_mem]
  exact (b.mutilateSet W w).sum_joint

/-! ### Interventions on one node -/

/-- After `do(X_k = a)`, assignments with `x k ≠ a` have probability `0`. -/
theorem joint_intervene_eq_zero {k : Fin n} {a : α} {x : Fin n → α}
    (hx : x k ≠ a) : (b.intervene k a).joint x = 0 := by
  classical
  rw [joint_intervene, ite_eq_right hx]

/-- For `x k = a`, `P(x) = P(x | do(X_k = a)) · p_k(a | x_{pa k})`. -/
theorem joint_eq_intervene_mul_cpt {k : Fin n} {a : α} {x : Fin n → α}
    (hx : x k = a) :
    b.joint x = (b.intervene k a).joint x * (b.cpt k (b.paVal k x)).weights a := by
  classical
  rw [joint_intervene, ite_eq_left hx, joint_eq_prod, ← Finset.mul_prod_erase _ _ (mem_univ k),
    mul_comm, hx]
  rfl

/-- **The intervention `do(X_k = a)` does not change the law of the non-descendants of `k`.** -/
theorem margProb_intervene_of_not_isDescendant [Fintype α] [DecidableEq α] (k : Fin n) (a : α)
    {S : Finset (Fin n)} (hS : ∀ i ∈ S, ¬b.IsDescendant k i) (x' : Fin n → α) :
    margProb (b.intervene k a).joint S x' = margProb b.joint S x' := by
  classical
  set N := univ.filter fun j => ¬b.IsDescendant k j
  have hN : b.IsAncestral N := by
    intro i j hE hj
    simp only [N, mem_filter, mem_univ, true_and] at hj ⊢
    exact fun hi => hj (Relation.ReflTransGen.tail hi hE)
  refine margProb_eq_of_tables (b.intervene k a) b hN hN (fun j hj x => ?_)
    (fun i hi => mem_filter.2 ⟨mem_univ _, hS i hi⟩) x'
  have hjk : j ≠ k := fun h => (mem_filter.1 hj).2 (h ▸ .refl)
  simp [intervene, hjk]
  rfl

/-- **The back-door adjustment** (Pearl 1995; Pearl 2009, Theorem 3.3.2): if the
set `Z` contains no descendant of the treatment node `k` and blocks every path between `k` and
the outcome node `y` that begins with an arrow into `k`, then
`P(X_y = v | do(X_k = a)) = ∑_z P(Z = z) P(X_y = v | X_k = a, Z = z)`, assuming
`P(X_k = a, Z = z) > 0` whenever `P(Z = z) > 0`. -/
theorem backdoor_adjustment [Fintype α] [DecidableEq α] (k y : Fin n) (Z : Finset (Fin n))
    (a v : α) (hky : k ≠ y) (hyZ : y ∉ Z) (hdesc : ∀ z ∈ Z, ¬b.IsDescendant k z)
    (hblock : ∀ p, b.IsPath k y p → (∃ h : 1 < p.length, b.Edge p[1] k) →
      b.PathBlocked (Z : Set (Fin n)) p)
    (hpos : ∀ z : Z → α, ∑ x with (fun i : Z => x i) = z, b.joint x ≠ 0 →
      ∑ x with x k = a ∧ (fun i : Z => x i) = z, b.joint x ≠ 0) :
    ∑ x with x y = v, (b.intervene k a).joint x =
      ∑ z : Z → α, (∑ x with (fun i : Z => x i) = z, b.joint x) *
        ((∑ x with x k = a ∧ x y = v ∧ (fun i : Z => x i) = z, b.joint x) /
          ∑ x with x k = a ∧ (fun i : Z => x i) = z, b.joint x) := by
  classical
  set P := b.joint
  set Q := (b.intervene k a).joint
  have hQ0 : ∀ x, 0 ≤ Q x := fun x => (b.intervene k a).toChain.joint_nonneg n x
  have hkZ : k ∉ Z := fun h => hdesc k h .refl
  set Pk := univ.filter fun i => b.Edge i k ∧ i ∉ Z with hPkdef
  have hPk : ∀ i ∈ Pk, b.Edge i k ∧ i ∉ Z := fun i hi => (mem_filter.1 hi).2
  have hyPk : y ∉ Pk := by
    intro hy
    obtain ⟨i, hi, hb⟩ : b.PathBlocked (Z : Set (Fin n)) [k, y] :=
      hblock [k, y] ⟨by simp [hky], List.IsChain.cons_cons (Or.inr (hPk y hy).1) (.singleton _),
        rfl, rfl⟩ ⟨by simp, (hPk y hy).1⟩
    simp at hi
  have hPkC : Disjoint Pk (insert k Z) := disjoint_left.2 fun p hp hpC => by
    rcases mem_insert.1 hpC with h | h
    · exact lt_irrefl _ (h ▸ (hPk p hp).1).1
    · exact (hPk p hp).2 h
  -- conditional independence once the arrows into `k` are removed
  have hJ : (b.mutilateSet {k} fun _ => a).joint = Q := b.joint_mutilateSet_singleton rfl
  have hci : CondIndep Q Pk {y} (insert k Z) := by
    have := (b.mutilateSet {k} fun _ => a).condIndep_of_dSeparated
      (b.dSeparated_mutilateSet (fun _ => a) (W := {k}) (C := insert k Z) (Zb := Z) (Ys := {y})
        (Ps := Pk) (singleton_subset_iff.2 (mem_insert_self _ _)) (subset_insert _ _)
        (insert_eq k Z).subset
        (fun y' hy' h => hky ((mem_singleton.1 h).symm.trans (mem_singleton.1 hy')))
        fun p hp => ⟨disjoint_left.1 hPkC hp, k, mem_singleton_self k, (hPk p hp).1,
          fun y' hy' l hl hE => by rw [mem_singleton] at hy'; subst hy'; exact hblock l hl hE⟩)
    rwa [hJ] at this
  -- sum over the values of `Z`
  rw [← Finset.sum_fiberwise (univ.filter fun x : Fin n → α => x y = v)
    (fun x => fun i : Z => x i)]
  refine sum_congr rfl fun z _ => ?_
  rw [filter_filter]
  obtain ⟨a₀⟩ := (inferInstance : Nonempty α)
  set xb : Fin n → α := fill Z (Function.update (Function.update (fun _ => a₀) y v) k a) z
    with hxb
  have hxk : xb k = a := by simp [hxb, fill, hkZ]
  have hxy : xb y = v := by simp [hxb, fill, hyZ, Ne.symm hky]
  have hres : ∀ x : Fin n → α, (fun i : Z => x i) = z ↔ ∀ i ∈ Z, x i = xb i := by
    intro x
    constructor
    · rintro h i hi
      have := congrFun h ⟨i, hi⟩
      simp only at this
      rw [this]
      simp [hxb, fill, hi]
    · intro h
      funext i
      rw [h i i.2]
      simp [hxb, fill]
  have c1 : ∑ x with x y = v ∧ (fun i : Z => x i) = z, Q x = margProb Q (insert y Z) xb := by
    unfold margProb
    refine sum_congr (filter_congr fun x _ => ?_) fun _ _ => rfl
    rw [forall_mem_insert, hxy, hres]
  have c2 : ∑ x with (fun i : Z => x i) = z, P x = margProb P Z xb := by
    unfold margProb
    exact sum_congr (filter_congr fun x _ => hres x) fun _ _ => rfl
  have c3 : ∑ x with x k = a ∧ x y = v ∧ (fun i : Z => x i) = z, P x =
      margProb P (insert k (insert y Z)) xb := by
    unfold margProb
    refine sum_congr (filter_congr fun x _ => ?_) fun _ _ => rfl
    rw [forall_mem_insert, forall_mem_insert, hxk, hxy, hres]
  have c4 : ∑ x with x k = a ∧ (fun i : Z => x i) = z, P x = margProb P (insert k Z) xb := by
    unfold margProb
    refine sum_congr (filter_congr fun x _ => ?_) fun _ _ => rfl
    rw [forall_mem_insert, hxk, hres]
  have hpos' : margProb P Z xb ≠ 0 → margProb P (insert k Z) xb ≠ 0 := by
    rw [← c2, ← c4]; exact hpos z
  rw [c1, c2, c3, c4]
  -- reweighting by the table of `k`
  have hkey := margProb_reweight (L := P) (L' := Q) (disjoint_singleton_right.2 hyPk) hPkC xb
    (fun x => (b.cpt k (b.paVal k x)).weights a)
    (fun x x' hxx' => by
      rw [show b.paVal k x = b.paVal k x' from funext fun j => hxx' _ ?_]
      by_cases hj : Fin.castLE k.2.le j ∈ Z
      · exact mem_union_right _ (mem_insert_of_mem hj)
      · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, ⟨by simp, by simp⟩, hj⟩))
    (fun x hx => b.joint_eq_intervene_mul_cpt ((hx k (mem_insert_self k Z)).trans hxk)) hci
  have hxk' : ∀ j ∈ ({k} : Finset (Fin n)), xb j = a := fun j hj => by
    rw [mem_singleton] at hj; rw [hj, hxk]
  have hQZ : margProb Q (insert k Z) xb = margProb Q Z xb := by
    rw [← hJ, insert_eq, union_comm]
    exact b.margProb_mutilateSet_union {k} _ Z hxk'
  have hQyZ : margProb Q ({y} ∪ insert k Z) xb = margProb Q (insert y Z) xb := by
    rw [← hJ, show ({y} : Finset (Fin n)) ∪ insert k Z = insert y Z ∪ {k} by
      ext i; simp only [mem_union, mem_insert, mem_singleton]; tauto]
    exact b.margProb_mutilateSet_union {k} _ _ hxk'
  have hPyZ : margProb P ({y} ∪ insert k Z) xb = margProb P (insert k (insert y Z)) xb := by
    congr 1
    ext i; simp only [mem_union, mem_insert, mem_singleton]; tauto
  -- the law of `Z` is unchanged by the intervention
  have hZ : margProb Q Z xb = margProb P Z xb :=
    b.margProb_intervene_of_not_isDescendant k a (fun i hi => hdesc i hi) xb
  rw [hQZ, hQyZ, hPyZ, hZ] at hkey
  by_cases hP0 : margProb P Z xb = 0
  · have hA : margProb Q (insert y Z) xb = 0 := le_antisymm
      (hP0 ▸ hZ ▸ margProb_le_of_subset hQ0 (subset_insert y Z) xb) (margProb_nonneg hQ0 _ _)
    rw [hA, hP0, zero_mul]
  · have hD0 := hpos' hP0
    field_simp
    linarith [hkey]

/-- **The front-door adjustment** (Pearl 1995; Pearl 2009, Theorem 3.3.4): if the
set `M` intercepts every directed path from the treatment node `k` to the outcome node `y`, no
path from `k` to a node of `M` that begins with an arrow into `k` is open (blocked by `∅`), and
every path from a node of `M` to `y` that begins with an arrow into that node is blocked by
`{k}`, then
`P(X_y = v | do(X_k = a)) = ∑_m P(M = m | X_k = a) ∑_{a'} P(X_y = v | X_k = a', M = m) P(X_k = a')`,
assuming `P(X_k = a', M = m) > 0` for all `a'` and `m`. -/
theorem frontdoor_adjustment [Fintype α] [DecidableEq α] (k y : Fin n) (M : Finset (Fin n))
    (a v : α) (hky : k ≠ y) (hkM : k ∉ M) (hyM : y ∉ M)
    (hdir : ∀ p : List (Fin n), p.IsChain b.Edge → p.head? = some k → p.getLast? = some y →
      ∃ m ∈ M, m ∈ p)
    (hkm : ∀ m ∈ M, ∀ p, b.IsPath k m p → (∃ h : 1 < p.length, b.Edge p[1] k) →
      b.PathBlocked ∅ p)
    (hmy : ∀ m ∈ M, ∀ p, b.IsPath m y p → (∃ h : 1 < p.length, b.Edge p[1] m) →
      b.PathBlocked {k} p)
    (hpos : ∀ (a' : α) (m : M → α), ∑ x with x k = a' ∧ (fun i : M => x i) = m, b.joint x ≠ 0) :
    ∑ x with x y = v, (b.intervene k a).joint x =
      ∑ m : M → α,
        ((∑ x with x k = a ∧ (fun i : M => x i) = m, b.joint x) /
            ∑ x with x k = a, b.joint x) *
          ∑ a' : α,
            ((∑ x with x k = a' ∧ x y = v ∧ (fun i : M => x i) = m, b.joint x) /
                ∑ x with x k = a' ∧ (fun i : M => x i) = m, b.joint x) *
              ∑ x with x k = a', b.joint x := by
  classical
  set P := b.joint with hPdef
  set Q := (b.intervene k a).joint with hQdef
  have hP0 : ∀ x, 0 ≤ P x := fun x => b.toChain.joint_nonneg n x
  obtain ⟨a₀⟩ := (inferInstance : Nonempty α)
  set Pk := univ.filter fun i => b.Edge i k with hPkdef
  set PaM := univ.filter fun i => i ∉ M ∧ i ≠ k ∧ ∃ j ∈ M, b.Edge i j with hPaMdef
  have hPkM : Disjoint Pk M := disjoint_left.2 fun p hp hpM => by
    have hE := (mem_filter.1 hp).2
    have hkp : k ≠ p := fun h => hkM (h ▸ hpM)
    obtain ⟨i, hi, -⟩ := hkm p hpM [k, p] ⟨by simp [hkp],
      List.IsChain.cons_cons (Or.inr hE) (.singleton _), rfl, rfl⟩ ⟨by simp, hE⟩
    simp at hi
  have hPkk : Disjoint Pk {k} := disjoint_singleton_right.2 fun h =>
    lt_irrefl _ (mem_filter.1 h).2.1
  have hyPaM : y ∉ PaM := by
    intro hy
    obtain ⟨-, -, m0, hm0, hE⟩ := (mem_filter.1 hy).2
    have hm0y : m0 ≠ y := fun h => hyM (h ▸ hm0)
    obtain ⟨i, hi, -⟩ := hmy m0 hm0 [m0, y] ⟨by simp [hm0y],
      List.IsChain.cons_cons (Or.inr hE) (.singleton _), rfl, rfl⟩ ⟨by simp, hE⟩
    simp at hi
  have hPaMC : Disjoint PaM (insert k M) := disjoint_left.2 fun p hp hpC => by
    obtain ⟨h1, h2, -⟩ := (mem_filter.1 hp).2
    rcases mem_insert.1 hpC with h | h
    · exact h2 h
    · exact h1 h
  have hPaMy : Disjoint PaM {y} := disjoint_singleton_right.2 hyPaM
  have hPaMs : ∀ (W : Finset (Fin n)), M ⊆ W → ∀ p ∈ PaM, p ∉ insert k M ∧ ∃ r ∈ W,
      b.Edge p r ∧ ∀ y' ∈ ({y} : Finset (Fin n)), ∀ l, b.IsPath r y' l →
        (∃ h : 1 < l.length, b.Edge l[1] r) →
          b.PathBlocked (({k} : Finset (Fin n)) : Set (Fin n)) l := by
    intro W hMW p hp
    obtain ⟨h1, h2, m0, hm0, hE⟩ := (mem_filter.1 hp).2
    refine ⟨by simp [h1, h2], m0, hMW hm0, hE, fun y' hy' l hl hb => ?_⟩
    rw [mem_singleton] at hy'
    subst hy'
    rw [coe_singleton]
    exact hmy m0 hm0 l hl hb
  -- the weight of the tables of `M`, a function of the variables in `PaM ∪ insert k M`
  set hM : (Fin n → α) → ℝ := fun x => ∏ j ∈ M, (b.cpt j (b.paVal j x)).weights (x j)
  have hhM : ∀ x x' : Fin n → α, (∀ i ∈ PaM ∪ insert k M, x i = x' i) → hM x = hM x' := by
    intro x x' hxx'
    refine prod_congr rfl fun j hj => ?_
    have hpa : b.paVal j x = b.paVal j x' := by
      funext i
      apply hxx'
      by_cases hiM : Fin.castLE j.2.le i ∈ M
      · exact mem_union_right _ (mem_insert_of_mem hiM)
      by_cases hik : Fin.castLE j.2.le i = k
      · exact mem_union_right _ (hik ▸ mem_insert_self _ _)
      · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hiM, hik, j, hj,
          ⟨by simp, by simp⟩⟩)
    rw [hpa, hxx' j (mem_union_right _ (mem_insert_of_mem hj))]
  have hsd : insert k M \ {k} = M := by
    ext i
    simp only [mem_sdiff, mem_insert, mem_singleton]
    constructor
    · rintro ⟨h | h, h'⟩
      · exact absurd h h'
      · exact h
    · intro h
      exact ⟨Or.inr h, fun h' => hkM (h' ▸ h)⟩
  -- sum over the values of `M`
  rw [← Finset.sum_fiberwise (univ.filter fun x : Fin n → α => x y = v)
    (fun x => fun i : M => x i)]
  refine sum_congr rfl fun m _ => ?_
  rw [filter_filter]
  set xb : Fin n → α := fill M (Function.update (Function.update (fun _ => a₀) y v) k a) m
    with hxb
  have hxk : xb k = a := by simp [hxb, fill, hkM]
  have hxy : xb y = v := by simp [hxb, fill, hyM, Ne.symm hky]
  have hxa : Function.update xb k a = xb := by rw [← hxk, Function.update_eq_self]
  have hres : ∀ x : Fin n → α, (fun i : M => x i) = m ↔ ∀ i ∈ M, x i = xb i := by
    intro x
    constructor
    · rintro h i hi
      have := congrFun h ⟨i, hi⟩
      simp only at this
      rw [this]
      simp [hxb, fill, hi]
    · intro h
      funext i
      rw [h i i.2]
      simp [hxb, fill]
  have hxaM : ∀ a', ∀ i ∈ M, Function.update xb k a' i = xb i := fun a' i hi =>
    Function.update_of_ne (fun h => hkM (by rw [← h]; exact hi)) _ _
  have hresa : ∀ a' (x : Fin n → α), (fun i : M => x i) = m ↔
      ∀ i ∈ M, x i = Function.update xb k a' i := by
    intro a' x
    rw [hres]
    exact forall₂_congr fun i hi => by rw [hxaM a' i hi]
  have c1 : ∑ x with x y = v ∧ (fun i : M => x i) = m, Q x = margProb Q (insert y M) xb := by
    unfold margProb
    refine sum_congr (filter_congr fun x _ => ?_) fun _ _ => rfl
    rw [forall_mem_insert, hxy, hres]
  have c2 : ∀ a', ∑ x with x k = a' ∧ (fun i : M => x i) = m, P x =
      margProb P (insert k M) (Function.update xb k a') := by
    intro a'
    unfold margProb
    refine sum_congr (filter_congr fun x _ => ?_) fun _ _ => rfl
    rw [forall_mem_insert, Function.update_self, hresa a']
  have c3 : ∀ a', ∑ x with x k = a', P x = margProb P {k} (Function.update xb k a') := by
    intro a'
    unfold margProb
    refine sum_congr (filter_congr fun x _ => ?_) fun _ _ => rfl
    simp
  have c4 : ∀ a', ∑ x with x k = a' ∧ x y = v ∧ (fun i : M => x i) = m, P x =
      margProb P (insert k (insert y M)) (Function.update xb k a') := by
    intro a'
    unfold margProb
    refine sum_congr (filter_congr fun x _ => ?_) fun _ _ => rfl
    rw [forall_mem_insert, forall_mem_insert, Function.update_self,
      Function.update_of_ne (Ne.symm hky), hxy, hresa a']
  rw [c1, c2 a, c3 a, hxa]
  rw [sum_congr rfl fun a' _ => by rw [c4 a', c2 a', c3 a']]
  -- step B: `P(M = m | do(a)) = P(M = m | a)`
  have hJ1 : (b.mutilateSet {k} xb).joint = Q := b.joint_mutilateSet_singleton hxk
  have hciB : CondIndep Q Pk M {k} := by
    have := (b.mutilateSet {k} xb).condIndep_of_dSeparated
      (b.dSeparated_mutilateSet xb (W := {k}) (C := {k}) (Zb := ∅) (Ys := M) (Ps := Pk)
        subset_rfl (empty_subset _) (by simp)
        (fun y' hy' h => hkM (by rw [mem_singleton] at h; rwa [h] at hy'))
        fun p hp => ⟨fun h => by
          rw [mem_singleton] at h
          subst h
          exact lt_irrefl _ (mem_filter.1 hp).2.1, k, mem_singleton_self k,
          (mem_filter.1 hp).2, fun y' hy' l hl hE => by rw [coe_empty]; exact hkm y' hy' l hl hE⟩)
    rwa [hJ1] at this
  have hB := margProb_reweight (L := P) (L' := Q) hPkM hPkk xb
    (fun x => (b.cpt k (b.paVal k x)).weights a)
    (fun x x' hxx' => by
      rw [show b.paVal k x = b.paVal k x' from funext fun i => hxx' _
        (mem_union_left _ (mem_filter.2 ⟨mem_univ _, by simp, by simp⟩))])
    (fun x hx => b.joint_eq_intervene_mul_cpt ((hx k (mem_singleton_self k)).trans hxk)) hciB
  have hMk : M ∪ {k} = insert k M := by rw [union_comm, ← insert_eq]
  have hQk : margProb Q {k} xb = 1 := by
    rw [← hJ1]; exact b.margProb_mutilateSet_self {k} xb fun _ _ => rfl
  have hQMk : margProb Q (M ∪ {k}) xb = margProb Q M xb := by
    rw [← hJ1]; exact b.margProb_mutilateSet_union {k} xb M fun _ _ => rfl
  rw [hQk, hQMk, hMk, mul_one] at hB
  -- step C: `P(y | do(a), M = m) = P(y | do(a, M = m))`
  set R' := (b.mutilateSet (insert k M) xb).joint with hR'def
  have hciC : CondIndep R' PaM {y} (insert k M) :=
    (b.mutilateSet (insert k M) xb).condIndep_of_dSeparated
      (b.dSeparated_mutilateSet xb (W := insert k M) (C := insert k M) (Zb := {k}) (Ys := {y})
        (Ps := PaM) subset_rfl (singleton_subset_iff.2 (mem_insert_self _ _)) subset_union_left
        (fun y' hy' => by
          rw [mem_singleton] at hy'
          subst hy'
          simp [Ne.symm hky, hyM])
        (hPaMs (insert k M) (subset_insert _ _)))
  have hC := margProb_reweight (L := Q) (L' := R') hPaMy hPaMC xb hM hhM (fun x hx => by
      rw [← hJ1, b.joint_mutilateSet_mul (singleton_subset_iff.2 (mem_insert_self k M)) xb hx,
        hsd]) hciC
  have hR'1 : margProb R' (insert k M) xb = 1 := b.margProb_mutilateSet_self _ xb fun _ _ => rfl
  have hR'y : margProb R' ({y} ∪ insert k M) xb = margProb R' {y} xb :=
    b.margProb_mutilateSet_union _ xb {y} fun _ _ => rfl
  have hQy : margProb Q ({y} ∪ insert k M) xb = margProb Q (insert y M) xb := by
    rw [← hJ1, show ({y} : Finset (Fin n)) ∪ insert k M = insert y M ∪ {k} by
      ext i; simp only [mem_union, mem_insert, mem_singleton]; tauto]
    exact b.margProb_mutilateSet_union {k} xb _ fun _ _ => rfl
  have hQkM : margProb Q (insert k M) xb = margProb Q M xb := by rw [← hMk, hQMk]
  rw [hR'1, hR'y, hQy, hQkM, mul_one] at hC
  -- step D: `do(a)` has no effect once `M` is fixed
  set R := (b.mutilateSet M xb).joint with hRdef
  have hD : margProb R' {y} xb = margProb R {y} xb := by
    set N := univ.filter fun j => ¬(b.mutilateSet M xb).IsDescendant k j with hNdef
    have hN2 : (b.mutilateSet M xb).IsAncestral N := by
      intro i j hE hj
      simp only [N, mem_filter, mem_univ, true_and] at hj ⊢
      exact fun hi => hj (Relation.ReflTransGen.tail hi hE)
    have hN1 : (b.mutilateSet (insert k M) xb).IsAncestral N := by
      intro i j hE hj
      obtain ⟨hE', hj'⟩ := (b.edge_mutilateSet_iff _ _).1 hE
      exact hN2 ((b.edge_mutilateSet_iff _ _).2 ⟨hE', fun h => hj' (mem_insert_of_mem h)⟩) hj
    refine margProb_eq_of_tables (b.mutilateSet (insert k M) xb) (b.mutilateSet M xb) hN1 hN2
      (fun j hj x => ?_) (singleton_subset_iff.2 (mem_filter.2 ⟨mem_univ _,
        b.not_isDescendant_mutilateSet xb hkM hdir⟩)) xb
    have hjk : j ≠ k := fun h => (mem_filter.1 hj).2 (h ▸ .refl)
    by_cases hjM : j ∈ M
    · simp [mutilateSet, hjM]
    · simp [mutilateSet, hjM, hjk]
      rfl
  -- step E: adjusting for `k` after fixing `M`
  have hciE : CondIndep R PaM {y} (insert k M) :=
    (b.mutilateSet M xb).condIndep_of_dSeparated
      (b.dSeparated_mutilateSet xb (W := M) (C := insert k M) (Zb := {k}) (Ys := {y})
        (Ps := PaM) (subset_insert _ _) (singleton_subset_iff.2 (mem_insert_self _ _))
        (by rw [← hMk])
        (fun y' hy' => by rw [mem_singleton] at hy'; subst hy'; exact hyM)
        (hPaMs M subset_rfl))
  have hkN : ∀ a', margProb R {k} (Function.update xb k a') =
      margProb P {k} (Function.update xb k a') := by
    intro a'
    set N := univ.filter fun j => ∀ m' ∈ M, ¬b.IsDescendant m' j with hNdef
    have hNb : b.IsAncestral N := by
      intro i j hE hj
      simp only [N, mem_filter, mem_univ, true_and] at hj ⊢
      exact fun m' hm' hi => hj m' hm' (Relation.ReflTransGen.tail hi hE)
    have hNM : (b.mutilateSet M xb).IsAncestral N := fun i j hE hj =>
      hNb ((b.edge_mutilateSet_iff _ _).1 hE).1 hj
    refine margProb_eq_of_tables (b.mutilateSet M xb) b hNM hNb (fun j hj x => ?_)
      (singleton_subset_iff.2 (mem_filter.2 ⟨mem_univ _, fun m' hm' =>
        b.not_isDescendant_of_blocked (fun h => hkM (by rw [← h]; exact hm')) (hkm m' hm')⟩)) _
    have hjM : j ∉ M := fun h => (mem_filter.1 hj).2 j h .refl
    simp [mutilateSet, hjM]
    rfl
  have hE : ∀ a', margProb R (insert k {y}) (Function.update xb k a') =
      margProb P (insert k (insert y M)) (Function.update xb k a') /
        margProb P (insert k M) (Function.update xb k a') *
          margProb P {k} (Function.update xb k a') := by
    intro a'
    set xa := Function.update xb k a'
    have hxaM' : ∀ j ∈ M, xa j = xb j := hxaM a'
    have h2 := margProb_reweight (L := P) (L' := R) hPaMy hPaMC xa hM hhM (fun x hx => by
        change b.joint x = _
        rw [← b.joint_mutilateSet_empty xb, b.joint_mutilateSet_mul (empty_subset M) xb
          (fun j hj => (hx j (mem_insert_of_mem hj)).trans (hxaM' j hj)), sdiff_empty]) hciE
    have hRk : margProb R (insert k M) xa = margProb P {k} xa := by
      rw [← hMk, union_comm, ← hkN a']
      exact b.margProb_mutilateSet_union M xb {k} hxaM'
    have hRky : margProb R ({y} ∪ insert k M) xa = margProb R (insert k {y}) xa := by
      rw [show ({y} : Finset (Fin n)) ∪ insert k M = insert k {y} ∪ M by
        ext i; simp only [mem_union, mem_insert, mem_singleton]; tauto]
      exact b.margProb_mutilateSet_union M xb _ hxaM'
    have hPy : margProb P ({y} ∪ insert k M) xa = margProb P (insert k (insert y M)) xa := by
      congr 1
      ext i; simp only [mem_union, mem_insert, mem_singleton]; tauto
    rw [hRk, hRky, hPy] at h2
    have hne : margProb P (insert k M) xa ≠ 0 := by
      have := hpos a' m
      rwa [c2 a'] at this
    field_simp
    linarith [h2]
  have hsumE : margProb R {y} xb = ∑ a' : α, margProb R (insert k {y}) (Function.update xb k a') :=
    margProb_eq_sum_insert R (by simp [hky]) xb
  have hPk0 : margProb P {k} xb ≠ 0 := by
    have h1 := hpos a m
    rw [c2 a, hxa] at h1
    exact (lt_of_lt_of_le (lt_of_le_of_ne (margProb_nonneg hP0 _ _) (Ne.symm h1))
      (margProb_le_of_subset hP0 (singleton_subset_iff.2 (mem_insert_self k M)) xb)).ne'
  rw [hC, hD, hsumE, sum_congr rfl fun a' _ => hE a', hB]
  field_simp

end BayesNet

end Cslib.MachineLearning.GraphicalModels
