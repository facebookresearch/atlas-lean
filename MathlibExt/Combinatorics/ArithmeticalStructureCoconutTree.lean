/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Sum
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Arithmetical structures on coconut trees

The vertex equation expresses the product of the two labels at a vertex as the sum
of its neighbours' labels. Starting at a leaf, this equation propagates a common
divisor of the leaf labels back along the path.

## References

* Alexander Diaz-Lopez, Brian Ha, Pamela E. Harris, Jonathan Rogers, Theo Koss, and Dorian Smith,
  *Arithmetical Structures on Coconut Trees*, INTEGERS **25** (2025), Article A82, pp. 1–23,
  Definitions 1–3, Lemmas 1–3, and Proposition 8. The smoothness characterization is Lemma 2.
* K. Archer, A. C. Bishop, A. Diaz-Lopez, L. D. García Puente, D. Glass, and J. Louwsma,
  *Arithmetical structures on bidents*, Discrete Mathematics **343**, no. 7 (2020),
  Article 111850, Lemma 2.1, credited for the path monotonicity argument in Lemma 1 above.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Arithmetical structure.** An arithmetical structure on a graph $G$ with vertex set $V$ is a
pair of labelings $d, r : V \to \mathbb{N}$ such that $d(v) > 0$ and $r(v) > 0$ for every vertex
$v$, $d(v)\, r(v) = \sum_{w \sim v} r(w)$ for every vertex $v$, where the sum runs over the
neighbours $w$ of $v$, and the only natural number dividing every $r(v)$ is $1$. For a finite graph
with adjacency matrix $A$ the middle condition reads $(\operatorname{diag}(d) - A)\, r = 0$.

The neighbour sum is taken to be $0$ when $v$ has infinitely many neighbours, so no arithmetical
structure exists on a graph with a vertex of infinite degree.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 2.1
(arXiv numbering). -/
public def IsArithmeticalStructure {V : Type*} (G : SimpleGraph V) (d r : V → ℕ) : Prop :=
  (∀ v, 0 < d v) ∧ (∀ v, 0 < r v) ∧
    (∀ v, d v * r v = ∑ᶠ w ∈ {w | G.Adj v w}, r w) ∧
    ∀ g : ℕ, (∀ v, g ∣ r v) → g = 1

/-- **The all-ones structure on a single edge.** On the graph with two vertices joined by an edge,
the labelings $d = (1, 1)$ and $r = (1, 1)$ form an arithmetical structure.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 2.1
(arXiv numbering). -/
public theorem isArithmeticalStructure_top_fin_two :
    IsArithmeticalStructure (⊤ : SimpleGraph (Fin 2)) 1 1 := by
  refine ⟨fun _ => one_pos, fun _ => one_pos, fun v => ?_, fun g hg => Nat.dvd_one.mp (hg 0)⟩
  rcases (show v = 0 ∨ v = 1 by fin_cases v <;> simp) with rfl | rfl
  · have : {w : Fin 2 | (⊤ : SimpleGraph (Fin 2)).Adj 0 w} = {1} := by
      ext w; fin_cases w <;> simp
    rw [this, finsum_mem_singleton]
    rfl
  · have : {w : Fin 2 | (⊤ : SimpleGraph (Fin 2)).Adj 1 w} = {0} := by
      ext w; fin_cases w <;> simp
    rw [this, finsum_mem_singleton]
    rfl

/-- **Coconut tree.** For natural numbers $p$ and $s$, the coconut tree $\mathrm{CT}(p, s)$ is the
graph whose vertices are the path vertices $v_1, \dots, v_p$ and the leaves
$v_{\ell_1}, \dots, v_{\ell_s}$, in which $v_i$ and $v_{i+1}$ are adjacent for $1 \le i < p$, every
leaf is adjacent to $v_p$, and there are no other edges. For $p = 0$ it consists of $s$ isolated
vertices.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 2.2
(arXiv numbering). -/
public def coconutTree (p s : ℕ) : SimpleGraph (Fin p ⊕ Fin s) :=
  SimpleGraph.fromRel fun a b =>
    match a, b with
    | .inl i, .inl j => i.val + 1 = j.val
    | .inl i, .inr _ => i.val + 1 = p
    | .inr _, _ => False

/-- **Adjacent path vertices of a coconut tree.** Let the coconut tree $CT(p, s)$ have path
vertices $v_1, \dots, v_p$. Two path vertices $v_a$ and $v_b$ are adjacent if and only if
$|a - b| = 1$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 2.2
(arXiv numbering). -/
public theorem coconutTree_adj_inl_inl {p s : ℕ} (i j : Fin p) :
    (coconutTree p s).Adj (.inl i) (.inl j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  simp only [coconutTree, SimpleGraph.fromRel_adj, ne_eq, Sum.inl.injEq]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    refine ⟨fun hij => ?_, h⟩
    subst hij
    omega

/-- **Adjacency of leaves and path vertices in a coconut tree.** Let the coconut tree
$CT(p, s)$ have path vertices $v_1, \dots, v_p$, with central vertex $v_p$. A leaf of $CT(p, s)$
is adjacent to a path vertex $v_k$ if and only if $k = p$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 2.2
(arXiv numbering). -/
public theorem coconutTree_adj_inl_inr {p s : ℕ} (i : Fin p) (j : Fin s) :
    (coconutTree p s).Adj (.inl i) (.inr j) ↔ i.val + 1 = p := by
  simp [coconutTree, SimpleGraph.fromRel_adj]

/-- **Leaves of a coconut tree are pairwise nonadjacent.** No leaf of the coconut tree $CT(p, s)$
is adjacent to a leaf.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 2.2
(arXiv numbering). -/
public theorem coconutTree_not_adj_inr_inr {p s : ℕ} (j j' : Fin s) :
    ¬(coconutTree p s).Adj (.inr j) (.inr j') := by
  simp [coconutTree, SimpleGraph.fromRel_adj]

/-- **Smooth arithmetical structure on a coconut tree.** Let $CT(p, s)$ be the coconut tree with
path vertices $v_1, \dots, v_p$ and leaves $\ell_1, \dots, \ell_s$ adjacent to $v_p$. An
arithmetical structure $(d, r)$ on $CT(p, s)$ is smooth if $d(v_i) \ge 2$ for $1 \le i \le p - 1$
and $d(\ell_j) \ge 2$ for $1 \le j \le s$; there is no condition on $d(v_p)$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 2.3
(arXiv numbering). -/
public def IsSmoothCoconut (p s : ℕ) (d r : Fin p ⊕ Fin s → ℕ) : Prop :=
  IsArithmeticalStructure (coconutTree p s) d r ∧
    (∀ i : Fin p, i.val + 1 < p → 2 ≤ d (.inl i)) ∧ ∀ j, 2 ≤ d (.inr j)

/-- **Leaves of a smooth coconut structure have label at least 2.** If $(d, r)$ is a smooth
arithmetical structure on the coconut tree $\mathrm{CT}(p, s)$, then $d_{\ell_j} \ge 2$ for every
leaf $\ell_j$, $1 \le j \le s$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 2.3
(arXiv numbering). -/
public theorem IsSmoothCoconut.two_le_leaf {p s : ℕ} {d r : Fin p ⊕ Fin s → ℕ}
    (h : IsSmoothCoconut p s d r) (j : Fin s) : 2 ≤ d (.inr j) :=
  h.2.2 j

namespace IsSmoothCoconut

-- Path vertices occupy levels 1 through p, and all leaves occupy level p + 1.
private def level (p s k : ℕ) : Set (Fin p ⊕ Fin s) :=
  {v | Sum.elim (fun i : Fin p => i.val + 1) (fun _ : Fin s => p + 1) v = k}

private noncomputable def levelSum {p s : ℕ} (r : Fin p ⊕ Fin s → ℕ) (k : ℕ) : ℕ :=
  ∑ᶠ w ∈ level p s k, r w

private theorem levelSum_path {p s : ℕ} (r : Fin p ⊕ Fin s → ℕ) (i : Fin p) :
    levelSum r (i.val + 1) = r (.inl i) := by
  have heq : level p s (i.val + 1) = {Sum.inl i} := by
    ext (j | j)
    · simp [level, Fin.ext_iff]
    · simp [level, Nat.ne_of_gt i.isLt]
  rw [levelSum, heq, finsum_mem_singleton]

private theorem levelSum_leaves {p s : ℕ} (r : Fin p ⊕ Fin s → ℕ) :
    levelSum r (p + 1) = ∑ j, r (.inr j) := by
  have heq : level p s (p + 1) = Set.range Sum.inr := by
    ext (i | j)
    · simp [level, Nat.ne_of_lt i.isLt]
    · simp [level]
  rw [levelSum, heq, finsum_mem_range Sum.inr_injective, finsum_eq_sum_of_fintype]

-- At a path vertex the neighbours are precisely the two adjacent levels.
private theorem path_equation {p s : ℕ} {d r : Fin p ⊕ Fin s → ℕ}
    (h : IsArithmeticalStructure (coconutTree p s) d r) (i : Fin p) :
    d (.inl i) * levelSum r (i.val + 1) = levelSum r i.val + levelSum r (i.val + 2) := by
  have hadj : {w | (coconutTree p s).Adj (.inl i) w} =
      level p s i.val ∪ level p s (i.val + 2) := by
    ext (j | j)
    · simp [level, coconutTree_adj_inl_inl]
      omega
    · simp [level, coconutTree_adj_inl_inr]
      omega
  have hdisj : Disjoint (level p s i.val) (level p s (i.val + 2)) := by
    rw [Set.disjoint_left]
    intro w hw hw'
    simp only [level, Set.mem_ofPred_eq] at hw hw'
    omega
  rw [levelSum_path, h.2.2.1 (.inl i), hadj]
  exact finsum_mem_union hdisj (Set.toFinite _) (Set.toFinite _)

-- Smoothness forces growth from the empty level 0 up to the central vertex.
private theorem levelSum_lt_succ {n s : ℕ} {d r : Fin (n + 1) ⊕ Fin s → ℕ}
    (h : IsSmoothCoconut (n + 1) s d r) (k : ℕ) (hk : k ≤ n) :
    levelSum r k < levelSum r (k + 1) := by
  induction k with
  | zero =>
    have hempty : level (n + 1) s 0 = ∅ := by
      ext (i | j) <;> simp [level]
    rw [levelSum, hempty, finsum_mem_empty]
    exact (h.1.2.1 _).trans_eq (levelSum_path r (0 : Fin (n + 1))).symm
  | succ k ih =>
    let i : Fin (n + 1) := ⟨k, by omega⟩
    have heq := path_equation h.1 i
    have hbound := Nat.mul_le_mul_right (levelSum r (k + 1)) (h.2.1 i (Nat.succ_le_succ hk))
    have hlt := ih (by omega)
    change d (.inl i) * levelSum r (k + 1) = levelSum r k + levelSum r (k + 2) at heq
    change levelSum r (k + 1) < levelSum r (k + 2)
    omega

-- The centre's equation forces a positive leaf sum, even for a one-vertex path.
private theorem leafSum_pos {n s : ℕ} {d r : Fin (n + 1) ⊕ Fin s → ℕ}
    (h : IsSmoothCoconut (n + 1) s d r) : 0 < ∑ j, r (.inr j) := by
  have heq := path_equation h.1 (Fin.last n)
  have hbound := Nat.mul_le_mul_right (levelSum r (n + 1)) (h.1.1 (.inl (Fin.last n)))
  simp only [Fin.val_last] at heq
  rw [← levelSum_leaves r]
  change 0 < levelSum r (n + 2)
  have hlt := levelSum_lt_succ h n le_rfl
  omega

private theorem leaf_equation {n s : ℕ} {d r : Fin (n + 1) ⊕ Fin s → ℕ}
    (h : IsArithmeticalStructure (coconutTree (n + 1) s) d r) (j : Fin s) :
    d (.inr j) * r (.inr j) = r (.inl (Fin.last n)) := by
  have hadj : {w | (coconutTree (n + 1) s).Adj (.inr j) w} = {Sum.inl (Fin.last n)} := by
    ext (k | k)
    · rw [Set.mem_ofPred_eq, SimpleGraph.adj_comm, coconutTree_adj_inl_inr]
      simp [Fin.ext_iff]
    · simp [coconutTree_not_adj_inr_inr]
  rw [h.2.2.1 (.inr j), hadj, finsum_mem_singleton]

end IsSmoothCoconut

/-- **Characterization of smooth coconut structures.** Let $p \ge 1$ and let $(d, r)$ be an
arithmetical structure on the coconut tree $CT(p, s)$ with path vertices $v_1, \dots, v_p$ and
leaves $\ell_1, \dots, \ell_s$ adjacent to $v_p$. Then $(d, r)$ is smooth if and only if
$r(\ell_j) < r(v_p)$ for every $j$ and $r(v_1) < r(v_2) < \dots < r(v_p)$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Lemma 2
(`integers-2025-A82-lem-2`). -/
public theorem IsArithmeticalStructure.isSmoothCoconut_iff {p s : ℕ}
    {d r : Fin p ⊕ Fin s → ℕ} (hp : 0 < p)
    (h : IsArithmeticalStructure (coconutTree p s) d r) :
    IsSmoothCoconut p s d r ↔
      (∀ j, r (.inr j) < r (.inl ⟨p - 1, by omega⟩)) ∧ StrictMono fun i : Fin p => r (.inl i) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  change IsSmoothCoconut (n + 1) s d r ↔
    (∀ j, r (.inr j) < r (.inl (Fin.last n))) ∧ StrictMono fun i : Fin (n + 1) => r (.inl i)
  have hleaf (j : Fin s) : 2 ≤ d (.inr j) ↔ r (.inr j) < r (.inl (Fin.last n)) := by
    rw [← IsSmoothCoconut.leaf_equation h j]
    have hpos := h.2.1 (.inr j)
    constructor
    · intro hd
      have hmul := Nat.mul_le_mul_right (r (.inr j)) hd
      omega
    · intro hr
      by_contra! hd
      have hmul := Nat.mul_le_mul_right (r (.inr j)) (show d (.inr j) ≤ 1 by omega)
      rw [one_mul] at hmul
      omega
  constructor
  · intro hs
    refine ⟨fun j => (hleaf j).mp (hs.2.2 j), Fin.strictMono_iff_lt_succ.mpr ?_⟩
    intro i
    have hi := IsSmoothCoconut.levelSum_lt_succ hs (i.val + 1) (by omega)
    change IsSmoothCoconut.levelSum r (i.castSucc.val + 1) <
      IsSmoothCoconut.levelSum r (i.succ.val + 1) at hi
    simpa only [IsSmoothCoconut.levelSum_path] using hi
  · rintro ⟨hl, hm⟩
    refine ⟨h, ?_, fun j => (hleaf j).mpr (hl j)⟩
    intro i hi
    let j : Fin (n + 1) := ⟨i.val + 1, hi⟩
    have hlt : i < j := Nat.lt_succ_self i.val
    have hnext : r (.inl i) < r (.inl j) := hm hlt
    rw [← IsSmoothCoconut.levelSum_path r j] at hnext
    have heq := IsSmoothCoconut.path_equation h i
    rw [IsSmoothCoconut.levelSum_path] at heq
    by_contra! hd
    have hpos := h.1 (.inl i)
    have hd_one : d (.inl i) = 1 := by omega
    rw [hd_one, one_mul] at heq
    change r (.inl i) < IsSmoothCoconut.levelSum r (i.val + 2) at hnext
    omega

/-- **The leaf labels of a smooth arithmetical structure on a coconut tree are coprime.** Let
$(d, r)$ be a smooth arithmetical structure on the coconut tree $\mathrm{CT}(p, s)$ with leaves
$v_{\ell_1}, \dots, v_{\ell_s}$. If a natural number $g$ divides $r(v_{\ell_j})$ for every
$j = 1, \dots, s$, then $g = 1$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Lemma 3
(`integers-2025-A82-lem-3`). -/
public theorem IsSmoothCoconut.eq_one_of_dvd_leaves {p s : ℕ}
    {d r : Fin p ⊕ Fin s → ℕ} (h : IsSmoothCoconut p s d r) {g : ℕ}
    (hg : ∀ j, g ∣ r (.inr j)) : g = 1 := by
  apply h.1.2.2.2 g
  rintro (i | j)
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt i.isLt)
    obtain ⟨j, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (leafSum_pos h).ne'
    have hleaf := leaf_equation h.1 j
    have hpair (k : ℕ) (hk : k ≤ n + 1) :
        g ∣ levelSum r k ∧ g ∣ levelSum r (k + 1) := by
      induction hk using Nat.decreasingInduction with
      | self =>
        rw [show levelSum r (n + 1) = _ from levelSum_path r (Fin.last n), ← hleaf,
          levelSum_leaves]
        exact ⟨dvd_mul_of_dvd_right (hg j) _, Finset.dvd_sum fun l _ => hg l⟩
      | of_succ k hk ih =>
        have heq := path_equation h.1 (⟨k, hk⟩ : Fin (n + 1))
        have hdvd := dvd_mul_of_dvd_right ih.1 (d (.inl ⟨k, hk⟩))
        rw [heq] at hdvd
        exact ⟨(Nat.dvd_add_iff_left ih.2).2 hdvd, ih.1⟩
    rw [← levelSum_path r i]
    exact (hpair i.val i.isLt.le).2
  · exact hg j

/-- **Smooth coconut structures with central label above one.** Let $p \ge 1$ and let $(d, r)$ be
a smooth arithmetical structure on the coconut tree $\mathrm{CT}(p, s)$, with central vertex $v_p$
and leaves $\ell_1, \ldots, \ell_s$. Then $d_{v_p} > 1$ if and only if
$r_{v_p} < \sum_{j=1}^{s} r_{\ell_j}$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Proposition 8
(`integers-2025-A82-prop-8`). -/
public theorem IsSmoothCoconut.one_lt_center_iff {p s : ℕ} (hp : 0 < p)
    {d r : Fin p ⊕ Fin s → ℕ} (h : IsSmoothCoconut p s d r) :
    1 < d (.inl ⟨p - 1, by omega⟩) ↔ r (.inl ⟨p - 1, by omega⟩) < ∑ j, r (.inr j) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  let c : Fin (n + 1) ⊕ Fin s := .inl (Fin.last n)
  change 1 < d c ↔ r c < ∑ j, r (.inr j)
  have hc : levelSum r (n + 1) = r c := levelSum_path r (Fin.last n)
  have hprev := levelSum_lt_succ h n le_rfl
  rw [hc] at hprev
  have heq := path_equation h.1 (Fin.last n)
  simp only [Fin.val_last, hc, levelSum_leaves] at heq
  change d c * r c = _ at heq
  constructor
  · intro hd
    have hmul := Nat.mul_le_mul_right (r c) (show 2 ≤ d c from hd)
    omega
  · intro hsum
    have hmul : 1 * r c < d c * r c := by omega
    exact (Nat.mul_lt_mul_right (h.1.2.1 c)).mp hmul

/-- **Smooth structures on coconut trees with two leaves.** Let $p \ge 1$ and let $(d, r)$ be a
smooth arithmetical structure on the coconut tree $CT(p, 2)$, whose path is
$v_1, \dots, v_p$ and whose two leaves are attached to the central vertex $v_p$. Then
$d(v_p) \le 1$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Corollary 7
(`integers-2025-A82-cor-7`). -/
public theorem IsSmoothCoconut.center_le_one_of_two {p : ℕ} (hp : 0 < p)
    {d r : Fin p ⊕ Fin 2 → ℕ} (h : IsSmoothCoconut p 2 d r) :
    d (.inl ⟨p - 1, by omega⟩) ≤ 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  let c : Fin (n + 1) ⊕ Fin 2 := .inl (Fin.last n)
  change d c ≤ 1
  have hleaf (j : Fin 2) : 2 * r (.inr j) ≤ r c := calc
    _ ≤ d (.inr j) * r (.inr j) := Nat.mul_le_mul_right _ (h.two_le_leaf j)
    _ = r c := leaf_equation h.1 j
  have hsum : (∑ j, r (.inr j)) ≤ r c := by
    rw [Fin.sum_univ_two]
    have h₀ := hleaf 0
    have h₁ := hleaf 1
    omega
  have hc : levelSum r (n + 1) = r c := levelSum_path r (Fin.last n)
  have hprev := levelSum_lt_succ h n le_rfl
  rw [hc] at hprev
  have heq := path_equation h.1 (Fin.last n)
  simp only [Fin.val_last, hc, levelSum_leaves] at heq
  change d c * r c = _ at heq
  have hmul : d c * r c < 2 * r c := by omega
  exact Nat.le_of_lt_succ ((Nat.mul_lt_mul_right (h.1.2.1 c)).mp hmul)

end

end MetaMathlibExt
