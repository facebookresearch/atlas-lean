/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Digraph.FiniteDAG
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Phylogenetic networks and their routing kernel

A `PhyloNetwork` is a finite rooted acyclic digraph (`Digraph.IsAcyclic`) in which every
non-root vertex has one or two parents, equipped with node ages (nonincreasing along edges,
so branch lengths `age u - age v` are nonnegative; zero-length edges are allowed) and
inheritance probabilities. Out-degrees are unrestricted and vertices carry no leaf labels:
this is the parent-bounded routing skeleton of a phylogenetic network, not the fully binary
notion (which would also bound out-degrees and label the leaves by taxa):
at a reticulation vertex `v` with parents `u₁, u₂`, a lineage arriving at `v` continues to
`u₁` with probability `γ = inherit v u₁ ∈ [0, 1]` and to `u₂` with probability `1 - γ`;
at a tree vertex the unique parent has inheritance probability `1`. The routing kernel
`routeProb v a` is the probability that `k` lineages at `v` choose the parents `a : Fin k → V`;
its rows sum to `1` over all parent choices, and over the parents of `v` for one lineage.

The `activeGraph` keeps the edges used with positive probability. When every inheritance
probability is `0` or `1`, the active graph is a rooted tree and the routing is deterministic;
a reticulation with `0 < γ < 1` uses both parents, so the active graph is not a tree.

## References

* C. Solís-Lemus and C. Ané, *Inferring phylogenetic networks with maximum pseudolikelihood
  under incomplete lineage sorting*, PLoS Genet. 12 (2016), e1005896 (network data model and
  inheritance probabilities).
-/

@[expose] public section

open Finset

namespace MathlibExt.Biology.PopulationGenetics.Coalescent

/-- The parents of `v` in a digraph whose edges run from ancestor to descendant. -/
def parentsOf {V : Type*} [Fintype V] (G : Digraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  {u | G.Adj u v}

/-- A **time-consistent parent-bounded routing network**: the routing skeleton of a rooted
phylogenetic network with inheritance probabilities (Yu–Degnan–Nakhleh 2012;
Zhang–Ogilvie–Drummond–Stadler 2018), without the binary out-degree classification or leaf
labels of the fully binary notion. The edges of the finite DAG `G` run from ancestor to
descendant. The root is the only node without a parent; every other node is a *tree node*
(one parent) or a *reticulation node* (two parents); out-degrees are unrestricted. Node ages
`time` (measured backward from the present) make the network time-consistent: a parent is
never younger than its child (`time v ≤ time u`, so zero-length edges are allowed), and the
branch length of an edge `u → v` is `time u - time v`. A lineage at `v` traces back to the
parent `u` with probability `inherit v u`: this vanishes off the parents and sums to `1`
over the parents, so it is `1` at a tree node and `γ, 1 - γ` at a reticulation node. -/
structure PhyloNetwork (V : Type*) [Fintype V] where
  /-- The directed acyclic graph; `G.Adj u v` means `u` is a parent of `v`. -/
  G : Digraph V
  /-- Adjacency is decidable. -/
  [decAdj : DecidableRel G.Adj]
  /-- The root. -/
  root : V
  /-- No directed cycle. -/
  isAcyclic : G.IsAcyclic
  /-- The root has no parent. -/
  parentsOf_root : parentsOf G root = ∅
  /-- Every other node has one parent (tree node) or two parents (reticulation node). -/
  card_parentsOf : ∀ v, v ≠ root → (parentsOf G v).card = 1 ∨ (parentsOf G v).card = 2
  /-- Node ages, measured backward in time. -/
  time : V → ℝ
  /-- Time-consistency: a parent is at least as old as its child. -/
  time_le : ∀ u v, G.Adj u v → time v ≤ time u
  /-- `inherit v u`: the probability that a lineage at `v` traces back to the parent `u`. -/
  inherit : V → V → ℝ
  /-- Inheritance probabilities are nonnegative. -/
  inherit_nonneg : ∀ v u, 0 ≤ inherit v u
  /-- A lineage only moves to a parent. -/
  inherit_eq_zero : ∀ v u, u ∉ parentsOf G v → inherit v u = 0
  /-- The inheritance probabilities at a non-root node sum to `1` over its parents. -/
  sum_inherit : ∀ v, v ≠ root → ∑ u ∈ parentsOf G v, inherit v u = 1

attribute [instance] PhyloNetwork.decAdj

namespace PhyloNetwork

variable {V : Type*} [Fintype V] (N : PhyloNetwork V)

/-- The parents of `v`. -/
def parents (v : V) : Finset V := parentsOf N.G v

/-- `v` is a reticulation node: it has two parents. -/
def IsReticulation (v : V) : Prop := (N.parents v).card = 2

/-- The length of the branch `u → v`: the age difference of its endpoints. -/
def branchLength (u v : V) : ℝ := N.time u - N.time v

/-- All branch lengths are nonnegative. -/
def NonnegLengths : Prop := ∀ u v, N.G.Adj u v → 0 ≤ N.branchLength u v

/-- **Time-consistency gives nonnegative branch lengths.** -/
theorem nonnegLengths : N.NonnegLengths := fun u v h => sub_nonneg.2 (N.time_le u v h)

/-- Membership in `parents v` is adjacency into `v`. -/
theorem mem_parents {u v : V} : u ∈ N.parents v ↔ N.G.Adj u v := by
  simp [parents, parentsOf]

/-- **Inheritance probabilities lie in `[0, 1]`** (`γ ∈ [0, 1]`). -/
theorem inherit_le_one (v u : V) : N.inherit v u ≤ 1 := by
  by_cases hu : u ∈ N.parents v
  · have hv : v ≠ N.root := by
      rintro rfl
      simp [parents, N.parentsOf_root] at hu
    have h := N.sum_inherit v hv
    rw [← h]
    exact single_le_sum (fun w _ => N.inherit_nonneg v w) hu
  · rw [N.inherit_eq_zero v u hu]
    exact zero_le_one

/-- At a reticulation node with parents `u₁ ≠ u₂`, the two inheritance probabilities are
`γ` and `1 - γ`. -/
theorem inherit_eq_one_sub [DecidableEq V] {v u₁ u₂ : V} (h : N.parents v = {u₁, u₂}) (hne : u₁ ≠ u₂) :
    N.inherit v u₂ = 1 - N.inherit v u₁ := by
  have hv : v ≠ N.root := by
    rintro rfl
    have : N.parents N.root = ∅ := N.parentsOf_root
    rw [this] at h
    exact (Finset.insert_ne_empty u₁ {u₂}) h.symm
  have hs := N.sum_inherit v hv
  have : ∑ u ∈ N.parents v, N.inherit v u = ∑ u ∈ parentsOf N.G v, N.inherit v u := rfl
  rw [← this, h, Finset.sum_pair hne] at hs
  linarith

/-- The **reticulation routing kernel**: `k` lineages entering `v` (backward in time) move to
parents independently, lineage `i` to `a i`, with probability `∏ i, inherit v (a i)`. -/
def routeProb (v : V) {k : ℕ} (a : Fin k → V) : ℝ := ∏ i, N.inherit v (a i)

/-- Routing probabilities are nonnegative. -/
theorem routeProb_nonneg (v : V) {k : ℕ} (a : Fin k → V) : 0 ≤ N.routeProb v a :=
  prod_nonneg fun i _ => N.inherit_nonneg v (a i)

/-- A routing that sends some lineage to a non-parent has probability `0`. -/
theorem routeProb_eq_zero {v : V} {k : ℕ} {a : Fin k → V} {i : Fin k} (hi : a i ∉ N.parents v) :
    N.routeProb v a = 0 :=
  prod_eq_zero (mem_univ i) (N.inherit_eq_zero v (a i) hi)

/-- **The routing kernel is normalized** over the assignments of the `k` lineages to the parents
of a non-root node. -/
theorem sum_routeProb_parents {v : V} (hv : v ≠ N.root) (k : ℕ) :
    ∑ a ∈ Fintype.piFinset (fun _ : Fin k => N.parents v), N.routeProb v a = 1 := by
  rw [show (∑ a ∈ Fintype.piFinset (fun _ : Fin k => N.parents v), N.routeProb v a) =
      ∏ _i : Fin k, ∑ u ∈ N.parents v, N.inherit v u from (prod_univ_sum _ _).symm]
  have h := N.sum_inherit v hv
  simp only [parents] at h ⊢
  simp [h]

/-- **The routing kernel rows sum to `1`** over all maps from the lineages to the nodes. -/
theorem sum_routeProb {v : V} (hv : v ≠ N.root) (k : ℕ) :
    ∑ a : Fin k → V, N.routeProb v a = 1 := by
  have hrow : ∑ u, N.inherit v u = 1 := by
    rw [← sum_subset (subset_univ (N.parents v)) fun u _ hu => N.inherit_eq_zero v u hu]
    exact N.sum_inherit v hv
  rw [show (∑ a : Fin k → V, N.routeProb v a) = ∏ _i : Fin k, ∑ u, N.inherit v u from
    (Fintype.prod_sum _).symm]
  simp [hrow]

/-- The edges used with positive inheritance probability. -/
def activeGraph : Digraph V where
  Adj u v := N.G.Adj u v ∧ 0 < N.inherit v u

/-- A **rooted tree** (arborescence) with root `r`: acyclic, `r` has no parent, and every other
vertex has exactly one parent. -/
def IsRootedTree (H : Digraph V) (r : V) : Prop :=
  H.IsAcyclic ∧ (∀ u, ¬ H.Adj u r) ∧ ∀ v, v ≠ r → ∃! u, H.Adj u v

omit [Fintype V] in
/-- A subgraph of an acyclic digraph is acyclic. -/
theorem isAcyclic_of_le {G H : Digraph V} (hGH : ∀ u v, H.Adj u v → G.Adj u v)
    (hG : G.IsAcyclic) : H.IsAcyclic := fun v hv =>
  hG v (Relation.TransGen.mono (r := H.Adj) (p := G.Adj) (fun a b h => hGH a b h) v v hv)

/-- **`γ ∈ {0, 1}` gives a tree.** If every inheritance probability is `0` or `1`, the edges
used with positive probability form a rooted tree on the nodes of the network. -/
theorem isRootedTree_activeGraph [DecidableEq V] (h01 : ∀ v u, N.inherit v u = 0 ∨ N.inherit v u = 1) :
    IsRootedTree N.activeGraph N.root := by
  refine ⟨isAcyclic_of_le (fun u v h => h.1) N.isAcyclic, fun u hu => ?_, fun v hv => ?_⟩
  · have : u ∈ N.parents N.root := N.mem_parents.2 hu.1
    have h0 : N.parents N.root = ∅ := N.parentsOf_root
    simp [h0] at this
  · have hs := N.sum_inherit v hv
    have hs' : ∑ u ∈ N.parents v, N.inherit v u = 1 := hs
    obtain ⟨u, hu, hpos⟩ : ∃ u ∈ N.parents v, 0 < N.inherit v u := by
      by_contra hcon
      push Not at hcon
      have : ∑ u ∈ N.parents v, N.inherit v u ≤ 0 :=
        sum_nonpos fun u hu => hcon u hu
      linarith
    refine ⟨u, ⟨N.mem_parents.1 hu, hpos⟩, fun w hw => ?_⟩
    by_contra hwu
    have hw1 : N.inherit v w = 1 := (h01 v w).resolve_left hw.2.ne'
    have hu1 : N.inherit v u = 1 := (h01 v u).resolve_left hpos.ne'
    have hsub : ({w, u} : Finset V) ⊆ N.parents v := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact N.mem_parents.2 hw.1
      · exact hu
    have hle := sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => N.inherit_nonneg v x
    rw [sum_pair hwu, hw1, hu1] at hle
    linarith

/-- **`γ ∈ {0, 1}` makes the routing deterministic**: at a non-root node every lineage moves to
the one parent with inheritance probability `1`. -/
theorem routeProb_of_zero_one [DecidableEq V] (h01 : ∀ v u, N.inherit v u = 0 ∨ N.inherit v u = 1) {v : V}
    (hv : v ≠ N.root) :
    ∃ u ∈ N.parents v, ∀ k (a : Fin k → V),
      N.routeProb v a = if ∀ i, a i = u then 1 else 0 := by
  obtain ⟨u, hu, huniq⟩ := (isRootedTree_activeGraph N h01).2.2 v hv
  have hu1 : N.inherit v u = 1 := (h01 v u).resolve_left hu.2.ne'
  have hzero : ∀ w, w ≠ u → N.inherit v w = 0 := fun w hw =>
    (h01 v w).resolve_right fun h1 => by
      by_cases hwp : N.G.Adj w v
      · exact hw (huniq w ⟨hwp, by rw [h1]; exact one_pos⟩)
      · have := N.inherit_eq_zero v w (fun h => hwp (N.mem_parents.1 h)); linarith
  refine ⟨u, N.mem_parents.2 hu.1, fun k a => ?_⟩
  split_ifs with h
  · simp [routeProb, h, hu1]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    exact prod_eq_zero (mem_univ i) (hzero _ hi)

/-- Conversely, a reticulation node with `0 < γ < 1` uses both parent edges, so the active graph
is not a rooted tree. -/
theorem not_isRootedTree_activeGraph [DecidableEq V] {v u₁ u₂ : V} (h : N.parents v = {u₁, u₂}) (hne : u₁ ≠ u₂)
    (hγ : 0 < N.inherit v u₁ ∧ N.inherit v u₁ < 1) :
    ¬ IsRootedTree N.activeGraph N.root := by
  rintro ⟨-, -, hT⟩
  have hv : v ≠ N.root := by
    rintro rfl
    have : N.parents N.root = ∅ := N.parentsOf_root
    rw [this] at h
    exact (Finset.insert_ne_empty u₁ {u₂}) h.symm
  have h2 := N.inherit_eq_one_sub h hne
  have hm1 : N.G.Adj u₁ v := N.mem_parents.1 (by rw [h]; simp)
  have hm2 : N.G.Adj u₂ v := N.mem_parents.1 (by rw [h]; simp)
  obtain ⟨w, -, hw⟩ := hT v hv
  have e1 := hw u₁ ⟨hm1, hγ.1⟩
  have e2 := hw u₂ ⟨hm2, by rw [h2]; linarith [hγ.2]⟩
  exact hne (e1.trans e2.symm)

end PhyloNetwork

end MathlibExt.Biology.PopulationGenetics.Coalescent
