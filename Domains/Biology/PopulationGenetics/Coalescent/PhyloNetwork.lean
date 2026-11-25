/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Digraph.FiniteDAG
public import Domains.Biology.PopulationGenetics.AdmixtureGraph
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Fin

/-!
# Phylogenetic networks and their routing kernel

A `PhyloNetwork` extends an `AdmixtureGraph` with node ages and nothing else: the root, the
parents function (`parents`), the proportions (here called inheritance probabilities,
`inherit v u = prop v u`), their normalization, and acyclicity (the well-founded parent
relation `wf`) all come from the underlying admixture graph. Every non-root vertex has one or
two parents; node ages are nonincreasing along edges, so branch lengths `age u - age v` are
nonnegative (zero-length edges are allowed). Out-degrees are unrestricted and vertices carry
no leaf labels: this is the parent-bounded routing skeleton of a phylogenetic network, not
the fully binary notion (which would also bound out-degrees and label the leaves by taxa):
at a reticulation vertex `v` with parents `u₁, u₂`, a lineage arriving at `v` continues to
`u₁` with probability `γ = inherit v u₁ ∈ [0, 1]` and to `u₂` with probability `1 - γ`;
at a tree vertex the unique parent has inheritance probability `1`.

The derived digraph `toDigraph` (also written `G`) has `Adj u v ↔ u ∈ parents v`; it is
acyclic (`PhyloNetwork.isAcyclic`). The routing kernel `routeProb v a` is the underlying
graph's multi-lineage kernel: the probability that `k` lineages at `v` choose the parents
`a : Fin k → V`; at non-root `v` its rows sum to `1` over all parent choices (and over the
parents of `v`), while at the root, where no lineage can move, the row is `0` for `k > 0`
(`routeProb_root`, `sum_routeProb_root`).

The `activeGraph` keeps the edges used with positive probability. When every inheritance
probability is `0` or `1`, the active graph is a rooted tree and the routing is
deterministic; a reticulation with `0 < γ < 1` uses both parents, so the active graph is not
a tree.

## References

* C. Solís-Lemus and C. Ané, *Inferring phylogenetic networks with maximum pseudolikelihood
  under incomplete lineage sorting*, PLoS Genet. 12 (2016), e1005896 (network data model and
  inheritance probabilities).
-/

@[expose] public section

open Finset

namespace MathlibExt.Biology.PopulationGenetics.Coalescent

/-- An **age-monotone parent-bounded routing network**: an admixture graph on a finite set `V` of
nodes (rooted, acyclic, every non-root node with one parent (a tree node) or two parents (a
reticulation node), proportions normalized at every non-root node) equipped with node ages. This is
the routing skeleton of a rooted phylogenetic network with inheritance probabilities
(Yu–Degnan–Nakhleh 2012; Zhang–Ogilvie–Drummond–Stadler 2018), without the binary out-degree
classification, leaf labels, or strict temporal constraints of the fully binary notion; out-degrees
are unrestricted. Node ages `time` (measured backward from the present) are only weakly monotone
along edges: a parent is never younger than its child (`time v ≤ time u`, so zero-length edges are
allowed; constant ages are not excluded), and the branch length of an edge `u → v` is
`time u - time v`. This is strictly weaker than time consistency in the phylogenetic sense, which
would in addition force tree edges to advance strictly in time. A lineage at `v` traces back to the
parent `u` with probability `inherit v u = prop v u`: this vanishes off the parents and sums to `1`
over the parents, so it is `1` at a tree node and `γ, 1 - γ` at a reticulation node. -/
structure PhyloNetwork (V : Type*) [Fintype V] extends AdmixtureGraph V where
  /-- Node ages, measured backward in time. -/
  time : V → ℝ
  /-- Age monotonicity: a parent is at least as old as its child. -/
  time_le : ∀ u v, u ∈ parents v → time v ≤ time u

namespace PhyloNetwork

variable {V : Type*} [Fintype V] (N : PhyloNetwork V)

/-- `inherit v u`: the probability that a lineage at `v` traces back to the parent `u`. This
is the underlying admixture graph's proportion `prop v u`, under its phylogenetic name. -/
abbrev inherit (v u : V) : ℝ := N.prop v u

/-- The digraph of the network, derived from the parents function: `Adj u v` iff `u` is a
parent of `v` (edges run from ancestor to descendant). -/
def toDigraph : Digraph V where
  Adj u v := u ∈ N.parents v

/-- The parent-to-child digraph of the network, `toDigraph`: `Adj u v` iff `u` is a parent of `v`
(edges run from ancestor to descendant). -/
abbrev G : Digraph V := N.toDigraph

/-- Adjacency in the derived digraph is decidable once equality on `V` is. -/
instance decidableRel_toDigraph [DecidableEq V] : DecidableRel N.toDigraph.Adj :=
  fun u v => Finset.decidableMem u (N.parents v)

/-- The derived digraph is acyclic, from well-foundedness of the parent relation. -/
theorem isAcyclic : N.toDigraph.IsAcyclic := by
  intro v hv
  exact N.toAdmixtureGraph.wf.transGen.irrefl.irrefl v hv

/-- The parents of `v` as read off the derived digraph are the graph's parents function. -/
theorem parentsOf_toDigraph [DecidableEq V] (v : V) :
    Digraph.parentsOf N.toDigraph v = N.parents v := by
  ext u
  simp only [Digraph.mem_parentsOf]
  exact Iff.rfl

/-- The root has no parent in the derived digraph. -/
theorem parentsOf_root [DecidableEq V] : Digraph.parentsOf N.toDigraph N.root = ∅ := by
  rw [N.parentsOf_toDigraph]
  exact N.parents_root

/-- Every non-root node has one parent (tree node) or two (reticulation node) in the derived
digraph. -/
theorem card_parentsOf [DecidableEq V] (v : V) (hv : v ≠ N.root) :
    (Digraph.parentsOf N.toDigraph v).card = 1 ∨
      (Digraph.parentsOf N.toDigraph v).card = 2 := by
  rw [N.parentsOf_toDigraph]
  exact N.card_parents v hv

/-- Inheritance probabilities are nonnegative. -/
theorem inherit_nonneg (v u : V) : 0 ≤ N.inherit v u := N.prop_nonneg v u

/-- A lineage only moves to a parent. -/
theorem inherit_eq_zero (v u : V) (h : u ∉ N.parents v) : N.inherit v u = 0 :=
  N.prop_eq_zero v u h

/-- The inheritance probabilities at a non-root node sum to `1` over its parents. -/
theorem sum_inherit (v : V) (hv : v ≠ N.root) : ∑ u ∈ N.parents v, N.inherit v u = 1 :=
  N.sum_prop v hv

/-- `v` is a reticulation node: it has two parents. -/
def IsReticulation (v : V) : Prop := (N.parents v).card = 2

/-- The length of the branch `u → v`: the age difference of its endpoints. -/
def branchLength (u v : V) : ℝ := N.time u - N.time v

/-- All branch lengths are nonnegative. -/
def NonnegLengths : Prop := ∀ u v, N.G.Adj u v → 0 ≤ N.branchLength u v

/-- **Age monotonicity gives nonnegative branch lengths.** -/
theorem nonnegLengths : N.NonnegLengths := fun u v h => sub_nonneg.2 (N.time_le u v h)

/-- Membership in `parents v` is adjacency into `v`. -/
theorem mem_parents {u v : V} : u ∈ N.parents v ↔ N.G.Adj u v := Iff.rfl

/-- **Inheritance probabilities are at most `1`**; with `inherit_nonneg` they lie in `[0, 1]`
(`γ ∈ [0, 1]`). -/
theorem inherit_le_one (v u : V) : N.inherit v u ≤ 1 :=
  N.toAdmixtureGraph.prop_le_one v u

/-- At a reticulation node with parents `u₁ ≠ u₂`, the two inheritance probabilities are
`γ` and `1 - γ`. -/
theorem inherit_eq_one_sub [DecidableEq V] {v u₁ u₂ : V} (h : N.parents v = {u₁, u₂})
    (hne : u₁ ≠ u₂) : N.inherit v u₂ = 1 - N.inherit v u₁ :=
  N.toAdmixtureGraph.prop_eq_one_sub_of_parents_eq_pair h hne

/-- The **reticulation routing kernel** `∏ i, inherit v (a i)`. At a non-root node `v` it is the
probability that `k` lineages entering `v` (backward in time) move to parents independently,
lineage `i` to `a i`, and its row sums to `1` (`sum_routeProb`); at the root, which has no parent,
every assignment of `k > 0` lineages has value `0` (`routeProb_root`). For `k = 0` the single empty
assignment has probability `1`, at every node. This is the underlying admixture graph's routing
kernel. -/
abbrev routeProb (v : V) {k : ℕ} (a : Fin k → V) : ℝ :=
  N.toAdmixtureGraph.routeProb v a

/-- Routing probabilities are nonnegative. -/
theorem routeProb_nonneg (v : V) {k : ℕ} (a : Fin k → V) : 0 ≤ N.routeProb v a :=
  N.toAdmixtureGraph.routeProb_nonneg v a

/-- A routing that sends some lineage to a non-parent has probability `0`. -/
theorem routeProb_eq_zero {v : V} {k : ℕ} {a : Fin k → V} {i : Fin k}
    (hi : a i ∉ N.parents v) : N.routeProb v a = 0 :=
  N.toAdmixtureGraph.routeProb_eq_zero hi

/-- **The routing kernel is normalized** over the assignments of the `k` lineages to the
parents of a non-root node. -/
theorem sum_routeProb_parents {v : V} (hv : v ≠ N.root) (k : ℕ) :
    ∑ a ∈ Fintype.piFinset (fun _ : Fin k => N.parents v), N.routeProb v a = 1 :=
  N.toAdmixtureGraph.sum_routeProb_parents hv k

/-- **The routing kernel rows sum to `1`** over all maps from the lineages to the nodes, at a
non-root node. -/
theorem sum_routeProb {v : V} (hv : v ≠ N.root) (k : ℕ) :
    ∑ a : Fin k → V, N.routeProb v a = 1 :=
  N.toAdmixtureGraph.sum_routeProb hv k

/-- At the root there is no parent to move to: for `k > 0` every assignment has
probability `0`. -/
theorem routeProb_root {k : ℕ} (hk : 0 < k) (a : Fin k → V) :
    N.routeProb N.root a = 0 :=
  N.toAdmixtureGraph.routeProb_root hk a

/-- The root row of the routing kernel has total mass `0` for `k > 0`. -/
theorem sum_routeProb_root {k : ℕ} (hk : 0 < k) :
    ∑ a : Fin k → V, N.routeProb N.root a = 0 :=
  N.toAdmixtureGraph.sum_routeProb_root hk

/-- The edges used with positive inheritance probability. -/
def activeGraph : Digraph V where
  Adj u v := N.G.Adj u v ∧ 0 < N.inherit v u

/-- **`γ ∈ {0, 1}` gives a tree.** If every inheritance probability is `0` or `1`, the edges used
with positive probability form a rooted tree on the nodes of the network, rooted at the network's
root. -/
theorem isRootedTree_activeGraph [DecidableEq V]
    (h01 : ∀ v u, N.inherit v u = 0 ∨ N.inherit v u = 1) :
    Digraph.IsRootedTree N.activeGraph N.root := by
  have huniq : ∀ v, v ≠ N.root → ∃! u, N.activeGraph.Adj u v := by
    intro v hv
    have hs' : ∑ u ∈ N.parents v, N.inherit v u = 1 := N.sum_inherit v hv
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
  have hacyc : N.activeGraph.IsAcyclic :=
    Digraph.isAcyclic_of_le (fun u v h => h.1) N.isAcyclic
  have hreach : ∀ v, Relation.ReflTransGen N.activeGraph.Adj N.root v := by
    have hwf : WellFounded N.activeGraph.Adj :=
      Digraph.isAcyclic_iff_wellFounded.1 hacyc
    intro v
    refine hwf.induction (C := fun v => Relation.ReflTransGen N.activeGraph.Adj N.root v) v
      fun v ih => ?_
    by_cases hv : v = N.root
    · subst hv
      exact Relation.ReflTransGen.refl
    · obtain ⟨u, hu, -⟩ := huniq v hv
      exact (ih u hu).tail hu
  refine ⟨hacyc, fun u hu => ?_, huniq, hreach⟩
  have : u ∈ N.parents N.root := N.mem_parents.2 hu.1
  simp [N.parents_root] at this

/-- **`γ ∈ {0, 1}` makes the routing deterministic**: at a non-root node every lineage moves
to the one parent with inheritance probability `1`. -/
theorem routeProb_of_zero_one [DecidableEq V]
    (h01 : ∀ v u, N.inherit v u = 0 ∨ N.inherit v u = 1) {v : V} (hv : v ≠ N.root) :
    ∃ u ∈ N.parents v, ∀ k (a : Fin k → V),
      N.routeProb v a = if ∀ i, a i = u then 1 else 0 := by
  obtain ⟨u, hu, huniq⟩ := (isRootedTree_activeGraph N h01).2.2.1 v hv
  have hu1 : N.inherit v u = 1 := (h01 v u).resolve_left hu.2.ne'
  have hzero : ∀ w, w ≠ u → N.inherit v w = 0 := fun w hw =>
    (h01 v w).resolve_right fun h1 => by
      by_cases hwp : N.G.Adj w v
      · exact hw (huniq w ⟨hwp, by rw [h1]; exact one_pos⟩)
      · have := N.inherit_eq_zero v w (fun h => hwp (N.mem_parents.1 h)); linarith
  refine ⟨u, N.mem_parents.2 hu.1, fun k a => ?_⟩
  split_ifs with h
  · change (∏ i, N.inherit v (a i)) = 1
    simp [h, hu1]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    change (∏ i, N.inherit v (a i)) = 0
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hzero _ hi)

/-- Conversely, a reticulation node with `0 < γ < 1` uses both parent edges, so the active graph is
not a rooted tree with root `N.root`. -/
theorem not_isRootedTree_activeGraph [DecidableEq V] {v u₁ u₂ : V}
    (h : N.parents v = {u₁, u₂}) (hne : u₁ ≠ u₂)
    (hγ : 0 < N.inherit v u₁ ∧ N.inherit v u₁ < 1) :
    ¬ Digraph.IsRootedTree N.activeGraph N.root := by
  rintro ⟨-, -, hT, -⟩
  have hv : v ≠ N.root := by
    rintro rfl
    rw [N.parents_root] at h
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
