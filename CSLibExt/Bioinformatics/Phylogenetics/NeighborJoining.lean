/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Neighbor joining reconstructs the tree from an additive metric

Neighbor joining (NJ) builds a phylogeny from a dissimilarity `d` on a finite set `X` of taxa.
It keeps a partition `S` of `X` into clusters with a dissimilarity `D` between clusters,
starting from the singletons with `D {x} {y} = d x y`. While at least four clusters remain, it
picks distinct clusters `a, b ∈ S` minimizing the Q-criterion
`Q(a, b) = (|S| - 2) D a b - ∑_{c ∈ S} D a c - ∑_{c ∈ S} D b c` (Studier–Keppler's form of
Saitou–Nei's criterion), replaces them by the cluster `a ∪ b`, and sets
`D (a ∪ b) c = (D a c + D b c - D a b) / 2` for the other clusters `c`. When three clusters
remain they are joined at a single vertex. The topology of the output tree is the set of
splits `{A, X \ A}` given by the clusters `A` formed along the way (`NJRun`); branch-length
estimates are not part of this file. Ties may be broken arbitrarily: `NJRun` allows every
minimizing choice.

If `d` is the path-length metric of a binary phylogenetic `X`-tree with positive edge lengths
(taxa at the leaves, every other vertex of degree three), then any pair minimizing `Q` is a
cherry, and NJ returns exactly the splits of the internal edges of the tree (`njRun_splits`).

## Proof outline

Each edge `{a, b}` splits the taxa into its `a`-side and its `b`-side (`side`). On a binary
phylogenetic tree these splits are pairwise compatible, contain every trivial split, and are
binary (a side with at least two taxa is the disjoint union of two sides). The path length is
the total length of the edges whose split separates the two taxa (`dist_eq_sum_darts`), so
`Q(x, y) = -∑ w e · splitGain e x y` (`sub_sum_sub_sum_eq_neg_sum_splitGain`), where
`splitGain` is the number of taxa on the far side of a split not separating `x, y`, and `1` on
a split separating them. A combinatorial argument on compatible binary split systems
(`exists_eq_pair_of_isMax`) shows that a pair maximizing the total gain is a two-element side,
which on the tree is a cherry (`exists_adj_adj_of_qCriterion_min`).

For the whole run, the same argument applies to the split system induced on the current
clusters: every cluster stays a side of the tree, the cluster dissimilarity stays the total
length of the edges separating two clusters (the NJ update is exact on a joined cherry), and
every split of the tree is either formed, trivial, or a union of current clusters. With at most
three clusters left, every nontrivial split is formed.

The theorem is due to Saitou and Nei (1987) and Studier and Keppler (1988); see also Gascuel
(1994) and Bryant (2005). The split-system proof above was written for this formalization and
is not taken from those papers.

## Main results

* `njRun_splits`: on the path-length metric of a binary phylogenetic tree with positive edge
  lengths, every complete NJ run forms exactly the splits of the internal edges.
* `exists_adj_adj_of_qCriterion_min`: on such a metric with at least four taxa, a pair of taxa
  minimizing the Q-criterion is a cherry; `NJRun.exists_adj_adj_of_join_init` is the first
  join of a run.
* `exists_eq_pair_of_isMax`: the cherry lemma for compatible binary split systems.
* `dist_eq_sum_darts`: the split decomposition of a tree metric.
* `qCriterion_singleton`: the Q-criterion of two singleton clusters at the start of a run.
* `njRun_splits_of_join`: a run on any dissimilarity forms exactly the splits of the internal
  edges if each of its joins forms a side; `exists_splitSystem_of_partition`: on a partition into
  sides, the tree metric is the split distance of the induced split system on the clusters plus
  row terms. Both serve the robustness theorem in `NeighborJoiningRobustness.lean`.

## References

* N. Saitou and M. Nei, *The neighbor-joining method: a new method for reconstructing
  phylogenetic trees*, Mol. Biol. Evol. 4 (1987), 406–425.
* J. A. Studier and K. J. Keppler, *A note on the neighbor-joining algorithm of Saitou and
  Nei*, Mol. Biol. Evol. 5 (1988), 729–731.
* O. Gascuel, *A note on Sattath and Tversky's, Saitou and Nei's, and Studier and Keppler's
  algorithms for inferring phylogenies from evolutionary distances*, Mol. Biol. Evol. 11
  (1994), 961–963.
* D. Bryant, *On the uniqueness of the selection criterion in neighbor-joining*, J. Classif.
  22 (2005), 3–15.
* C. Semple and M. Steel, *Phylogenetics*, Oxford University Press, 2003, ch. 7.
-/
@[expose] public section

namespace Cslib.Bioinformatics.Phylogenetics.NeighborJoining

open Finset

/-! ### The algorithm -/

section Algorithm

variable {X : Type*} [DecidableEq X]

/-- The dissimilarity between clusters at the start of neighbor joining: on singletons,
`initialDist d {x} {y} = d x y` (only singleton values are used). -/
def initialDist (d : X → X → ℝ) (u v : Finset X) : ℝ :=
  ∑ x ∈ u, ∑ y ∈ v, d x y

/-- The Studier–Keppler form of the neighbor-joining criterion on the cluster set `S`:
`Q(a, b) = (|S| - 2) D a b - ∑_{c ∈ S} D a c - ∑_{c ∈ S} D b c`. -/
def qCriterion (S : Finset (Finset X)) (D : Finset X → Finset X → ℝ) (a b : Finset X) : ℝ :=
  ((S.card : ℝ) - 2) * D a b - ∑ c ∈ S, D a c - ∑ c ∈ S, D b c

/-- The cluster dissimilarity after joining `a` and `b`: the new cluster `a ∪ b` is at
`(D a c + D b c - D a b) / 2` from every other cluster `c`, and at `0` from itself; other
values are unchanged. -/
noncomputable def joinDist (D : Finset X → Finset X → ℝ) (a b : Finset X) (u v : Finset X) : ℝ :=
  if u = a ∪ b then (if v = a ∪ b then 0 else (D a v + D b v - D a b) / 2)
  else if v = a ∪ b then (D a u + D b u - D a b) / 2 else D u v

/-- `NJRun d S D C`: some run of neighbor joining on the dissimilarity `d` reaches the cluster
set `S` with cluster dissimilarity `D`, having formed the clusters in `C`. A join is allowed
while at least four clusters remain, for any pair of distinct clusters minimizing
`qCriterion`. -/
inductive NJRun [Fintype X] (d : X → X → ℝ) :
    Finset (Finset X) → (Finset X → Finset X → ℝ) → Finset (Finset X) → Prop
  /-- The run starts from the singletons, with no cluster formed. -/
  | init : NJRun d (Finset.univ.image fun x => {x}) (initialDist d) ∅
  /-- Join a pair of distinct clusters minimizing the Q-criterion. -/
  | join {S : Finset (Finset X)} {D : Finset X → Finset X → ℝ} {C : Finset (Finset X)}
      {a b : Finset X} :
      NJRun d S D C → 4 ≤ S.card → a ∈ S → b ∈ S → a ≠ b →
      (∀ a' ∈ S, ∀ b' ∈ S, a' ≠ b' → qCriterion S D a b ≤ qCriterion S D a' b') →
      NJRun d (insert (a ∪ b) ((S.erase a).erase b)) (joinDist D a b) (insert (a ∪ b) C)

end Algorithm

/-! ### Binary phylogenetic trees and their splits -/

/-- `G` with the taxon placement `ι` is a **binary phylogenetic `X`-tree**: `G` is a tree,
`ι` is injective, the leaves (degree-one vertices) are exactly the taxa, and every other
vertex has degree three. -/
def IsBinaryPhylogeneticTree {X : Type*} {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (ι : X → V) : Prop :=
  G.IsTree ∧ Function.Injective ι ∧ (∀ v, G.degree v = 1 ↔ v ∈ Set.range ι) ∧
    ∀ v, v ∉ Set.range ι → G.degree v = 3

open scoped Classical in
/-- The taxa on the `a`-side of the edge `{a, b}`: those whose vertex is still joined to `a`
once the edge `{a, b}` is deleted. -/
noncomputable def side {X : Type*} [Fintype X] {V : Type*} (G : SimpleGraph V) (ι : X → V)
    (a b : V) : Finset X :=
  univ.filter fun z => (G.deleteEdges {s(a, b)}).Reachable (ι z) a

/-- The contribution of one split `{A, Aᶜ}` to the neighbor-joining score of the pair `x, y`:
the number of taxa on the far side of the split when `x, y` lie on the same side, and `1`
when the split separates them. -/
def splitGain {X : Type*} [Fintype X] [DecidableEq X] (A : Finset X) (x y : X) : ℝ :=
  if x ∈ A then (if y ∈ A then ((univ \ A).card : ℝ) else 1)
  else (if y ∈ A then 1 else (A.card : ℝ))

private lemma reach_or {V : Type*} {G : SimpleGraph V} (hG : G.Connected) {a b : V}
    (v : V) : (G.deleteEdges {s(a, b)}).Reachable v a ∨
      (G.deleteEdges {s(a, b)}).Reachable v b := by
  have aux : ∀ {v w : V} (p : G.Walk v w), ((G.deleteEdges {s(a, b)}).Reachable w a ∨
      (G.deleteEdges {s(a, b)}).Reachable w b) → ((G.deleteEdges {s(a, b)}).Reachable v a ∨
      (G.deleteEdges {s(a, b)}).Reachable v b) := by
    intro v w p
    induction p with
    | nil => exact id
    | @cons v u _ h q ih =>
      intro hw
      by_cases he : s(v, u) = s(a, b)
      · rcases Sym2.eq_iff.mp he with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact Or.inl .rfl
        · exact Or.inr .rfl
      · have hadj : (G.deleteEdges {s(a, b)}).Adj v u := by
          simp [h, he]
        exact (ih hw).imp (hadj.reachable.trans ·) (hadj.reachable.trans ·)
  obtain ⟨p⟩ := hG.preconnected v a
  exact aux p (Or.inl .rfl)

private lemma not_reach {V : Type*} {G : SimpleGraph V} (hG : G.IsTree) {a b : V}
    (hab : G.Adj a b) : ¬ (G.deleteEdges {s(a, b)}).Reachable a b :=
  SimpleGraph.isBridge_iff.mp (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hG.isAcyclic hab)

private lemma mem_side {X : Type*} [Fintype X] {V : Type*} {G : SimpleGraph V} {ι : X → V}
    {a b : V} {z : X} : z ∈ side G ι a b ↔ (G.deleteEdges {s(a, b)}).Reachable (ι z) a := by
  classical
  simp [side]

/-- In a tree, the two sides of an edge partition the taxa. -/
theorem side_swap {X : Type*} [Fintype X] [DecidableEq X] {V : Type*} {G : SimpleGraph V}
    {ι : X → V} (hG : G.IsTree) {a b : V} (hab : G.Adj a b) :
    side G ι b a = univ \ side G ι a b := by
  ext z
  rw [Finset.mem_sdiff, mem_side, mem_side, Sym2.eq_swap]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro hb ha
    exact not_reach hG hab (ha.symm.trans hb)
  · intro ha
    exact (reach_or hG.connected (ι z)).resolve_left ha

/-- In a tree, the splits of any two edges are compatible: one side of the first edge lies
inside one side of the second. -/
theorem side_compat {X : Type*} [Fintype X] {V : Type*} {G : SimpleGraph V} {ι : X → V}
    (hG : G.IsTree) {a b c e : V} (hab : G.Adj a b) (hce : G.Adj c e) :
    side G ι b a ⊆ side G ι c e ∨ side G ι b a ⊆ side G ι e c ∨
      side G ι a b ⊆ side G ι c e ∨ side G ι a b ⊆ side G ι e c := by
  classical
  by_cases heq : s(c, e) = s(a, b)
  · rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl le_rfl))
    · exact Or.inl le_rfl
  -- `c` and `e` lie on the same side of `{a, b}`
  have hce' : (G.deleteEdges {s(a, b)}).Adj c e := by simp [hce, heq]
  -- the side of `{a, b}` away from `c`
  have key : ∀ {a b : V}, G.Adj a b → s(c, e) ≠ s(a, b) →
      (G.deleteEdges {s(a, b)}).Reachable c a →
      side G ι b a ⊆ side G ι c e ∨ side G ι b a ⊆ side G ι e c := by
    intro a b hab hne hca
    have hsub : ∀ z, z ∈ side G ι b a → (G.deleteEdges {s(c, e)}).Reachable (ι z) b := by
      intro z hz
      rw [mem_side, Sym2.eq_swap, SimpleGraph.reachable_deleteEdges_iff_exists_walk] at hz
      obtain ⟨q, hq⟩ := hz
      rw [SimpleGraph.reachable_deleteEdges_iff_exists_walk]
      refine ⟨q, fun hmem => ?_⟩
      have hc := q.fst_mem_support_of_mem_edges hmem
      have hcb : (G.deleteEdges {s(a, b)}).Reachable c b := by
        rw [SimpleGraph.reachable_deleteEdges_iff_exists_walk]
        exact ⟨q.dropUntil c hc, fun h => hq (q.edges_dropUntil_subset_edges hc h)⟩
      exact not_reach hG hab (hca.symm.trans hcb)
    rcases reach_or (a := c) (b := e) hG.connected b with hb | hb
    · left
      intro z hz
      rw [mem_side]
      exact (hsub z hz).trans hb
    · right
      intro z hz
      have hec : s(e, c) = s(c, e) := Sym2.eq_swap
      rw [mem_side, hec]
      exact (hsub z hz).trans hb
  rcases reach_or (a := a) (b := b) hG.connected c with hca | hcb
  · rcases key hab heq hca with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hba : s(b, a) = s(a, b) := Sym2.eq_swap
    rw [← hba] at heq hcb
    rcases key hab.symm heq hcb with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

/-- The leaf side of a pendant edge holds only the leaf's taxon. -/
theorem side_leaf {X : Type*} [Fintype X] {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {ι : X → V} (hT : IsBinaryPhylogeneticTree G ι) {z : X} {b : V}
    (hb : G.Adj (ι z) b) : side G ι (ι z) b = {z} := by
  ext z'
  rw [mem_side, Finset.mem_singleton]
  constructor
  · rintro ⟨q⟩
    have hdeg : G.degree (ι z) = 1 := (hT.2.2.1 (ι z)).mpr ⟨z, rfl⟩
    obtain ⟨b', -, hb'⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
    by_contra hne
    have hne' : ι z ≠ ι z' := fun h => hne (hT.2.1 h).symm
    obtain ⟨u, h, -, -⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hne' q.reverse
    rw [SimpleGraph.deleteEdges_adj] at h
    obtain ⟨h1, h2⟩ := h
    have := (hb' _ h1).trans (hb' _ hb).symm
    subst this
    exact h2 rfl
  · rintro rfl
    exact .rfl

private lemma mem_edges_iff {V : Type*} {G : SimpleGraph V} (hG : G.IsTree) {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) (a b : V) :
    s(a, b) ∈ p.edges ↔ ¬ (G.deleteEdges {s(a, b)}).Reachable u v := by
  classical
  constructor
  · intro hmem hr
    rw [SimpleGraph.reachable_deleteEdges_iff_exists_walk] at hr
    obtain ⟨q, hq⟩ := hr
    have := (hG.isAcyclic.subsingleton_path _ _).elim ⟨p, hp⟩ ⟨q.bypass, q.bypass_isPath⟩
    simp only [Subtype.mk.injEq] at this
    subst this
    exact hq (q.edges_bypass_subset_edges hmem)
  · intro hr
    by_contra hmem
    exact hr (SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨p, hmem⟩)

private lemma reach_of_reach {V : Type*} {G : SimpleGraph V} (hG : G.IsTree) {a b c v : V}
    (hac : G.Adj a c) (hcb : c ≠ b) (h : (G.deleteEdges {s(c, a)}).Reachable v c) :
    (G.deleteEdges {s(a, b)}).Reachable v a := by
  classical
  rw [SimpleGraph.reachable_deleteEdges_iff_exists_walk] at h
  obtain ⟨q, hq⟩ := h
  have hq' : s(a, b) ∉ q.edges := by
    intro hmem
    have ha := q.fst_mem_support_of_mem_edges hmem
    refine not_reach hG hac.symm ?_
    rw [SimpleGraph.reachable_deleteEdges_iff_exists_walk]
    refine ⟨(q.dropUntil a ha).reverse, fun h' => hq ?_⟩
    rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at h'
    exact q.edges_dropUntil_subset_edges ha h'
  have hr : (G.deleteEdges {s(a, b)}).Reachable v c :=
    SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨q, hq'⟩
  refine hr.trans (SimpleGraph.Adj.reachable ?_)
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨hac.symm, ?_⟩
  simp only [Set.mem_singleton_iff, Sym2.eq_iff]
  rintro (⟨rfl, -⟩ | ⟨rfl, -⟩)
  · exact hac.ne rfl
  · exact hcb rfl

private lemma side_subset {X : Type*} [Fintype X] {V : Type*} {G : SimpleGraph V} {ι : X → V}
    (hG : G.IsTree) {a b c : V} (hac : G.Adj a c) (hcb : c ≠ b) :
    side G ι c a ⊆ side G ι a b := by
  intro z hz
  rw [mem_side] at hz ⊢
  exact reach_of_reach hG hac hcb hz

/-- Every side of every edge of a binary phylogenetic tree holds a taxon. -/
theorem side_nonempty {X : Type*} [Fintype X] {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {ι : X → V} (hT : IsBinaryPhylogeneticTree G ι) {a b : V}
    (hab : G.Adj a b) : (side G ι a b).Nonempty := by
  classical
  -- strong induction on the number of vertices on the `a`-side
  suffices H : ∀ n, ∀ a b, G.Adj a b →
      (univ.filter fun v => (G.deleteEdges {s(a, b)}).Reachable v a).card = n →
      (side G ι a b).Nonempty from H _ a b hab rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hab hn
    by_cases ha : a ∈ Set.range ι
    · obtain ⟨z, rfl⟩ := ha
      exact ⟨z, mem_side.mpr .rfl⟩
    · have hdeg : G.degree a = 3 := hT.2.2.2 a ha
      obtain ⟨c, hc, hcb⟩ : ∃ c, G.Adj a c ∧ c ≠ b := by
        by_contra hcon
        simp only [not_exists, not_and, not_not] at hcon
        have hsub : G.neighborFinset a ⊆ {b} := fun c hc =>
          Finset.mem_singleton.mpr (hcon c ((G.mem_neighborFinset a c).mp hc))
        have := Finset.card_le_card hsub
        rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg, Finset.card_singleton] at this
        omega
      refine (ih _ ?_ c a hc.symm rfl).mono (side_subset hT.1 hc hcb)
      rw [← hn]
      apply Finset.card_lt_card
      refine ⟨fun v hv => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        exact reach_of_reach hT.1 hc hcb hv
      · have : a ∈ univ.filter fun v => (G.deleteEdges {s(c, a)}).Reachable v c :=
          hsub (by simp)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact not_reach hT.1 hc.symm this.symm

/-- At an internal vertex `a` with neighbor `b`, the `a`-side of `{a, b}` is the disjoint union
of the far sides of the other two edges at `a`. -/
theorem side_eq_union {X : Type*} [Fintype X] [DecidableEq X] {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {ι : X → V} (hT : IsBinaryPhylogeneticTree G ι)
    {a b : V} (ha : a ∉ Set.range ι) (hab : G.Adj a b) :
    ∃ c e, G.Adj a c ∧ G.Adj a e ∧ c ≠ b ∧ e ≠ b ∧ c ≠ e ∧
      Disjoint (side G ι c a) (side G ι e a) ∧ side G ι a b = side G ι c a ∪ side G ι e a := by
  classical
  have hdeg : (G.neighborFinset a).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hT.2.2.2 a ha
  have hbN : b ∈ G.neighborFinset a := (G.mem_neighborFinset a b).mpr hab
  have hcard : ((G.neighborFinset a).erase b).card = 2 := by
    rw [Finset.card_erase_of_mem hbN, hdeg]
  obtain ⟨c, e, hce, hN⟩ := Finset.card_eq_two.mp hcard
  have hc : c ∈ (G.neighborFinset a).erase b := by rw [hN]; simp
  have he : e ∈ (G.neighborFinset a).erase b := by rw [hN]; simp
  rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hc he
  refine ⟨c, e, hc.2, he.2, hc.1, he.1, hce, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro z hzc hze
    have h1 := side_subset (ι := ι) hT.1 he.2 (Ne.symm hce) hze
    rw [side_swap hT.1 hc.2] at hzc
    exact (Finset.mem_sdiff.mp hzc).2 h1
  · apply Finset.Subset.antisymm
    · intro z hz
      rw [mem_side] at hz
      have hza : ι z ≠ a := fun h => ha ⟨z, h⟩
      obtain ⟨p, hp⟩ : ∃ p : G.Walk (ι z) a, p.IsPath := by
        obtain ⟨q⟩ := hT.1.connected.preconnected (ι z) a
        exact ⟨q.bypass, q.bypass_isPath⟩
      obtain ⟨u, hu, p', hp'⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hza.symm p.reverse
      have hmem : s(u, a) ∈ p.edges := by
        have : s(a, u) ∈ p.reverse.edges := by rw [hp']; simp
        rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at this
        rwa [Sym2.eq_swap]
      have hnr := (mem_edges_iff hT.1 hp u a).mp hmem
      have huN : u ∈ G.neighborFinset a := (G.mem_neighborFinset a u).mpr hu
      by_cases hub : u = b
      · subst hub
        rw [Sym2.eq_swap] at hnr
        exact absurd hz hnr
      · have : u ∈ (G.neighborFinset a).erase b := Finset.mem_erase.mpr ⟨hub, huN⟩
        rw [hN] at this
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rw [Finset.mem_union, mem_side, mem_side]
        rcases this with rfl | rfl
        · exact Or.inl ((reach_or hT.1.connected (ι z)).resolve_right hnr)
        · exact Or.inr ((reach_or hT.1.connected (ι z)).resolve_right hnr)
    · exact Finset.union_subset (side_subset hT.1 hc.2 hc.1) (side_subset hT.1 he.2 he.1)

private lemma sameSide_iff {X : Type*} [Fintype X] {V : Type*} {G : SimpleGraph V}
    {ι : X → V} (hG : G.IsTree) (a b : V) (x y : X) :
    (x ∈ side G ι a b ↔ y ∈ side G ι a b) ↔
      (G.deleteEdges {s(a, b)}).Reachable (ι x) (ι y) := by
  rw [mem_side, mem_side]
  constructor
  · intro h
    by_cases hx : (G.deleteEdges {s(a, b)}).Reachable (ι x) a
    · exact hx.trans (h.mp hx).symm
    · have hy : ¬ (G.deleteEdges {s(a, b)}).Reachable (ι y) a := fun hy => hx (h.mpr hy)
      exact ((reach_or hG.connected _).resolve_left hx).trans
        ((reach_or hG.connected _).resolve_left hy).symm
  · intro h
    exact ⟨fun hx => h.symm.trans hx, fun hy => h.trans hy⟩

/-- **Split decomposition of a tree metric.** The path length between two taxa is half the sum,
over the darts (oriented edges) of the tree, of the lengths of the edges whose split separates
them. -/
theorem dist_eq_sum_darts {X : Type*} [Fintype X] [DecidableEq X] {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {ι : X → V} (hG : G.IsTree) {w : Sym2 V → ℝ}
    {d : X → X → ℝ}
    (hd : ∀ x y (p : G.Walk (ι x) (ι y)), p.IsPath → d x y = (p.edges.map w).sum) (x y : X) :
    d x y = (1 / 2) * ∑ t : G.Dart,
      w t.edge * (if (x ∈ side G ι t.fst t.snd ↔ y ∈ side G ι t.fst t.snd) then 0 else 1) := by
  classical
  obtain ⟨q⟩ := hG.connected.preconnected (ι x) (ι y)
  set p := q.bypass
  have hp : p.IsPath := q.bypass_isPath
  rw [hd x y p hp]
  set f : Sym2 V → ℝ := fun e => if e ∈ p.edges then w e else 0 with hf
  have hterm : ∀ t : G.Dart, w t.edge *
      (if (x ∈ side G ι t.fst t.snd ↔ y ∈ side G ι t.fst t.snd) then 0 else 1) = f t.edge := by
    intro t
    have h1 := sameSide_iff (ι := ι) hG t.fst t.snd x y
    have h2 := mem_edges_iff hG hp t.fst t.snd
    simp only [hf, SimpleGraph.Dart.edge]
    by_cases hr : (G.deleteEdges {s(t.fst, t.snd)}).Reachable (ι x) (ι y)
    · have h3 : s(t.fst, t.snd) ∉ p.edges := fun h => h2.mp h hr
      simp [h1.mpr hr, h3]
    · have h3 : ¬ (x ∈ side G ι t.fst t.snd ↔ y ∈ side G ι t.fst t.snd) := fun h => hr (h1.mp h)
      simp only [h3, h2.mpr hr, ite_false, ite_true]
      ring
  simp only [hterm]
  have hfib : ∑ t : G.Dart, f t.edge = ∑ e ∈ G.edgeFinset, 2 * f e := by
    rw [← Finset.sum_fiberwise_of_maps_to' (g := SimpleGraph.Dart.edge) (t := G.edgeFinset)
      (fun t _ => SimpleGraph.mem_edgeFinset.mpr t.edge_mem)]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [Finset.sum_const, nsmul_eq_mul,
      G.dart_edge_fiber_card e (SimpleGraph.mem_edgeFinset.mp he)]
    norm_num
  have hsum : ∑ e ∈ G.edgeFinset, f e = (p.edges.map w).sum := by
    rw [← List.sum_toFinset w hp.edges_nodup, hf, ← Finset.sum_filter]
    congr 1
    ext e
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, List.mem_toFinset,
      and_iff_right_iff_imp]
    exact fun he => p.edges_subset_edgeSet he
  rw [hfib, ← Finset.mul_sum, hsum]
  ring

/-! ### The cherry lemma for compatible binary split systems -/

/-- Compatibility of two sides in quadrant form: the four quadrants are not all inhabited. -/
private def Cpt {X : Type*} (A B : Finset X) : Prop :=
  ∀ a b c d, a ∈ A → a ∈ B → b ∈ A → b ∉ B → c ∉ A → c ∈ B → d ∉ A → d ∉ B → False

private lemma cpt_of {X : Type*} [Fintype X] [DecidableEq X] {A B : Finset X}
    (h : Disjoint A B ∨ A ⊆ B ∨ B ⊆ A ∨ A ∪ B = univ) : Cpt A B := by
  intro a b c d ha1 ha2 hb1 hb2 hc1 hc2 hd1 hd2
  rcases h with h | h | h | h
  · exact Finset.disjoint_left.mp h ha1 ha2
  · exact hb2 (h hb1)
  · exact hc1 (h hc2)
  · have : d ∈ A ∪ B := h ▸ Finset.mem_univ d
    rcases Finset.mem_union.mp this with h' | h'
    · exact hd1 h'
    · exact hd2 h'

private lemma Cpt.compl {X : Type*} [Fintype X] [DecidableEq X] {A B : Finset X}
    (h : Cpt A B) : Cpt (univ \ A) B := by
  intro a b c d ha1 ha2 hb1 hb2 hc1 hc2 hd1 hd2
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at ha1 hb1 hc1 hd1
  exact h c d a b hc1 hc2 hd1 hd2 ha1 ha2 hb1 hb2

private lemma splitGain_compl {X : Type*} [Fintype X] [DecidableEq X] (A : Finset X)
    (x y : X) : splitGain (univ \ A) x y = splitGain A x y := by
  by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;>
    simp [splitGain, hx, hy, Finset.sdiff_sdiff_eq_self (Finset.subset_univ A)]

private lemma splitGain_comm {X : Type*} [Fintype X] [DecidableEq X] (A : Finset X)
    (x y : X) : splitGain A x y = splitGain A y x := by
  by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> simp [splitGain, hx, hy]

private lemma one_le_splitGain {X : Type*} [Fintype X] [DecidableEq X] {A : Finset X}
    (hA : A.Nonempty) (hAc : (univ \ A).Nonempty) (x y : X) : 1 ≤ splitGain A x y := by
  have h1 : (1 : ℝ) ≤ A.card := by exact_mod_cast hA.card_pos
  have h2 : (1 : ℝ) ≤ (univ \ A).card := by exact_mod_cast hAc.card_pos
  by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> simp [splitGain, hx, hy, h1, h2]

/-- The comparison for one side `A` not containing `x, y`, in the case `|H| ≥ 2`. -/
private lemma gain_le_pair_aux {X : Type*} [Fintype X] [DecidableEq X] {A H P : Finset X}
    {x y p q : X} (hxP : x ∉ P) (hxH : x ∉ H) (hyP : y ∈ P) (hHP : Disjoint H P)
    (hcover : ∀ z, z = x ∨ z ∈ H ∨ z ∈ P) (hpH : p ∈ H) (hqH : q ∈ H)
    (hH : 2 * H.card ≤ Fintype.card X) (cAP : Cpt A P) (cAB : Cpt A {p, q})
    (hx : x ∉ A) (hy : y ∉ A) : splitGain A x y ≤ splitGain A p q := by
  have hxB : x ∉ ({p, q} : Finset X) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl) <;> contradiction
  have hpP : p ∉ P := Finset.disjoint_left.mp hHP hpH
  simp only [splitGain, hx, hy, ite_false]
  by_cases hp : p ∈ A <;> by_cases hq : q ∈ A
  · -- `A ⊆ H`, so `|A| ≤ n / 2`
    simp only [hp, hq, ite_true]
    have hAH : A ⊆ H := by
      intro z hz
      rcases hcover z with rfl | h | h
      · exact absurd hz hx
      · exact h
      · exact (cAP z p y x hz h hp hpP hy hyP hx hxP).elim
    have h1 := Finset.card_le_card hAH
    have h2 : (univ \ A).card + A.card = Fintype.card X := by
      rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A), Finset.card_univ]
    have : A.card ≤ (univ \ A).card := by omega
    exact_mod_cast this
  · -- `A = {p}`
    simp only [hp, hq, ite_true, ite_false]
    have : A ⊆ {p} := by
      intro z hz
      by_contra hzp
      rw [Finset.mem_singleton] at hzp
      have hzB : z ∉ ({p, q} : Finset X) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (h | rfl)
        · exact hzp h
        · exact hq hz
      exact cAB p z q x hp (by simp) hz hzB hq (by simp) hx hxB
    have := Finset.card_le_card this
    rw [Finset.card_singleton] at this
    exact_mod_cast this
  · simp only [hp, hq, ite_true, ite_false]
    have : A ⊆ {q} := by
      intro z hz
      by_contra hzq
      rw [Finset.mem_singleton] at hzq
      have hzB : z ∉ ({p, q} : Finset X) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (rfl | h)
        · exact hp hz
        · exact hzq h
      exact cAB q z p x hq (by simp) hz hzB hp (by simp) hx hxB
    have := Finset.card_le_card this
    rw [Finset.card_singleton] at this
    exact_mod_cast this
  · simp [hp, hq]

/-- The comparison for one side `A` not containing `x, y`, in the case `H = {z}`. -/
private lemma gain_le_single_aux {X : Type*} [Fintype X] [DecidableEq X] {A P : Finset X}
    {x y z : X} (hxP : x ∉ P) (hyP : y ∈ P) (hzP : z ∉ P)
    (hcover : ∀ t, t = x ∨ t = z ∨ t ∈ P) (cAP : Cpt A P)
    (hx : x ∉ A) (hy : y ∉ A) : splitGain A x y ≤ splitGain A x z := by
  simp only [splitGain, hx, hy, ite_false]
  by_cases hz : z ∈ A
  · simp only [hz, ite_true]
    have : A ⊆ {z} := by
      intro t ht
      rcases hcover t with rfl | rfl | h
      · exact absurd ht hx
      · simp
      · exact (cAP t z y x ht h hz hzP hy hyP hx hxP).elim
    have := Finset.card_le_card this
    rw [Finset.card_singleton] at this
    exact_mod_cast this
  · simp [hz]

private lemma gain_le_pair {X : Type*} [Fintype X] [DecidableEq X] {A H P : Finset X}
    {x y p q : X} (hA : A.Nonempty) (hAc : (univ \ A).Nonempty) (hxP : x ∉ P) (hxH : x ∉ H)
    (hyP : y ∈ P) (hHP : Disjoint H P) (hcover : ∀ z, z = x ∨ z ∈ H ∨ z ∈ P) (hpH : p ∈ H)
    (hqH : q ∈ H) (hH : 2 * H.card ≤ Fintype.card X) (cAP : Cpt A P) (cAB : Cpt A {p, q}) :
    splitGain A x y ≤ splitGain A p q := by
  by_cases hx : x ∈ A <;> by_cases hy : y ∈ A
  · rw [← splitGain_compl A x y, ← splitGain_compl A p q]
    exact gain_le_pair_aux hxP hxH hyP hHP hcover hpH hqH hH cAP.compl cAB.compl
      (by simp [hx]) (by simp [hy])
  · have : splitGain A x y = 1 := by simp [splitGain, hx, hy]
    rw [this]; exact one_le_splitGain hA hAc p q
  · have : splitGain A x y = 1 := by simp [splitGain, hx, hy]
    rw [this]; exact one_le_splitGain hA hAc p q
  · exact gain_le_pair_aux hxP hxH hyP hHP hcover hpH hqH hH cAP cAB hx hy

private lemma gain_le_single {X : Type*} [Fintype X] [DecidableEq X] {A P : Finset X}
    {x y z : X} (hA : A.Nonempty) (hAc : (univ \ A).Nonempty) (hxP : x ∉ P) (hyP : y ∈ P)
    (hzP : z ∉ P) (hcover : ∀ t, t = x ∨ t = z ∨ t ∈ P) (cAP : Cpt A P) :
    splitGain A x y ≤ splitGain A x z := by
  by_cases hx : x ∈ A <;> by_cases hy : y ∈ A
  · rw [← splitGain_compl A x y, ← splitGain_compl A x z]
    exact gain_le_single_aux hxP hyP hzP hcover cAP.compl (by simp [hx]) (by simp [hy])
  · have : splitGain A x y = 1 := by simp [splitGain, hx, hy]
    rw [this]; exact one_le_splitGain hA hAc x z
  · have : splitGain A x y = 1 := by simp [splitGain, hx, hy]
    rw [this]; exact one_le_splitGain hA hAc x z
  · exact gain_le_single_aux hxP hyP hzP hcover cAP hx hy

/-- **Cherry lemma for split systems.** For a compatible system of splits with positive weights,
containing every trivial split and binary (every side with at least two taxa is the disjoint
union of two sides), on at least four taxa, a pair maximizing the total `splitGain` is a
side of some split. -/
theorem exists_eq_pair_of_isMax {X : Type*} [Fintype X] [DecidableEq X] {E : Type*} [Fintype E]
    (A : E → Finset X) (w : E → ℝ) (hw : ∀ e, 0 < w e) (hne : ∀ e, (A e).Nonempty)
    (hcompl : ∀ e, ∃ e', A e' = univ \ A e)
    (hcompat : ∀ e e', Disjoint (A e) (A e') ∨ A e ⊆ A e' ∨ A e' ⊆ A e ∨ A e ∪ A e' = univ)
    (hbin : ∀ e, 2 ≤ (A e).card → ∃ e₁ e₂, Disjoint (A e₁) (A e₂) ∧ A e₁ ∪ A e₂ = A e)
    (hsingle : ∀ z, ∃ e, A e = {z}) (hX : 4 ≤ Fintype.card X) {x y : X} (hxy : x ≠ y)
    (hmax : ∀ x' y', x' ≠ y' →
      ∑ e, w e * splitGain (A e) x' y' ≤ ∑ e, w e * splitGain (A e) x y) :
    ∃ e, A e = {x, y} := by
  have hc : ∀ e e', Cpt (A e) (A e') := fun e e' => cpt_of (hcompat e e')
  have hAc : ∀ e, (univ \ A e).Nonempty := fun e => by
    obtain ⟨e', h⟩ := hcompl e
    rw [← h]
    exact hne e'
  -- the two branches at the neighbor of a leaf
  have decomp : ∀ u v : X, u ≠ v → ∃ eH eP, v ∈ A eP ∧ u ∉ A eH ∧ u ∉ A eP ∧
      Disjoint (A eH) (A eP) ∧ ∀ z, z = u ∨ z ∈ A eH ∨ z ∈ A eP := by
    intro u v huv
    obtain ⟨e₀, he₀⟩ := hsingle u
    obtain ⟨e₀', he₀'⟩ := hcompl e₀
    rw [he₀] at he₀'
    have hcard : 2 ≤ (A e₀').card := by
      rw [he₀', Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Finset.card_singleton]
      omega
    obtain ⟨e₁, e₂, hd, hu⟩ := hbin e₀' hcard
    have hsub : ∀ z, z ∈ A e₁ ∪ A e₂ ↔ z ≠ u := by
      intro z; rw [hu, he₀']; simp
    have hu1 : u ∉ A e₁ := fun h => (hsub u).mp (Finset.mem_union_left _ h) rfl
    have hu2 : u ∉ A e₂ := fun h => (hsub u).mp (Finset.mem_union_right _ h) rfl
    have hcov : ∀ z, z = u ∨ z ∈ A e₁ ∨ z ∈ A e₂ := by
      intro z
      by_cases hz : z = u
      · exact Or.inl hz
      · exact Or.inr (Finset.mem_union.mp ((hsub z).mpr hz))
    rcases Finset.mem_union.mp ((hsub v).mpr huv.symm) with hv | hv
    · exact ⟨e₂, e₁, hv, hu2, hu1, hd.symm, fun z => (hcov z).imp_right Or.symm⟩
    · exact ⟨e₁, e₂, hv, hu1, hu2, hd, hcov⟩
  -- a strictly better pair when the branch `H` at `u` away from `v` is small
  have improve : ∀ (u v : X) (eH eP : E), v ∈ A eP → u ∉ A eH → u ∉ A eP →
      Disjoint (A eH) (A eP) → (∀ z, z = u ∨ z ∈ A eH ∨ z ∈ A eP) → 2 ≤ (A eP).card →
      2 * (A eH).card ≤ Fintype.card X → ∃ u' v', u' ≠ v' ∧
        ∑ e, w e * splitGain (A e) u v < ∑ e, w e * splitGain (A e) u' v' := by
    intro u v eH eP hv hu hu' hd hcov hP2 hH2
    have hP1 : (1 : ℝ) < (A eP).card := by exact_mod_cast hP2
    by_cases h1 : (A eH).card = 1
    · obtain ⟨z, hz⟩ := Finset.card_eq_one.mp h1
      have hzH : z ∈ A eH := by rw [hz]; simp
      have hzP : z ∉ A eP := Finset.disjoint_left.mp hd hzH
      have huz : u ≠ z := fun h => hu (h ▸ hzH)
      refine ⟨u, z, huz, Finset.sum_lt_sum (fun e _ => ?_) ⟨eP, Finset.mem_univ _, ?_⟩⟩
      · refine mul_le_mul_of_nonneg_left ?_ (hw e).le
        refine gain_le_single (hne e) (hAc e) hu' hv hzP (fun t => ?_) (hc e eP)
        rcases hcov t with h | h | h
        · exact Or.inl h
        · rw [hz, Finset.mem_singleton] at h; exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · refine mul_lt_mul_of_pos_left ?_ (hw eP)
        simpa [splitGain, hu', hv, hzP] using hP1
    · have h2 : 2 ≤ (A eH).card := by
        have := (hne eH).card_pos
        omega
      obtain ⟨eB, heB, hmin⟩ := (univ.filter fun e => A e ⊆ A eH ∧ 2 ≤ (A e).card).exists_min_image
        (fun e => (A e).card) ⟨eH, by simp [h2]⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heB hmin
      obtain ⟨e₁, e₂, hd12, hu12⟩ := hbin eB heB.2
      have hcard := Finset.card_union_of_disjoint hd12
      rw [hu12] at hcard
      have p1 := (hne e₁).card_pos
      have p2 := (hne e₂).card_pos
      have c1 : (A e₁).card ≤ 1 := by
        by_contra hc1
        have := hmin e₁ ⟨(hu12 ▸ Finset.subset_union_left).trans heB.1, by omega⟩
        omega
      have c2 : (A e₂).card ≤ 1 := by
        by_contra hc2
        have := hmin e₂ ⟨(hu12 ▸ Finset.subset_union_right).trans heB.1, by omega⟩
        omega
      obtain ⟨p, q, hpq, hB⟩ := Finset.card_eq_two.mp (show (A eB).card = 2 by omega)
      have hpH : p ∈ A eH := heB.1 (by rw [hB]; simp)
      have hqH : q ∈ A eH := heB.1 (by rw [hB]; simp)
      have hpP : p ∉ A eP := Finset.disjoint_left.mp hd hpH
      have hqP : q ∉ A eP := Finset.disjoint_left.mp hd hqH
      refine ⟨p, q, hpq, Finset.sum_lt_sum (fun e _ => ?_) ⟨eP, Finset.mem_univ _, ?_⟩⟩
      · refine mul_le_mul_of_nonneg_left ?_ (hw e).le
        exact gain_le_pair (hne e) (hAc e) hu' hu hv hd hcov hpH hqH (by omega) (hc e eP)
          (hB ▸ hc e eB)
      · refine mul_lt_mul_of_pos_left ?_ (hw eP)
        simpa [splitGain, hu', hv, hpP, hqP] using hP1
  by_contra hnot
  obtain ⟨eH, eP, hyP, hxH, hxP, hHP, hcov⟩ := decomp x y hxy
  obtain ⟨eH', eP', hxP', hyH', hyP', hHP', hcov'⟩ := decomp y x hxy.symm
  have hxH' : x ∉ A eH' := fun h => Finset.disjoint_left.mp hHP' h hxP'
  have hyH : y ∉ A eH := fun h => Finset.disjoint_left.mp hHP h hyP
  -- the two small branches are disjoint
  have hdisj : Disjoint (A eH) (A eH') := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    have hzP : z ∉ A eP := Finset.disjoint_left.mp hHP hz
    have hzP' : z ∉ A eP' := Finset.disjoint_left.mp hHP' hz'
    have h1 : A eH' ⊆ A eH := by
      intro t ht
      rcases hcov t with rfl | h | h
      · exact absurd ht hxH'
      · exact h
      · exact (hc eH' eP t z y x ht h hz' hzP hyH' hyP hxH' hxP).elim
    have h2 : A eH ⊆ A eH' := by
      intro t ht
      rcases hcov' t with rfl | h | h
      · exact absurd ht hyH
      · exact h
      · exact (hc eH eP' t z x y ht h hz hzP' hxH hxP' hyH hyP').elim
    have heq : A eH = A eH' := Finset.Subset.antisymm h2 h1
    by_cases hex : ∃ t, t ≠ x ∧ t ≠ y ∧ t ∉ A eH
    · obtain ⟨t, htx, hty, htH⟩ := hex
      have htP : t ∈ A eP := ((hcov t).resolve_left htx).resolve_left htH
      have htP' : t ∈ A eP' := ((hcov' t).resolve_left hty).resolve_left (heq ▸ htH)
      exact hc eP eP' t y x z htP htP' hyP hyP' hxP hxP' hzP hzP'
    · obtain ⟨e', he'⟩ := hcompl eH
      refine hnot ⟨e', ?_⟩
      rw [he']
      ext t
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro htH
        by_contra hxy'
        rw [not_or] at hxy'
        exact hex ⟨t, hxy'.1, hxy'.2, htH⟩
      · rintro (rfl | rfl)
        · exact hxH
        · exact hyH
  have hH'P : A eH' ⊆ A eP := by
    intro t ht
    rcases hcov t with rfl | h | h
    · exact absurd ht hxH'
    · exact absurd ht (Finset.disjoint_left.mp hdisj h)
    · exact h
  have hHsP' : A eH ⊆ A eP' := by
    intro t ht
    rcases hcov' t with rfl | h | h
    · exact absurd ht hyH
    · exact absurd h (Finset.disjoint_left.mp hdisj ht)
    · exact h
  have hP2 : 2 ≤ (A eP).card := by
    have := Finset.card_le_card (Finset.insert_subset hyP hH'P)
    rw [Finset.card_insert_of_notMem hyH'] at this
    have := (hne eH').card_pos
    omega
  have hP2' : 2 ≤ (A eP').card := by
    have := Finset.card_le_card (Finset.insert_subset hxP' hHsP')
    rw [Finset.card_insert_of_notMem hxH] at this
    have := (hne eH).card_pos
    omega
  have hsum : (A eH).card + (A eH').card + 2 ≤ Fintype.card X := by
    have hsub : A eH ∪ A eH' ⊆ univ \ {x, y} := by
      intro t ht
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, not_or]
      rcases Finset.mem_union.mp ht with h | h
      · exact ⟨fun h' => hxH (h' ▸ h), fun h' => hyH (h' ▸ h)⟩
      · exact ⟨fun h' => hxH' (h' ▸ h), fun h' => hyH' (h' ▸ h)⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Finset.card_pair hxy] at this
    omega
  by_cases hle : (A eH).card ≤ (A eH').card
  · obtain ⟨u', v', huv, hlt⟩ := improve x y eH eP hyP hxH hxP hHP hcov hP2 (by omega)
    exact absurd (hmax u' v' huv) (not_le.mpr hlt)
  · obtain ⟨u', v', huv, hlt⟩ := improve y x eH' eP' hxP' hyH' hyP' hHP' hcov' hP2' (by omega)
    simp only [splitGain_comm _ y x] at hlt
    exact absurd (hmax u' v' huv) (not_le.mpr hlt)

/-! ### The Q-criterion as a sum over splits -/

/-- The Q-criterion of two singleton clusters at the start of neighbor joining:
`Q({x}, {y}) = (|X| - 2) d x y - ∑_z d x z - ∑_z d y z`. -/
theorem qCriterion_singleton {X : Type*} [Fintype X] [DecidableEq X] (d : X → X → ℝ)
    (x y : X) :
    qCriterion (univ.image fun x => ({x} : Finset X)) (initialDist d) {x} {y} =
      ((Fintype.card X : ℝ) - 2) * d x y - ∑ z, d x z - ∑ z, d y z := by
  have hinj : Set.InjOn (fun x : X => ({x} : Finset X)) (univ : Finset X) :=
    fun a _ b _ h => Finset.singleton_injective h
  simp [qCriterion, initialDist, Finset.card_image_of_injective _ Finset.singleton_injective,
    Finset.sum_image hinj]

private lemma sum_sep {X : Type*} [Fintype X] [DecidableEq X] (A : Finset X) (x : X) :
    ∑ z, (if (x ∈ A ↔ z ∈ A) then (0 : ℝ) else 1) =
      if x ∈ A then ((univ \ A).card : ℝ) else (A.card : ℝ) := by
  have h1 : ∀ B : Finset X, ∑ z, (if z ∈ B then (1 : ℝ) else 0) = (B.card : ℝ) := by
    intro B
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  by_cases hx : x ∈ A
  · simp only [hx, ite_true]
    rw [← h1]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hz : z ∈ A <;> simp [hz]
  · simp only [hx, ite_false]
    rw [← h1]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hz : z ∈ A <;> simp [hz]

private lemma card_add_card_sdiff {X : Type*} [Fintype X] [DecidableEq X] (A : Finset X) :
    (A.card : ℝ) + ((univ \ A).card : ℝ) = Fintype.card X := by
  rw [← Nat.cast_add, Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ,
    Nat.add_sub_cancel' (Finset.card_le_univ A)]

/-- **The Q-criterion of a split-decomposed dissimilarity.** If `d x y` is half the total
weight of the splits `A e` separating `x` and `y`, then
`(|X| - 2) d x y - ∑_z d x z - ∑_z d y z = -∑ e, w e * splitGain (A e) x y`. -/
theorem sub_sum_sub_sum_eq_neg_sum_splitGain {X : Type*} [Fintype X] [DecidableEq X] {E : Type*}
    [Fintype E] (A : E → Finset X) (w : E → ℝ) {d : X → X → ℝ}
    (hd : ∀ x y, d x y = (1 / 2) * ∑ e, w e * (if (x ∈ A e ↔ y ∈ A e) then 0 else 1))
    (x y : X) :
    ((Fintype.card X : ℝ) - 2) * d x y - ∑ z, d x z - ∑ z, d y z =
      -∑ e, w e * splitGain (A e) x y := by
  have key : ∀ u, ∑ z, d u z = (1 / 2) * ∑ e, w e *
      (if u ∈ A e then ((univ \ A e).card : ℝ) else ((A e).card : ℝ)) := by
    intro u
    simp only [hd]
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.mul_sum, sum_sep]
  rw [key x, key y, hd x y]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hc := card_add_card_sdiff (A e)
  by_cases hx : x ∈ A e <;> by_cases hy : y ∈ A e <;>
    simp only [hx, hy, splitGain, iff_true, iff_false, iff_self, ite_true, ite_false,
      not_true_eq_false] <;>
    first | ring1 | linear_combination (-(w e) / 2) * hc

/-! ### Neighbor joining on a compatible binary split system -/

/-- The axioms of the split system of a binary phylogenetic tree used below. -/
private structure SplitSys {X : Type*} [Fintype X] [DecidableEq X] {E : Type*}
    (A : E → Finset X) : Prop where
  ne : ∀ e, (A e).Nonempty
  compl : ∀ e, ∃ e', A e' = univ \ A e
  compat : ∀ e e', Disjoint (A e) (A e') ∨ A e ⊆ A e' ∨ A e' ⊆ A e ∨ A e ∪ A e' = univ
  bin : ∀ e, 2 ≤ (A e).card → ∃ e₁ e₂, Disjoint (A e₁) (A e₂) ∧ A e₁ ∪ A e₂ = A e
  single : ∀ z, ∃ e, A e = {z}

/-- `S` partitions the taxa into sides of the split system. -/
private structure IsPart {X : Type*} {E : Type*} (A : E → Finset X)
    (S : Finset (Finset X)) : Prop where
  side : ∀ s ∈ S, ∃ e, A e = s
  disj : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → Disjoint s t
  cover : ∀ x, ∃ s ∈ S, x ∈ s

/-- `1` for each way the split `B` separates the clusters `s` and `t`. -/
private noncomputable def sepI {X : Type*} [Fintype X] [DecidableEq X] (B s t : Finset X) : ℝ :=
  (if s ⊆ B ∧ t ⊆ univ \ B then 1 else 0) + (if t ⊆ B ∧ s ⊆ univ \ B then 1 else 0)

/-- The tree distance between two clusters: the total weight of the splits separating them. -/
private noncomputable def treeD {X : Type*} [Fintype X] [DecidableEq X] {E : Type*} [Fintype E]
    (A : E → Finset X) (w : E → ℝ) (s t : Finset X) : ℝ :=
  (1 / 2) * ∑ e, w e * sepI (A e) s t

private lemma not_out_of_in {X : Type*} [Fintype X] [DecidableEq X] {B s : Finset X}
    (hs : s.Nonempty) (h : s ⊆ B) : ¬ s ⊆ univ \ B := by
  intro h'
  obtain ⟨x, hx⟩ := hs
  exact (Finset.mem_sdiff.mp (h' hx)).2 (h hx)

private lemma in_or_out_of_cpt {X : Type*} [Fintype X] [DecidableEq X] {B r s : Finset X}
    (hc : Cpt B r) (hrs : Disjoint r s) (h1 : ¬ r ⊆ B) (h2 : ¬ r ⊆ univ \ B) :
    (s ⊆ B ∧ ∀ t, Disjoint r t → t ⊆ B) ∨ (s ⊆ univ \ B ∧ ∀ t, Disjoint r t → t ⊆ univ \ B) := by
  obtain ⟨u, hur, huB⟩ := Finset.not_subset.mp h1
  obtain ⟨v, hvr, hvB⟩ := Finset.not_subset.mp h2
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hvB
  -- either `B ⊆ r` or `univ \ B ⊆ r`
  by_cases hB : ∃ t, t ∈ B ∧ t ∉ r
  · obtain ⟨t, htB, htr⟩ := hB
    -- then every element outside `B` lies in `r`
    have hout : ∀ z, z ∉ B → z ∈ r := by
      intro z hzB
      by_contra hzr
      exact hc v t u z hvB hvr htB htr huB hur hzB hzr
    left
    have key : ∀ t, Disjoint r t → t ⊆ B := by
      intro t' ht' z hz
      by_contra hzB
      exact Finset.disjoint_left.mp ht' (hout z hzB) hz
    exact ⟨key s hrs, key⟩
  · push Not at hB
    right
    have key : ∀ t, Disjoint r t → t ⊆ univ \ B := by
      intro t' ht' z hz
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      intro hzB
      exact Finset.disjoint_left.mp ht' (hB z hzB) hz
    exact ⟨key s hrs, key⟩

/-- The split identity behind the neighbor-joining distance update. -/
private lemma sepI_union {X : Type*} [Fintype X] [DecidableEq X] {B a b c : Finset X}
    (ha : a.Nonempty) (hb : b.Nonempty) (hc : c.Nonempty) (hab : Disjoint a b)
    (hac : Disjoint a c) (hbc : Disjoint b c) (cBa : Cpt B a) (cBb : Cpt B b)
    (cBU : Cpt B (a ∪ b)) :
    2 * sepI B (a ∪ b) c = sepI B a c + sepI B b c - sepI B a b := by
  have hna := not_out_of_in (B := B) ha
  have hnb := not_out_of_in (B := B) hb
  have hnc := not_out_of_in (B := B) hc
  have hna' : a ⊆ univ \ B → ¬ a ⊆ B := fun h h' => hna h' h
  have hnb' : b ⊆ univ \ B → ¬ b ⊆ B := fun h h' => hnb h' h
  have hnc' : c ⊆ univ \ B → ¬ c ⊆ B := fun h h' => hnc h' h
  unfold sepI
  simp only [Finset.union_subset_iff]
  by_cases hai : a ⊆ B
  · by_cases hbi : b ⊆ B
    · simp only [hai, hbi, hna hai, hnb hbi, true_and, and_false, ite_false]
      split_ifs <;> norm_num
    · by_cases hbo : b ⊆ univ \ B
      · -- `a ∪ b` is split by `B`, so `c` lies on one side
        have hcio : c ⊆ B ∨ c ⊆ univ \ B := by
          rcases in_or_out_of_cpt (s := c) cBU (Finset.disjoint_union_left.mpr ⟨hac, hbc⟩)
            (fun h => hbi (Finset.union_subset_iff.mp h).2)
            (fun h => hna hai (Finset.union_subset_iff.mp h).1) with h | h
          · exact Or.inl h.1
          · exact Or.inr h.1
        rcases hcio with h | h
        · simp only [hai, hbi, hbo, hna hai, h, hnc h, and_false,
            and_true, ite_false, ite_true]
          norm_num
        · simp only [hai, hbi, hbo, hna hai, h, hnc' h, and_false,
            and_true, ite_false, ite_true]
          norm_num
      · rcases in_or_out_of_cpt (s := c) cBb hbc hbi hbo with h | h
        · simp only [hai, hbi, hbo, hna hai, h.1, hnc h.1, and_false,
            ite_false]
          norm_num
        · exact absurd hai (hna' (h.2 a hab.symm))
  · by_cases hao : a ⊆ univ \ B
    · by_cases hbo : b ⊆ univ \ B
      · simp only [hai, hao, hbo, hnb' hbo, true_and, false_and, and_false, ite_false]
        split_ifs <;> norm_num
      · by_cases hbi : b ⊆ B
        · have hcio : c ⊆ B ∨ c ⊆ univ \ B := by
            rcases in_or_out_of_cpt (s := c) cBU (Finset.disjoint_union_left.mpr ⟨hac, hbc⟩)
              (fun h => hai (Finset.union_subset_iff.mp h).1)
              (fun h => hbo (Finset.union_subset_iff.mp h).2) with h | h
            · exact Or.inl h.1
            · exact Or.inr h.1
          rcases hcio with h | h
          · simp only [hai, hbi, hbo, hao, h, hnc h, and_false,
              and_true, ite_false, ite_true]
            norm_num
          · simp only [hai, hbi, hbo, hao, h, hnc' h, and_false,
              and_true, ite_false, ite_true]
            norm_num
        · rcases in_or_out_of_cpt (s := c) cBb hbc hbi hbo with h | h
          · exact absurd (h.2 a hab.symm) hai
          · simp only [hai, hbi, hbo, hao, h.1, hnc' h.1, and_false,
              and_true, ite_false]
            norm_num
    · -- `a` is split by `B`: `b` and `c` lie on the same side
      rcases in_or_out_of_cpt (s := c) cBa hac hai hao with h | h
      · have hbB := h.2 b hab
        simp only [hai, hao, hbB, hnb hbB, h.1, hnc h.1, and_false,
          and_true, ite_false]
        norm_num
      · have hbB := h.2 b hab
        simp only [hai, hao, hbB, hnb' hbB, h.1, hnc' h.1, and_false,
          and_true, ite_false]
        norm_num

private lemma treeD_union {X : Type*} [Fintype X] [DecidableEq X] {E : Type*} [Fintype E]
    {A : E → Finset X} (w : E → ℝ) (hA : SplitSys A) {a b c : Finset X} {ea eb eU : E}
    (hea : A ea = a) (heb : A eb = b) (heU : A eU = a ∪ b) (hc : c.Nonempty)
    (hab : Disjoint a b) (hac : Disjoint a c) (hbc : Disjoint b c) :
    treeD A w (a ∪ b) c = (treeD A w a c + treeD A w b c - treeD A w a b) / 2 := by
  have h : ∀ e, w e * (2 * sepI (A e) (a ∪ b) c) =
      w e * sepI (A e) a c + w e * sepI (A e) b c - w e * sepI (A e) a b := by
    intro e
    rw [sepI_union (hea ▸ hA.ne ea) (heb ▸ hA.ne eb) hc hab hac hbc
      (hea ▸ cpt_of (hA.compat e ea)) (heb ▸ cpt_of (hA.compat e eb))
      (heU ▸ cpt_of (hA.compat e eU))]
    ring
  have hs := Finset.sum_congr rfl (fun e (_ : e ∈ (univ : Finset E)) => h e)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_left_comm (w _) 2,
    ← Finset.mul_sum] at hs
  unfold treeD
  linear_combination (1 / 4 : ℝ) * hs

universe u in
/-- The reduction of a split system to a partition `S` into sides: the splits cutting no
cluster, read on the clusters, form a split system of the same kind on the clusters, and the
tree distance between clusters is half the total weight of the reduced splits separating
them. -/
private lemma reduce {X : Type*} [Fintype X] [DecidableEq X] {E : Type u} [Fintype E]
    {A : E → Finset X} (hA : SplitSys A) {S : Finset (Finset X)} (hS : IsPart A S)
    (w : E → ℝ) :
    ∃ (E' : Type u) (_ : Fintype E') (g : E' → E) (A' : E' → Finset {s // s ∈ S}),
      SplitSys A' ∧ (∀ e s, s ∈ A' e ↔ (s : Finset X) ⊆ A (g e)) ∧
      (∀ e x, x ∈ A (g e) ↔ ∃ s, s ∈ A' e ∧ x ∈ (s : Finset X)) ∧
      ∀ s t : {s // s ∈ S}, treeD A w s t =
        (1 / 2) * ∑ e, w (g e) * (if (s ∈ A' e ↔ t ∈ A' e) then 0 else 1) := by
  classical
  have hSne : ∀ s ∈ S, s.Nonempty := fun s hs => by
    obtain ⟨e, he⟩ := hS.side s hs
    exact he ▸ hA.ne e
  have hAc : ∀ e, (univ \ A e).Nonempty := fun e => by
    obtain ⟨e', h⟩ := hA.compl e
    rw [← h]
    exact hA.ne e'
  -- active splits: no cluster is split
  let act : E → Prop := fun e => ∀ s ∈ S, s ⊆ A e ∨ s ⊆ univ \ A e
  let Y := {s // s ∈ S}
  let E' := {e // act e}
  let A' : E' → Finset Y := fun e => univ.filter fun s => (s : Finset X) ⊆ A e.1
  have hmemA' : ∀ (e : E') (s : Y), s ∈ A' e ↔ (s : Finset X) ⊆ A e.1 := by
    intro e s; simp [A']
  have hout : ∀ (e : E') (s : Y), (s : Finset X) ⊆ univ \ A e.1 ↔ s ∉ A' e := by
    intro e s
    rw [hmemA']
    constructor
    · exact fun h h' => not_out_of_in (hSne s s.2) h' h
    · exact fun h => (e.2 s s.2).resolve_left h
  have hcov : ∀ (e : E') (x : X), x ∈ A e.1 ↔ ∃ s : Y, s ∈ A' e ∧ x ∈ (s : Finset X) := by
    intro e x
    constructor
    · intro hx
      obtain ⟨s, hs, hxs⟩ := hS.cover x
      refine ⟨⟨s, hs⟩, (hmemA' _ _).mpr ?_, hxs⟩
      rcases e.2 s hs with h | h
      · exact h
      · exact absurd hx (Finset.mem_sdiff.mp (h hxs)).2
    · rintro ⟨s, hs, hxs⟩
      exact (hmemA' _ _).mp hs hxs
  -- the side of a cluster is active and reduces to that cluster
  have hsingle : ∀ s : Y, ∃ e : E', A' e = {s} := by
    intro s
    obtain ⟨e, he⟩ := hS.side s s.2
    have hact : act e := by
      intro t ht
      by_cases hts : t = s
      · exact Or.inl (hts ▸ he.symm ▸ le_rfl)
      · right
        intro z hz
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, he]
        exact fun hz' => Finset.disjoint_left.mp (hS.disj t ht s s.2 hts) hz hz'
    refine ⟨⟨e, hact⟩, ?_⟩
    ext t
    rw [hmemA', Finset.mem_singleton]
    constructor
    · intro h
      by_contra hts
      have hts' : (t : Finset X) ≠ s := fun h' => hts (Subtype.ext h')
      obtain ⟨z, hz⟩ := hSne t t.2
      exact Finset.disjoint_left.mp (hS.disj t t.2 s s.2 hts') hz (he ▸ h hz)
    · rintro rfl
      exact he.symm ▸ le_rfl
  have hne' : ∀ e : E', (A' e).Nonempty := by
    intro e
    obtain ⟨x, hx⟩ := hA.ne e.1
    obtain ⟨s, hs, -⟩ := (hcov e x).mp hx
    exact ⟨s, hs⟩
  have hcompl' : ∀ e : E', ∃ e', A' e' = univ \ A' e := by
    intro e
    obtain ⟨e', he'⟩ := hA.compl e.1
    have hact : act e' := by
      intro s hs
      rw [he', Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)]
      exact (e.2 s hs).symm
    refine ⟨⟨e', hact⟩, ?_⟩
    ext s
    rw [hmemA', Finset.mem_sdiff, ← hout]
    simp [he']
  have hcompat' : ∀ e e' : E', Disjoint (A' e) (A' e') ∨ A' e ⊆ A' e' ∨ A' e' ⊆ A' e ∨
      A' e ∪ A' e' = univ := by
    intro e e'
    rcases hA.compat e.1 e'.1 with h | h | h | h
    · left
      rw [Finset.disjoint_left]
      intro s hs hs'
      obtain ⟨z, hz⟩ := hSne s s.2
      exact Finset.disjoint_left.mp h ((hmemA' _ _).mp hs hz) ((hmemA' _ _).mp hs' hz)
    · right; left
      intro s hs
      exact (hmemA' _ _).mpr (((hmemA' _ _).mp hs).trans h)
    · right; right; left
      intro s hs
      exact (hmemA' _ _).mpr (((hmemA' _ _).mp hs).trans h)
    · right; right; right
      ext s
      simp only [Finset.mem_union, Finset.mem_univ, iff_true]
      by_contra hs
      rw [not_or, ← hout, ← hout] at hs
      obtain ⟨z, hz⟩ := hSne s s.2
      have : z ∈ A e.1 ∪ A e'.1 := h ▸ Finset.mem_univ z
      rcases Finset.mem_union.mp this with h' | h'
      · exact (Finset.mem_sdiff.mp (hs.1 hz)).2 h'
      · exact (Finset.mem_sdiff.mp (hs.2 hz)).2 h'
  have hbin' : ∀ e : E', 2 ≤ (A' e).card →
      ∃ e₁ e₂, Disjoint (A' e₁) (A' e₂) ∧ A' e₁ ∪ A' e₂ = A' e := by
    intro e h2
    obtain ⟨s₁, hs₁, s₂, hs₂, hs12⟩ := Finset.one_lt_card.mp h2
    rw [hmemA'] at hs₁ hs₂
    have hs12' : (s₁ : Finset X) ≠ s₂ := fun h => hs12 (Subtype.ext h)
    have hd12 := hS.disj s₁ s₁.2 s₂ s₂.2 hs12'
    have hcardA : 2 ≤ (A e.1).card := by
      have := Finset.card_le_card (Finset.union_subset hs₁ hs₂)
      rw [Finset.card_union_of_disjoint hd12] at this
      have := (hSne s₁ s₁.2).card_pos
      have := (hSne s₂ s₂.2).card_pos
      omega
    obtain ⟨e₁, e₂, hd, hu⟩ := hA.bin e.1 hcardA
    -- a cluster inside `A e` lies inside `A e₁` or inside `A e₂`
    have hin : ∀ s ∈ S, s ⊆ A e.1 → s ⊆ A e₁ ∨ s ⊆ A e₂ := by
      intro s hs hsA
      by_contra hcon
      rw [not_or] at hcon
      obtain ⟨u₁, hu₁s, hu₁⟩ := Finset.not_subset.mp hcon.1
      obtain ⟨u₂, hu₂s, hu₂⟩ := Finset.not_subset.mp hcon.2
      have hu₁2 : u₁ ∈ A e₂ := by
        have := hsA hu₁s; rw [← hu] at this
        exact (Finset.mem_union.mp this).resolve_left hu₁
      have hu₂1 : u₂ ∈ A e₁ := by
        have := hsA hu₂s; rw [← hu] at this
        exact (Finset.mem_union.mp this).resolve_right hu₂
      obtain ⟨o, ho⟩ := hAc e.1
      have ho' : o ∉ A e.1 := (Finset.mem_sdiff.mp ho).2
      have hos : o ∉ s := fun h => ho' (hsA h)
      obtain ⟨es, hes⟩ := hS.side s hs
      have c1 := hes ▸ cpt_of (hA.compat e₁ es)
      have c2 := hes ▸ cpt_of (hA.compat e₂ es)
      -- `A e₁ ⊆ s` and `A e₂ ⊆ s`
      have h1 : A e₁ ⊆ s := by
        intro z hz
        by_contra hzs
        exact c1 u₂ z u₁ o hu₂1 hu₂s hz hzs hu₁ hu₁s
          (fun h => ho' (hu ▸ Finset.mem_union_left _ h)) hos
      have h2 : A e₂ ⊆ s := by
        intro z hz
        by_contra hzs
        exact c2 u₁ z u₂ o hu₁2 hu₁s hz hzs hu₂ hu₂s
          (fun h => ho' (hu ▸ Finset.mem_union_right _ h)) hos
      have hsA' : A e.1 ⊆ s := hu ▸ Finset.union_subset h1 h2
      -- but `A e` holds two clusters
      have hne1 : (s₁ : Finset X) ≠ s ∨ (s₂ : Finset X) ≠ s := by
        by_contra h'
        rw [not_or, not_not, not_not] at h'
        exact hs12' (h'.1.trans h'.2.symm)
      rcases hne1 with h' | h'
      · obtain ⟨z, hz⟩ := hSne s₁ s₁.2
        exact Finset.disjoint_left.mp (hS.disj s₁ s₁.2 s hs h') hz (hsA' (hs₁ hz))
      · obtain ⟨z, hz⟩ := hSne s₂ s₂.2
        exact Finset.disjoint_left.mp (hS.disj s₂ s₂.2 s hs h') hz (hsA' (hs₂ hz))
    have hsub1 : A e₁ ⊆ A e.1 := hu ▸ Finset.subset_union_left
    have hsub2 : A e₂ ⊆ A e.1 := hu ▸ Finset.subset_union_right
    have hact : ∀ e₀, A e₀ ⊆ A e.1 → (∀ s ∈ S, s ⊆ A e.1 → s ⊆ A e₁ ∨ s ⊆ A e₂) →
        (e₀ = e₁ ∨ e₀ = e₂) → act e₀ := by
      intro e₀ hsub _ h0 s hs
      rcases e.2 s hs with h | h
      · rcases hin s hs h with h' | h'
        · rcases h0 with rfl | rfl
          · exact Or.inl h'
          · right; intro z hz
            simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
            exact fun hz' => Finset.disjoint_left.mp hd (h' hz) hz'
        · rcases h0 with rfl | rfl
          · right; intro z hz
            simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
            exact fun hz' => Finset.disjoint_left.mp hd hz' (h' hz)
          · exact Or.inl h'
      · right
        exact h.trans (Finset.sdiff_subset_sdiff le_rfl hsub)
    refine ⟨⟨e₁, hact e₁ hsub1 hin (Or.inl rfl)⟩, ⟨e₂, hact e₂ hsub2 hin (Or.inr rfl)⟩, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro s hs1 hs2
      rw [hmemA'] at hs1 hs2
      obtain ⟨z, hz⟩ := hSne s s.2
      exact Finset.disjoint_left.mp hd (hs1 hz) (hs2 hz)
    · ext s
      simp only [Finset.mem_union, hmemA']
      constructor
      · rintro (h | h)
        · exact h.trans hsub1
        · exact h.trans hsub2
      · exact hin s s.2
  -- the tree distance in reduced form
  have hsep : ∀ (s t : Y), treeD A w s t = (1 / 2) * ∑ e : E', w e.1 *
      (if (s ∈ A' e ↔ t ∈ A' e) then 0 else 1) := by
    intro s t
    unfold treeD
    congr 1
    rw [← Fintype.sum_subtype_add_sum_subtype act]
    have hinact : ∀ e : {e // ¬ act e}, w e.1 * sepI (A e.1) s t = 0 := by
      intro e
      have he := e.2
      simp only [act, not_forall, not_or] at he
      obtain ⟨r, hr, hr1, hr2⟩ := he
      obtain ⟨er, her⟩ := hS.side r hr
      have cr := her ▸ cpt_of (hA.compat e.1 er)
      have key : ∀ u ∈ S, (u ⊆ A e.1 → u ≠ r ∧ ∀ v ∈ S, v ≠ r → ¬ v ⊆ univ \ A e.1) := by
        intro u hu huA
        have hur : u ≠ r := fun h => hr1 (h ▸ huA)
        refine ⟨hur, fun v hv hvr hvO => ?_⟩
        rcases in_or_out_of_cpt (s := u) cr (hS.disj r hr u hu hur.symm) hr1 hr2 with h | h
        · exact not_out_of_in (hSne v hv) (h.2 v (hS.disj r hr v hv hvr.symm)) hvO
        · exact not_out_of_in (hSne u hu) huA h.1
      unfold sepI
      rw [ite_eq_right, ite_eq_right, add_zero, mul_zero]
      · rintro ⟨h1, h2⟩
        obtain ⟨-, h⟩ := key t t.2 h1
        by_cases hsr : (s : Finset X) = r
        · exact hr2 (hsr ▸ h2)
        · exact h s s.2 hsr h2
      · rintro ⟨h1, h2⟩
        obtain ⟨-, h⟩ := key s s.2 h1
        by_cases htr : (t : Finset X) = r
        · exact hr2 (htr ▸ h2)
        · exact h t t.2 htr h2
    rw [Finset.sum_eq_zero (fun e _ => hinact e), add_zero]
    refine Finset.sum_congr rfl fun e _ => ?_
    congr 1
    have hout' : ∀ u : Y, (u : Finset X) ⊆ univ \ A e.1 ↔ ¬ (u : Finset X) ⊆ A e.1 := by
      intro u; rw [hout, hmemA']
    unfold sepI
    by_cases h1 : (s : Finset X) ⊆ A e.1 <;> by_cases h2 : (t : Finset X) ⊆ A e.1 <;>
      simp [h1, h2, hmemA', hout']
  exact ⟨E', inferInstance, Subtype.val, A', ⟨hne', hcompl', hcompat', hbin', hsingle⟩,
    hmemA', hcov, hsep⟩

/-- The reduced cherry lemma: on a partition of the taxa into sides, a pair of clusters
minimizing the Q-criterion for the tree distance between clusters forms a side. -/
private lemma exists_eq_union_of_qCriterion_min {X : Type*} [Fintype X] [DecidableEq X]
    {E : Type*} [Fintype E] {A : E → Finset X} {w : E → ℝ} (hA : SplitSys A)
    (hw : ∀ e, 0 < w e) {S : Finset (Finset X)} (hS : IsPart A S) (h4 : 4 ≤ S.card)
    {D : Finset X → Finset X → ℝ} (hD : ∀ s ∈ S, ∀ t ∈ S, D s t = treeD A w s t)
    {a b : Finset X} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hmin : ∀ a' ∈ S, ∀ b' ∈ S, a' ≠ b' → qCriterion S D a b ≤ qCriterion S D a' b') :
    ∃ e, A e = a ∪ b := by
  obtain ⟨E', _, g, A', hA', -, hcov, htree⟩ := reduce hA hS w
  have hsep : ∀ s t : {s // s ∈ S}, D s t =
      (1 / 2) * ∑ e, w (g e) * (if (s ∈ A' e ↔ t ∈ A' e) then 0 else 1) := fun s t =>
    (hD s s.2 t t.2).trans (htree s t)
  have hcardY : 4 ≤ Fintype.card {s // s ∈ S} := by
    rw [Fintype.card_coe]; exact h4
  have hQ : ∀ s t : {s // s ∈ S}, qCriterion S D s t =
      -∑ e, w (g e) * splitGain (A' e) s t := by
    intro s t
    rw [← sub_sum_sub_sum_eq_neg_sum_splitGain A' (fun e => w (g e)) (d := fun s t => D s t)
      hsep s t]
    unfold qCriterion
    rw [Fintype.card_coe]
    rw [← Finset.sum_coe_sort S (fun c => D s c), ← Finset.sum_coe_sort S (fun c => D t c)]
  obtain ⟨e, he⟩ := exists_eq_pair_of_isMax A' (fun e => w (g e)) (fun e => hw (g e)) hA'.ne
    hA'.compl hA'.compat hA'.bin hA'.single hcardY (x := ⟨a, ha⟩) (y := ⟨b, hb⟩)
    (fun h => hab (congrArg Subtype.val h))
    (fun s t hst => by
      have := hmin s s.2 t t.2 (fun h => hst (Subtype.ext h))
      rw [hQ ⟨a, ha⟩ ⟨b, hb⟩, hQ s t] at this
      linarith)
  refine ⟨g e, ?_⟩
  ext x
  rw [hcov e x, he, Finset.mem_union]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨s, rfl | rfl, hx⟩
    · exact Or.inl hx
    · exact Or.inr hx
  · rintro (hx | hx)
    · exact ⟨⟨a, ha⟩, Or.inl rfl, hx⟩
    · exact ⟨⟨b, hb⟩, Or.inr rfl, hx⟩

private lemma treeD_comm {X : Type*} [Fintype X] [DecidableEq X] {E : Type*} [Fintype E]
    (A : E → Finset X) (w : E → ℝ) (s t : Finset X) : treeD A w s t = treeD A w t s := by
  unfold treeD sepI
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

private lemma treeD_self {X : Type*} [Fintype X] [DecidableEq X] {E : Type*} [Fintype E]
    (A : E → Finset X) (w : E → ℝ) {s : Finset X} (hs : s.Nonempty) : treeD A w s s = 0 := by
  unfold treeD sepI
  rw [Finset.sum_eq_zero, mul_zero]
  intro e _
  have h : ¬ (s ⊆ A e ∧ s ⊆ univ \ A e) := fun h => not_out_of_in hs h.1 h.2
  simp [h]

/-- The invariant of a neighbor-joining run whose joins form sides, at the level of splits. -/
private structure Inv {X : Type*} [Fintype X] [DecidableEq X] {E : Type*}
    (A : E → Finset X) (S : Finset (Finset X)) (C : Finset (Finset X)) : Prop where
  part : IsPart A S
  small : ∀ s ∈ S, s.card = 1 ∨ s ∈ C
  formed : ∀ c ∈ C, (∃ e, A e = c) ∧ 2 ≤ c.card ∧ 2 ≤ (univ \ c).card
  split : ∀ e, A e ∈ C ∨ univ \ A e ∈ C ∨ (A e).card ≤ 1 ∨ (univ \ A e).card ≤ 1 ∨
    ∀ s ∈ S, s ⊆ A e ∨ s ⊆ univ \ A e

private lemma inv_init {X : Type*} [Fintype X] [DecidableEq X] {E : Type*}
    {A : E → Finset X} (hA : SplitSys A) :
    Inv A (univ.image fun x => ({x} : Finset X)) ∅ where
  part :=
    { side := by
        intro s hs
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hs
        exact hA.single x
      disj := by
        intro s hs t ht hst
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hs
        obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp ht
        rw [Finset.disjoint_singleton]
        exact fun h => hst (h ▸ rfl)
      cover := fun x => ⟨{x}, Finset.mem_image_of_mem _ (Finset.mem_univ x),
        Finset.mem_singleton_self x⟩ }
  small := by
    intro s hs
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hs
    exact Or.inl (Finset.card_singleton x)
  formed := by simp
  split := by
    intro e
    right; right; right; right
    intro s hs
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hs
    by_cases hx : x ∈ A e
    · exact Or.inl (Finset.singleton_subset_iff.mpr hx)
    · exact Or.inr (Finset.singleton_subset_iff.mpr (by simp [hx]))

private lemma eq_of_cpt_union {X : Type*} [Fintype X] [DecidableEq X] {B a b : Finset X}
    (ha : a.Nonempty) (hb : b.Nonempty) (hc : Cpt B (a ∪ b))
    (haB : a ⊆ B) (hbB : b ⊆ univ \ B) : B = a ∨ univ \ B = b := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  have hvB : v ∉ B := (Finset.mem_sdiff.mp (hbB hv)).2
  by_cases h : ∃ t, t ∈ B ∧ t ∉ a ∪ b
  · obtain ⟨t, htB, htU⟩ := h
    right
    -- every element outside `B` lies in `a ∪ b`, hence in `b`
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro hzB
      by_contra hzb
      have hza : z ∉ a := fun h => hzB (haB h)
      exact hc u t v z (haB hu) (Finset.mem_union_left _ hu) htB htU hvB
        (Finset.mem_union_right _ hv) hzB (by simp [hza, hzb])
    · intro hzb hzB
      exact (Finset.mem_sdiff.mp (hbB hzb)).2 hzB
  · push Not at h
    left
    ext z
    constructor
    · intro hzB
      rcases Finset.mem_union.mp (h z hzB) with h' | h'
      · exact h'
      · exact absurd hzB (Finset.mem_sdiff.mp (hbB h')).2
    · exact fun h' => haB h'

/-- Joining two clusters whose union is a side preserves the invariant. -/
private lemma inv_join {X : Type*} [Fintype X] [DecidableEq X] {E : Type*}
    {A : E → Finset X} (hA : SplitSys A) {S : Finset (Finset X)} {C : Finset (Finset X)}
    (hI : Inv A S C) (h4 : 4 ≤ S.card) {a b : Finset X} (ha : a ∈ S) (hb : b ∈ S)
    (hab : a ≠ b) {eU : E} (heU : A eU = a ∪ b) :
    Inv A (insert (a ∪ b) ((S.erase a).erase b)) (insert (a ∪ b) C) := by
  have hSne : ∀ s ∈ S, s.Nonempty := fun s hs => by
    obtain ⟨e, he⟩ := hI.part.side s hs
    exact he ▸ hA.ne e
  have hdab := hI.part.disj a ha b hb hab
  have hane := hSne a ha
  have hbne := hSne b hb
  have hmem : ∀ t, t ∈ insert (a ∪ b) ((S.erase a).erase b) ↔
      t = a ∪ b ∨ (t ∈ S ∧ t ≠ a ∧ t ≠ b) := by
    intro t
    simp only [Finset.mem_insert, Finset.mem_erase]
    tauto
  have hdisjU : ∀ t ∈ S, t ≠ a → t ≠ b → Disjoint (a ∪ b) t := fun t ht hta htb =>
    Finset.disjoint_union_left.mpr ⟨hI.part.disj a ha t ht (Ne.symm hta),
      hI.part.disj b hb t ht (Ne.symm htb)⟩
  have hneU : ∀ t ∈ S, t ≠ a → t ≠ b → t ≠ a ∪ b := by
    intro t ht hta htb h
    obtain ⟨z, hz⟩ := hSne t ht
    have := hdisjU t ht hta htb
    rw [← h] at this
    exact Finset.disjoint_left.mp this hz hz
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro t ht
    rcases (hmem t).mp ht with rfl | ⟨ht, -, -⟩
    · exact ⟨eU, heU⟩
    · exact hI.part.side t ht
  · intro s hs t ht hst
    rcases (hmem s).mp hs with rfl | ⟨hs, hsa, hsb⟩ <;>
      rcases (hmem t).mp ht with rfl | ⟨ht, hta, htb⟩
    · exact absurd rfl hst
    · exact hdisjU t ht hta htb
    · exact (hdisjU s hs hsa hsb).symm
    · exact hI.part.disj s hs t ht hst
  · intro x
    obtain ⟨s, hs, hxs⟩ := hI.part.cover x
    by_cases hsa : s = a
    · exact ⟨a ∪ b, (hmem _).mpr (Or.inl rfl), Finset.mem_union_left _ (hsa ▸ hxs)⟩
    · by_cases hsb : s = b
      · exact ⟨a ∪ b, (hmem _).mpr (Or.inl rfl), Finset.mem_union_right _ (hsb ▸ hxs)⟩
      · exact ⟨s, (hmem _).mpr (Or.inr ⟨hs, hsa, hsb⟩), hxs⟩
  · intro t ht
    rcases (hmem t).mp ht with rfl | ⟨ht, -, -⟩
    · exact Or.inr (Finset.mem_insert_self _ _)
    · exact (hI.small t ht).imp_right (Finset.mem_insert_of_mem)
  · intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · refine ⟨⟨eU, heU⟩, ?_, ?_⟩
      · rw [Finset.card_union_of_disjoint hdab]
        have := hane.card_pos; have := hbne.card_pos; omega
      · have hcard : 2 ≤ ((S.erase a).erase b).card := by
          rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩),
            Finset.card_erase_of_mem ha]
          omega
        obtain ⟨c₁, hc₁, c₂, hc₂, hc12⟩ := Finset.one_lt_card.mp hcard
        simp only [Finset.mem_erase] at hc₁ hc₂
        have hsub : c₁ ∪ c₂ ⊆ univ \ (a ∪ b) := by
          intro z hz
          rw [Finset.mem_sdiff]
          refine ⟨Finset.mem_univ z, fun hzU => ?_⟩
          rcases Finset.mem_union.mp hz with h | h
          · exact Finset.disjoint_left.mp (hdisjU c₁ hc₁.2.2 hc₁.2.1 hc₁.1) hzU h
          · exact Finset.disjoint_left.mp (hdisjU c₂ hc₂.2.2 hc₂.2.1 hc₂.1) hzU h
        have := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint (hI.part.disj c₁ hc₁.2.2 c₂ hc₂.2.2 hc12)] at this
        have := (hSne c₁ hc₁.2.2).card_pos
        have := (hSne c₂ hc₂.2.2).card_pos
        omega
    · exact hI.formed c hc
  · intro e
    rcases hI.split e with h | h | h | h | h
    · exact Or.inl (Finset.mem_insert_of_mem h)
    · exact Or.inr (Or.inl (Finset.mem_insert_of_mem h))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · have hcU := heU ▸ cpt_of (hA.compat e eU)
      have hact : (a ∪ b) ⊆ A e ∨ (a ∪ b) ⊆ univ \ A e → ∀ t ∈ insert (a ∪ b)
          ((S.erase a).erase b), t ⊆ A e ∨ t ⊆ univ \ A e := by
        intro hU t ht
        rcases (hmem t).mp ht with rfl | ⟨ht, -, -⟩
        · exact hU
        · exact h t ht
      have hone : ∀ c ∈ S, (A e = c ∨ univ \ A e = c) → A e ∈ insert (a ∪ b) C ∨
          univ \ A e ∈ insert (a ∪ b) C ∨ (A e).card ≤ 1 ∨ (univ \ A e).card ≤ 1 := by
        intro c hc hce
        rcases hce with h' | h' <;> rcases hI.small c hc with h1 | h1 <;> rw [← h'] at h1
        · exact Or.inr (Or.inr (Or.inl h1.le))
        · exact Or.inl (Finset.mem_insert_of_mem h1)
        · exact Or.inr (Or.inr (Or.inr h1.le))
        · exact Or.inr (Or.inl (Finset.mem_insert_of_mem h1))
      rcases h a ha with ha' | ha' <;> rcases h b hb with hb' | hb'
      · exact Or.inr (Or.inr (Or.inr (Or.inr (hact (Or.inl (Finset.union_subset ha' hb'))))))
      · rcases eq_of_cpt_union hane hbne hcU ha' hb' with h' | h'
        · rcases hone a ha (Or.inl h') with h'' | h'' | h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl h'')
          · exact Or.inr (Or.inr (Or.inl h''))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h'')))
        · rcases hone b hb (Or.inr h') with h'' | h'' | h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl h'')
          · exact Or.inr (Or.inr (Or.inl h''))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h'')))
      · rcases eq_of_cpt_union hbne hane (Finset.union_comm a b ▸ hcU) hb' ha'
          with h' | h'
        · rcases hone b hb (Or.inl h') with h'' | h'' | h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl h'')
          · exact Or.inr (Or.inr (Or.inl h''))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h'')))
        · rcases hone a ha (Or.inr h') with h'' | h'' | h'' | h''
          · exact Or.inl h''
          · exact Or.inr (Or.inl h'')
          · exact Or.inr (Or.inr (Or.inl h''))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h'')))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (hact (Or.inr (Finset.union_subset ha' hb'))))))

/-- Joining two clusters whose union is a side keeps the cluster dissimilarity equal to the
tree distance. -/
private lemma dist_join {X : Type*} [Fintype X] [DecidableEq X] {E : Type*} [Fintype E]
    {A : E → Finset X} {w : E → ℝ} (hA : SplitSys A) {S : Finset (Finset X)} (hP : IsPart A S)
    {D : Finset X → Finset X → ℝ} (hD : ∀ s ∈ S, ∀ t ∈ S, D s t = treeD A w s t)
    {a b : Finset X} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) {eU : E} (heU : A eU = a ∪ b) :
    ∀ s ∈ insert (a ∪ b) ((S.erase a).erase b), ∀ t ∈ insert (a ∪ b) ((S.erase a).erase b),
      joinDist D a b s t = treeD A w s t := by
  have hSne : ∀ s ∈ S, s.Nonempty := fun s hs => by
    obtain ⟨e, he⟩ := hP.side s hs
    exact he ▸ hA.ne e
  obtain ⟨ea, hea⟩ := hP.side a ha
  obtain ⟨eb, heb⟩ := hP.side b hb
  have hdab := hP.disj a ha b hb hab
  have hane := hSne a ha
  have hmem : ∀ t, t ∈ insert (a ∪ b) ((S.erase a).erase b) ↔
      t = a ∪ b ∨ (t ∈ S ∧ t ≠ a ∧ t ≠ b) := by
    intro t
    simp only [Finset.mem_insert, Finset.mem_erase]
    tauto
  have hneU : ∀ t ∈ S, t ≠ a → t ≠ b → t ≠ a ∪ b := by
    intro t ht hta htb h
    obtain ⟨z, hz⟩ := hSne t ht
    have := Finset.disjoint_union_left.mpr ⟨hP.disj a ha t ht (Ne.symm hta),
      hP.disj b hb t ht (Ne.symm htb)⟩
    rw [← h] at this
    exact Finset.disjoint_left.mp this hz hz
  intro s hs t ht
  unfold joinDist
  rcases (hmem s).mp hs with rfl | ⟨hs, hsa, hsb⟩ <;>
    rcases (hmem t).mp ht with h | ⟨ht, hta, htb⟩
  · rw [ite_eq_left rfl, ite_eq_left h, h]
    exact (treeD_self A w (hane.mono Finset.subset_union_left)).symm
  · rw [ite_eq_left rfl, ite_eq_right (hneU t ht hta htb), hD a ha t ht, hD b hb t ht,
      hD a ha b hb]
    exact (treeD_union w hA hea heb heU (hSne t ht) hdab (hP.disj a ha t ht (Ne.symm hta))
      (hP.disj b hb t ht (Ne.symm htb))).symm
  · rw [ite_eq_right (hneU s hs hsa hsb), ite_eq_left h, hD a ha s hs, hD b hb s hs,
      hD a ha b hb, h, treeD_comm A w s]
    exact (treeD_union w hA hea heb heU (hSne s hs) hdab (hP.disj a ha s hs (Ne.symm hsa))
      (hP.disj b hb s hs (Ne.symm hsb))).symm
  · rw [ite_eq_right (hneU s hs hsa hsb), ite_eq_right (hneU t ht hta htb)]
    exact hD s hs t ht

/-- Along a run of neighbor joining on a tree metric, the invariant holds and the cluster
dissimilarity is the tree distance. -/
private lemma inv_run {X : Type*} [Fintype X] [DecidableEq X] {E : Type*} [Fintype E]
    {A : E → Finset X} {w : E → ℝ} (hA : SplitSys A) (hw : ∀ e, 0 < w e) {d : X → X → ℝ}
    (hd : ∀ x y, d x y = treeD A w {x} {y}) {S : Finset (Finset X)}
    {D : Finset X → Finset X → ℝ} {C : Finset (Finset X)} (hrun : NJRun d S D C) :
    Inv A S C ∧ ∀ s ∈ S, ∀ t ∈ S, D s t = treeD A w s t := by
  induction hrun with
  | init =>
    refine ⟨inv_init hA, fun s hs t ht => ?_⟩
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp ht
    simp [initialDist, hd]
  | join _ h4 ha hb hab hmin ih =>
    obtain ⟨eU, heU⟩ := exists_eq_union_of_qCriterion_min hA hw ih.1.part h4 ih.2 ha hb hab hmin
    exact ⟨inv_join hA ih.1 h4 ha hb hab heU, dist_join hA ih.1.part ih.2 ha hb hab heU⟩

private lemma inv_final {X : Type*} [Fintype X] [DecidableEq X] {E : Type*}
    {A : E → Finset X} (hA : SplitSys A) {S : Finset (Finset X)}
    {C : Finset (Finset X)} (hI : Inv A S C)
    (h3 : S.card ≤ 3) (A₀ : Finset X) :
    (A₀ ∈ C ∨ univ \ A₀ ∈ C) ↔ ∃ e, A e = A₀ ∧ 2 ≤ A₀.card ∧ 2 ≤ (univ \ A₀).card := by
  have hSne : ∀ s ∈ S, s.Nonempty := fun s hs => by
    obtain ⟨e, he⟩ := hI.part.side s hs
    exact he ▸ hA.ne e
  constructor
  · rintro (h | h)
    · obtain ⟨⟨e, he⟩, h1, h2⟩ := hI.formed A₀ h
      exact ⟨e, he, h1, h2⟩
    · obtain ⟨⟨e, he⟩, h1, h2⟩ := hI.formed _ h
      obtain ⟨e', he'⟩ := hA.compl e
      rw [he, Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)] at he'
      rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)] at h2
      exact ⟨e', he', h2, h1⟩
  · rintro ⟨e, rfl, h1, h2⟩
    rcases hI.split e with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · omega
    · omega
    · -- the clusters inside `A e` and those outside
      classical
      have hfill : ∀ B : Finset X, (∀ s ∈ S, s ⊆ B ∨ s ⊆ univ \ B) → B.Nonempty →
          (S.filter fun s => s ⊆ B).Nonempty ∧ ((S.filter fun s => s ⊆ B).card = 1 → B ∈ S) := by
        intro B hB hBne
        have hcovB : ∀ x ∈ B, ∃ s ∈ S, x ∈ s ∧ s ⊆ B := by
          intro x hx
          obtain ⟨s, hs, hxs⟩ := hI.part.cover x
          refine ⟨s, hs, hxs, ?_⟩
          rcases hB s hs with h' | h'
          · exact h'
          · exact absurd hx (Finset.mem_sdiff.mp (h' hxs)).2
        obtain ⟨x, hx⟩ := hBne
        obtain ⟨s, hs, hxs, hsB⟩ := hcovB x hx
        refine ⟨⟨s, Finset.mem_filter.mpr ⟨hs, hsB⟩⟩, fun h1 => ?_⟩
        obtain ⟨s', hs'⟩ := Finset.card_eq_one.mp h1
        have hmem : ∀ t, t ∈ S → t ⊆ B → t = s' := by
          intro t ht htB
          have : t ∈ S.filter fun s => s ⊆ B := Finset.mem_filter.mpr ⟨ht, htB⟩
          rw [hs'] at this
          exact Finset.mem_singleton.mp this
        have hs'S : s' ∈ S := by
          have : s' ∈ S.filter fun s => s ⊆ B := hs' ▸ Finset.mem_singleton_self s'
          exact (Finset.mem_filter.mp this).1
        have hs'B : s' ⊆ B := by
          have : s' ∈ S.filter fun s => s ⊆ B := hs' ▸ Finset.mem_singleton_self s'
          exact (Finset.mem_filter.mp this).2
        have : B = s' := by
          apply Finset.Subset.antisymm _ hs'B
          intro z hz
          obtain ⟨t, ht, hzt, htB⟩ := hcovB z hz
          exact hmem t ht htB ▸ hzt
        exact this ▸ hs'S
      have hAc : (univ \ A e).Nonempty := by
        obtain ⟨e', h'⟩ := hA.compl e
        rw [← h']
        exact hA.ne e'
      have hc' : ∀ s ∈ S, s ⊆ univ \ A e ∨ s ⊆ univ \ (univ \ A e) := by
        intro s hs
        rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)]
        exact (h s hs).symm
      obtain ⟨hi1, hi2⟩ := hfill (A e) h (hA.ne e)
      obtain ⟨ho1, ho2⟩ := hfill (univ \ A e) hc' hAc
      have hdisj : Disjoint (S.filter fun s => s ⊆ A e) (S.filter fun s => s ⊆ univ \ A e) := by
        rw [Finset.disjoint_left]
        intro s hs hs'
        rw [Finset.mem_filter] at hs hs'
        exact not_out_of_in (hSne s hs.1) hs.2 hs'.2
      have hsub := Finset.card_le_card (Finset.union_subset
        (Finset.filter_subset (fun s => s ⊆ A e) S)
        (Finset.filter_subset (fun s => s ⊆ univ \ A e) S))
      rw [Finset.card_union_of_disjoint hdisj] at hsub
      have := hi1.card_pos
      have := ho1.card_pos
      have hsmall : ∀ B ∈ S, 2 ≤ B.card → B ∈ C := fun B hB h2 =>
        (hI.small B hB).resolve_left (by omega)
      by_cases hi : (S.filter fun s => s ⊆ A e).card = 1
      · exact Or.inl (hsmall _ (hi2 hi) h1)
      · exact Or.inr (hsmall _ (ho2 (by omega)) h2)

/-! ### Assembly -/

/-- A side holding a single taxon `z` is the leaf side of `z`'s pendant edge. -/
theorem eq_of_side_eq_singleton {X : Type*} [Fintype X] {V : Type*}
    [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {ι : X → V}
    (hT : IsBinaryPhylogeneticTree G ι) {c a : V} (hca : G.Adj c a) {z : X}
    (h : side G ι c a = {z}) : c = ι z := by
  classical
  by_cases hc : c ∈ Set.range ι
  · obtain ⟨z', rfl⟩ := hc
    rw [side_leaf hT hca, Finset.singleton_inj] at h
    rw [h]
  · obtain ⟨c₁, c₂, h₁, h₂, -, -, -, hdisj, hunion⟩ := side_eq_union hT hc hca
    have hcard := Finset.card_union_of_disjoint hdisj
    rw [← hunion, h, Finset.card_singleton] at hcard
    have := (side_nonempty hT h₁.symm).card_pos
    have := (side_nonempty hT h₂.symm).card_pos
    omega

/-- If a side of the edge `{a, b}` is the pair `{x, y}`, then `a` is a common neighbor of the
leaves `ι x` and `ι y`: they form a cherry. -/
theorem adj_adj_of_side_eq_pair {X : Type*} [Fintype X] [DecidableEq X] {V : Type*}
    [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {ι : X → V}
    (hT : IsBinaryPhylogeneticTree G ι) {a b : V} (hab : G.Adj a b) {x y : X} (hxy : x ≠ y)
    (h : side G ι a b = {x, y}) : G.Adj (ι x) a ∧ G.Adj (ι y) a := by
  have ha : a ∉ Set.range ι := by
    rintro ⟨z, rfl⟩
    have := congrArg Finset.card h
    rw [side_leaf hT hab, Finset.card_singleton, Finset.card_pair hxy] at this
    omega
  obtain ⟨c, e, hc, he, -, -, -, hdisj, hunion⟩ := side_eq_union hT ha hab
  have hcne := side_nonempty hT hc.symm
  have hene := side_nonempty hT he.symm
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [← hunion, h, Finset.card_pair hxy] at hcard
  have hc1 : (side G ι c a).card = 1 := by
    have := hene.card_pos; have := hcne.card_pos; omega
  have he1 : (side G ι e a).card = 1 := by
    have := hene.card_pos; have := hcne.card_pos; omega
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hc1
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp he1
  have hcu := eq_of_side_eq_singleton hT hc.symm hu
  have hev := eq_of_side_eq_singleton hT he.symm hv
  have hxu : x ∈ side G ι c a ∪ side G ι e a := by rw [← hunion, h]; simp
  have hyu : y ∈ side G ι c a ∪ side G ι e a := by rw [← hunion, h]; simp
  rw [hu, hv] at hxu hyu
  simp only [Finset.mem_union, Finset.mem_singleton] at hxu hyu
  rcases hxu with rfl | rfl <;> rcases hyu with rfl | rfl
  · exact absurd rfl hxy
  · exact ⟨hcu ▸ hc.symm, hev ▸ he.symm⟩
  · exact ⟨hev ▸ he.symm, hcu ▸ hc.symm⟩
  · exact absurd rfl hxy

/-- The sides of the edges of a binary phylogenetic tree form a compatible binary split
system containing every trivial split. -/
private lemma splitSys_side {X : Type*} [Fintype X] [DecidableEq X] {V : Type*}
    [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {ι : X → V}
    (hT : IsBinaryPhylogeneticTree G ι) :
    SplitSys (fun t : G.Dart => side G ι t.fst t.snd) := by
  set A : G.Dart → Finset X := fun t => side G ι t.fst t.snd with hA
  have hsw : ∀ t : G.Dart, side G ι t.snd t.fst = univ \ A t := fun t =>
    side_swap hT.1 t.adj
  refine ⟨fun t => side_nonempty hT t.adj, fun t => ⟨t.symm, hsw t⟩, fun t t' => ?_,
    fun t ht => ?_, fun z => ?_⟩
  · rcases side_compat (ι := ι) hT.1 t.adj t'.adj with h | h | h | h
    · rw [hsw t] at h
      right; right; right
      ext z; by_cases hz : z ∈ A t
      · simp only [Finset.mem_union, Finset.mem_univ, iff_true]
        left; exact hz
      · simp only [Finset.mem_union, Finset.mem_univ, iff_true]
        right
        exact h (by simp [hz])
    · rw [hsw t, hsw t'] at h
      right; right; left
      intro z hz; by_contra hz'
      have := h (by simp [hz'] : z ∈ univ \ A t)
      simp [hz] at this
    · right; left; exact h
    · rw [hsw t'] at h
      left
      rw [Finset.disjoint_left]
      intro z hz hz'
      have := h hz
      simp [hz'] at this
  · have ha : t.fst ∉ Set.range ι := by
      rintro ⟨z, hz⟩
      have := side_leaf hT (hz ▸ t.adj)
      simp only [hA] at ht
      rw [← hz, this, Finset.card_singleton] at ht
      omega
    obtain ⟨c, e, hc, he, -, -, -, hdisj, hunion⟩ := side_eq_union hT ha t.adj
    exact ⟨⟨(c, t.fst), hc.symm⟩, ⟨(e, t.fst), he.symm⟩, hdisj, hunion.symm⟩
  · have h1 : G.degree (ι z) = 1 := (hT.2.2.1 (ι z)).mpr ⟨z, rfl⟩
    obtain ⟨b, hb, -⟩ := (G.degree_eq_one_iff_existsUnique_adj).mp h1
    exact ⟨⟨(ι z, b), hb⟩, side_leaf hT hb⟩

/-- **On a tree metric, a pair of taxa minimizing the Q-criterion is a cherry**
(Saitou & Nei 1987; Studier & Keppler 1988; Bryant 2005). Let `d` be the path-length metric
of a binary phylogenetic `X`-tree `(G, ι)` with positive edge lengths `w` and at least four
taxa. If the distinct taxa `x, y` minimize the Q-criterion over all pairs of distinct
singleton clusters at the start of neighbor joining, then `ι x` and `ι y` have a common
neighbor. -/
theorem exists_adj_adj_of_qCriterion_min {X : Type*} [Fintype X] [DecidableEq X] {V : Type*}
    [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {ι : X → V}
    (hT : IsBinaryPhylogeneticTree G ι) {w : Sym2 V → ℝ} (hw : ∀ e ∈ G.edgeSet, 0 < w e)
    {d : X → X → ℝ}
    (hd : ∀ x y (p : G.Walk (ι x) (ι y)), p.IsPath → d x y = (p.edges.map w).sum)
    (hX : 4 ≤ Fintype.card X) {x y : X} (hxy : x ≠ y)
    (hmin : ∀ a' ∈ univ.image (fun x => ({x} : Finset X)),
      ∀ b' ∈ univ.image (fun x => ({x} : Finset X)), a' ≠ b' →
        qCriterion (univ.image fun x => ({x} : Finset X)) (initialDist d) {x} {y} ≤
          qCriterion (univ.image fun x => ({x} : Finset X)) (initialDist d) a' b') :
    ∃ u, G.Adj (ι x) u ∧ G.Adj (ι y) u := by
  classical
  set A : G.Dart → Finset X := fun t => side G ι t.fst t.snd with hA
  have hS := splitSys_side hT
  have hQ : ∀ x y, qCriterion (univ.image fun x => ({x} : Finset X)) (initialDist d) {x} {y} =
      -∑ t, w t.edge * splitGain (A t) x y := by
    intro x y
    rw [qCriterion_singleton]
    exact sub_sum_sub_sum_eq_neg_sum_splitGain A (fun t => w t.edge)
      (fun x y => dist_eq_sum_darts hT.1 hd x y) x y
  obtain ⟨t, ht⟩ := exists_eq_pair_of_isMax A (fun t => w t.edge)
    (fun t => hw _ t.edge_mem) hS.ne hS.compl hS.compat hS.bin hS.single hX hxy
    (fun x' y' hne => by
      have := hmin {x'} (by simp) {y'} (by simp) (by simpa using hne)
      rw [hQ, hQ] at this
      linarith)
  exact ⟨t.fst, adj_adj_of_side_eq_pair hT t.adj hxy ht⟩

/-- **The first join of neighbor joining on a tree metric joins a cherry.** On the path-length
metric of a binary phylogenetic `X`-tree with positive edge lengths and at least four taxa,
any pair of clusters that neighbor joining may join from the initial singletons consists of
two taxa with a common neighbor. -/
theorem NJRun.exists_adj_adj_of_join_init {X : Type*} [Fintype X] [DecidableEq X] {V : Type*}
    [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {ι : X → V}
    (hT : IsBinaryPhylogeneticTree G ι) {w : Sym2 V → ℝ} (hw : ∀ e ∈ G.edgeSet, 0 < w e)
    {d : X → X → ℝ}
    (hd : ∀ x y (p : G.Walk (ι x) (ι y)), p.IsPath → d x y = (p.edges.map w).sum)
    {a b : Finset X} (ha : a ∈ univ.image fun x => ({x} : Finset X))
    (hb : b ∈ univ.image fun x => ({x} : Finset X)) (hab : a ≠ b)
    (h4 : 4 ≤ (univ.image fun x => ({x} : Finset X)).card)
    (hmin : ∀ a' ∈ univ.image (fun x => ({x} : Finset X)),
      ∀ b' ∈ univ.image (fun x => ({x} : Finset X)), a' ≠ b' →
        qCriterion (univ.image fun x => ({x} : Finset X)) (initialDist d) a b ≤
          qCriterion (univ.image fun x => ({x} : Finset X)) (initialDist d) a' b') :
    ∃ x y u, a = {x} ∧ b = {y} ∧ x ≠ y ∧ G.Adj (ι x) u ∧ G.Adj (ι y) u := by
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hb
  have hxy : x ≠ y := fun h => hab (by rw [h])
  rw [Finset.card_image_of_injective _ Finset.singleton_injective, Finset.card_univ] at h4
  obtain ⟨u, hu⟩ := exists_adj_adj_of_qCriterion_min hT hw hd h4 hxy hmin
  exact ⟨x, y, u, rfl, rfl, hxy, hu⟩


/-- On a tree metric the tree distance between singleton clusters is the dissimilarity. -/
private lemma dist_eq_treeD {X : Type*} [Fintype X] [DecidableEq X] {V : Type*}
    [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {ι : X → V} (hG : G.IsTree)
    {w : Sym2 V → ℝ} {d : X → X → ℝ}
    (hd : ∀ x y (p : G.Walk (ι x) (ι y)), p.IsPath → d x y = (p.edges.map w).sum) (x y : X) :
    d x y = treeD (fun t : G.Dart => side G ι t.fst t.snd) (fun t => w t.edge) {x} {y} := by
  rw [dist_eq_sum_darts hG hd x y]
  unfold treeD
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  unfold sepI
  by_cases hx : x ∈ side G ι t.fst t.snd <;> by_cases hy : y ∈ side G ι t.fst t.snd <;>
    simp [hx, hy]

/-- An edge of a binary phylogenetic tree with both endpoints internal has at least two taxa
on each side. -/
private lemma two_le_card_side {X : Type*} [Fintype X] {V : Type*}
    [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {ι : X → V}
    (hT : IsBinaryPhylogeneticTree G ι) {a b : V} (hab : G.Adj a b) (ha : a ∉ Set.range ι) :
    2 ≤ (side G ι a b).card := by
  classical
  obtain ⟨c, e, hc, he, -, -, -, hdisj, hunion⟩ := side_eq_union hT ha hab
  rw [hunion, Finset.card_union_of_disjoint hdisj]
  have := (side_nonempty hT hc.symm).card_pos
  have := (side_nonempty hT he.symm).card_pos
  omega

/-- `1` if a side of the split `B` is a proper subset of the cluster `s` and contains `x`. -/
private noncomputable def inner {X : Type*} [Fintype X] [DecidableEq X] (B s : Finset X)
    (x : X) : ℝ :=
  if (B ⊂ s ∧ x ∈ B) ∨ (univ \ B ⊂ s ∧ x ∉ B) then 1 else 0

/-- A split compatible with two disjoint clusters cuts at most one of them; the indicator that
it separates `x ∈ s` from `y ∈ t` is the indicator that it separates the clusters plus terms
depending only on `(s, x)` and on `(t, y)`. -/
private lemma sep_eq_sepI_add_inner {X : Type*} [Fintype X] [DecidableEq X] {B s t : Finset X}
    (hBs : Disjoint B s ∨ B ⊆ s ∨ s ⊆ B ∨ B ∪ s = univ)
    (hBt : Disjoint B t ∨ B ⊆ t ∨ t ⊆ B ∨ B ∪ t = univ) (hst : Disjoint s t) {x y : X}
    (hx : x ∈ s) (hy : y ∈ t) :
    (if (x ∈ B ↔ y ∈ B) then (0 : ℝ) else 1) = sepI B s t + inner B s x + inner B t y := by
  classical
  rcases hBs with hBs | hBs | hBs | hBs <;>
    rcases hBt with hBt | hBt | hBt | hBt <;>
    by_cases hxb : x ∈ B <;> by_cases hyb : y ∈ B <;>
    simp only [sepI, inner, Finset.ssubset_iff_subset_ne, ne_eq, Finset.ext_iff,
      Finset.subset_iff, Finset.disjoint_left, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_univ, true_and, iff_true] at * <;>
    grind

/-- A dart whose side holds at least two taxa starts at an internal vertex. -/
private lemma fst_notMem_range_of_two_le_card {X : Type*} [Fintype X] {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {ι : X → V} (hT : IsBinaryPhylogeneticTree G ι)
    {a b : V} (hab : G.Adj a b) (h : 2 ≤ (side G ι a b).card) : a ∉ Set.range ι := by
  rintro ⟨z, rfl⟩
  rw [side_leaf hT hab, Finset.card_singleton] at h
  omega

universe u in
/-- **The path metric on a partition into sides.** Let `S` partition the taxa of a binary
phylogenetic `X`-tree `(G, ι)` with positive edge lengths `w` and path-length metric `d` into
sides of edges. Then there is a system of splits `A e` (`e : E`) of the set of clusters with
positive weights `w' e`, closed under complement, pairwise compatible, binary, and containing
every trivial split, such that
* the weight of every internal split (both sides with at least two clusters) is the length of an
  edge with both endpoints internal;
* a split whose side is `{s, t}` comes from an edge with side `s ∪ t`;
* for taxa `x ∈ s` and `y ∈ t` of distinct clusters, `d x y` is half the total weight of the
  splits separating `s` from `t`, plus a term `ρ s x` depending only on `s` and `x` and a term
  `ρ t y`.
In the construction, the splits are those of the edges that cut no cluster. -/
theorem exists_splitSystem_of_partition {X : Type*} [Fintype X] [DecidableEq X] {V : Type u}
    [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {ι : X → V}
    (hT : IsBinaryPhylogeneticTree G ι) {w : Sym2 V → ℝ} (hw : ∀ e ∈ G.edgeSet, 0 < w e)
    {d : X → X → ℝ}
    (hd : ∀ x y (p : G.Walk (ι x) (ι y)), p.IsPath → d x y = (p.edges.map w).sum)
    {S : Finset (Finset X)} (hside : ∀ s ∈ S, ∃ u v, G.Adj u v ∧ side G ι u v = s)
    (hdisj : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → Disjoint s t) (hcover : ∀ x, ∃ s ∈ S, x ∈ s) :
    ∃ (E : Type u) (_ : Fintype E) (A : E → Finset {s // s ∈ S}) (w' : E → ℝ)
      (ρ : {s // s ∈ S} → X → ℝ),
      (∀ e, 0 < w' e) ∧ (∀ e, (A e).Nonempty) ∧ (∀ e, ∃ e', A e' = univ \ A e) ∧
      (∀ e e', Disjoint (A e) (A e') ∨ A e ⊆ A e' ∨ A e' ⊆ A e ∨ A e ∪ A e' = univ) ∧
      (∀ e, 2 ≤ (A e).card → ∃ e₁ e₂, Disjoint (A e₁) (A e₂) ∧ A e₁ ∪ A e₂ = A e) ∧
      (∀ s, ∃ e, A e = {s}) ∧
      (∀ e, 2 ≤ (A e).card → 2 ≤ (univ \ A e).card →
        ∃ u v, G.Adj u v ∧ u ∉ Set.range ι ∧ v ∉ Set.range ι ∧ w' e = w s(u, v)) ∧
      (∀ e s t, A e = {s, t} → ∃ u v, G.Adj u v ∧ side G ι u v = (s : Finset X) ∪ t) ∧
      ∀ s t : {s // s ∈ S}, s ≠ t → ∀ x ∈ (s : Finset X), ∀ y ∈ (t : Finset X),
        d x y = (1 / 2) * ∑ e, w' e * (if (s ∈ A e ↔ t ∈ A e) then 0 else 1) +
          ρ s x + ρ t y := by
  classical
  have hSS := splitSys_side hT
  have hP : IsPart (fun t : G.Dart => side G ι t.fst t.snd) S :=
    ⟨fun s hs => by
      obtain ⟨u, v, huv, h⟩ := hside s hs
      exact ⟨⟨(u, v), huv⟩, h⟩, hdisj, hcover⟩
  obtain ⟨E', _, g, A', hA', hmemA', hcov, htree⟩ := reduce hSS hP (fun t => w t.edge)
  -- a cluster outside a reduced split lies in the complement of the original split
  have hout : ∀ e (s : {s // s ∈ S}), s ∉ A' e →
      (s : Finset X) ⊆ univ \ side G ι (g e).fst (g e).snd := by
    intro e s hs x hx
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ x, fun hxA => ?_⟩
    obtain ⟨s', hs', hxs'⟩ := (hcov e x).mp hxA
    have hne : (s' : Finset X) ≠ s := fun h => hs (Subtype.ext h ▸ hs')
    exact Finset.disjoint_left.mp (hdisj s' s'.2 s s.2 hne) hxs' hx
  have htwo : ∀ (B : Finset X) (s₁ s₂ : {s // s ∈ S}), s₁ ≠ s₂ → (s₁ : Finset X) ⊆ B →
      (s₂ : Finset X) ⊆ B → 2 ≤ B.card := by
    intro B s₁ s₂ h12 h1 h2
    have h12' : (s₁ : Finset X) ≠ s₂ := fun h => h12 (Subtype.ext h)
    have hc := Finset.card_le_card (Finset.union_subset h1 h2)
    rw [Finset.card_union_of_disjoint (hdisj s₁ s₁.2 s₂ s₂.2 h12')] at hc
    obtain ⟨e₁, he₁⟩ := hP.side s₁ s₁.2
    obtain ⟨e₂, he₂⟩ := hP.side s₂ s₂.2
    have := (he₁ ▸ hSS.ne e₁).card_pos
    have := (he₂ ▸ hSS.ne e₂).card_pos
    omega
  refine ⟨E', inferInstance, A', fun e => w (g e).edge,
    fun s x => (1 / 2) * ∑ t : G.Dart, w t.edge * inner (side G ι t.fst t.snd) s x,
    fun e => hw _ (g e).edge_mem, hA'.ne, hA'.compl, hA'.compat, hA'.bin, hA'.single, ?_, ?_, ?_⟩
  · intro e h1 h2
    obtain ⟨s₁, hs₁, s₂, hs₂, h12⟩ := Finset.one_lt_card.mp h1
    obtain ⟨t₁, ht₁, t₂, ht₂, ht12⟩ := Finset.one_lt_card.mp h2
    have hin : 2 ≤ (side G ι (g e).fst (g e).snd).card :=
      htwo _ s₁ s₂ h12 ((hmemA' e s₁).mp hs₁) ((hmemA' e s₂).mp hs₂)
    have hout2 : 2 ≤ (side G ι (g e).snd (g e).fst).card := by
      rw [side_swap hT.1 (g e).adj]
      exact htwo _ t₁ t₂ ht12 (hout e t₁ (Finset.mem_sdiff.mp ht₁).2)
        (hout e t₂ (Finset.mem_sdiff.mp ht₂).2)
    exact ⟨(g e).fst, (g e).snd, (g e).adj, fst_notMem_range_of_two_le_card hT (g e).adj hin,
      fst_notMem_range_of_two_le_card hT (g e).adj.symm hout2, rfl⟩
  · intro e s t he
    refine ⟨(g e).fst, (g e).snd, (g e).adj, ?_⟩
    ext x
    rw [hcov e x, he, Finset.mem_union]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨s', rfl | rfl, hx⟩
      · exact Or.inl hx
      · exact Or.inr hx
    · rintro (hx | hx)
      · exact ⟨s, Or.inl rfl, hx⟩
      · exact ⟨t, Or.inr rfl, hx⟩
  · intro s t hst x hx y hy
    have hst' : (s : Finset X) ≠ t := fun h => hst (Subtype.ext h)
    obtain ⟨es, hes⟩ := hP.side s s.2
    obtain ⟨et, het⟩ := hP.side t t.2
    have key : ∀ e : G.Dart,
        (if (x ∈ side G ι e.fst e.snd ↔ y ∈ side G ι e.fst e.snd) then (0 : ℝ) else 1) =
          sepI (side G ι e.fst e.snd) s t + inner (side G ι e.fst e.snd) s x +
            inner (side G ι e.fst e.snd) t y := fun e =>
      sep_eq_sepI_add_inner (hes ▸ hSS.compat e es) (het ▸ hSS.compat e et)
        (hdisj s s.2 t t.2 hst') hx hy
    rw [dist_eq_sum_darts hT.1 hd x y, ← htree s t]
    unfold treeD
    simp only [key, mul_add, Finset.sum_add_distrib]

/-- The splits formed by a run satisfying the invariant on the sides of a binary phylogenetic
tree, once at most three clusters remain, are exactly the splits of the internal edges. -/
private lemma splits_iff_of_inv {X : Type*} [DecidableEq X] [Fintype X] {V : Type*}
    [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {ι : X → V}
    (hT : IsBinaryPhylogeneticTree G ι) {S C : Finset (Finset X)}
    (hI : Inv (fun t : G.Dart => side G ι t.fst t.snd) S C) (hS : S.card ≤ 3) (A : Finset X) :
    (A ∈ C ∨ Finset.univ \ A ∈ C) ↔
      ∃ a b, G.Adj a b ∧ a ∉ Set.range ι ∧ b ∉ Set.range ι ∧
        ∀ x, x ∈ A ↔ (G.deleteEdges {s(a, b)}).Reachable (ι x) a := by
  rw [inv_final (splitSys_side hT) hI hS A]
  constructor
  · rintro ⟨t, ht, h1, h2⟩
    have hsw : side G ι t.snd t.fst = univ \ A := (side_swap hT.1 t.adj).trans (by rw [ht])
    refine ⟨t.fst, t.snd, t.adj, ?_, ?_, fun x => ?_⟩
    · rintro ⟨z, hz⟩
      have := side_leaf hT (hz ▸ t.adj)
      rw [hz, ht] at this
      rw [this, Finset.card_singleton] at h1
      omega
    · rintro ⟨z, hz⟩
      have := side_leaf hT (hz ▸ t.adj.symm)
      rw [hz, hsw] at this
      rw [this, Finset.card_singleton] at h2
      omega
    · rw [← ht, mem_side]
  · rintro ⟨a, b, hab, ha, hb, hA⟩
    have hside : side G ι a b = A := by
      ext x
      rw [mem_side, hA]
    refine ⟨⟨(a, b), hab⟩, hside, hside ▸ two_le_card_side hT hab ha, ?_⟩
    rw [← hside, ← side_swap hT.1 hab]
    exact two_le_card_side hT hab.symm hb

/-- **Neighbor joining is exact on tree metrics.** Let `d` be the path-length metric of a
binary phylogenetic `X`-tree `(G, ι)` with positive edge lengths `w`. Then every complete run
of neighbor joining (stopped with at most three clusters) forms exactly the splits of the
internal edges of the tree: a set of taxa `A` or its complement is a formed cluster if and
only if `A` is the set of taxa on the `a`-side of an edge `{a, b}` with both endpoints
internal.

Source: Saitou & Nei (1987); Studier & Keppler (1988); Gascuel (1994); Bryant (2005).
Proves the deferred entry `njRun_splits`. -/
theorem njRun_splits {X : Type*} [DecidableEq X] [Fintype X] {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {ι : X → V} (hT : IsBinaryPhylogeneticTree G ι)
    {w : Sym2 V → ℝ} (hw : ∀ e ∈ G.edgeSet, 0 < w e) {d : X → X → ℝ}
    (hd : ∀ x y (p : G.Walk (ι x) (ι y)), p.IsPath → d x y = (p.edges.map w).sum)
    {S : Finset (Finset X)} {D : Finset X → Finset X → ℝ} {C : Finset (Finset X)}
    (hrun : NJRun d S D C) (hS : S.card ≤ 3) (A : Finset X) :
    (A ∈ C ∨ Finset.univ \ A ∈ C) ↔
      ∃ a b, G.Adj a b ∧ a ∉ Set.range ι ∧ b ∉ Set.range ι ∧
        ∀ x, x ∈ A ↔ (G.deleteEdges {s(a, b)}).Reachable (ι x) a := by
  classical
  exact splits_iff_of_inv hT
    (inv_run (splitSys_side hT) (fun t => hw _ t.edge_mem) (dist_eq_treeD hT.1 hd) hrun).1 hS A

/-- **Neighbor joining forms the splits of a tree when every join forms a side.** Let `(G, ι)`
be a binary phylogenetic `X`-tree and `D` any dissimilarity. Suppose that whenever a run of
neighbor joining on `D` has reached a partition `S` of the taxa into sides of edges of the tree
(with at least four clusters) and joins two of its clusters, their union is again a side of an
edge. Then every complete run of neighbor joining on `D` (stopped with at most three clusters)
forms exactly the splits of the internal edges of the tree. This reduces the correctness of
neighbor joining on `D` to its selection step. -/
theorem njRun_splits_of_join {X : Type*} [DecidableEq X] [Fintype X] {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {ι : X → V} (hT : IsBinaryPhylogeneticTree G ι)
    {D : X → X → ℝ}
    (hjoin : ∀ {S : Finset (Finset X)} {Dc : Finset X → Finset X → ℝ} {C : Finset (Finset X)}
      {a b : Finset X}, NJRun D S Dc C → (∀ s ∈ S, ∃ u v, G.Adj u v ∧ side G ι u v = s) →
      (∀ s ∈ S, ∀ t ∈ S, s ≠ t → Disjoint s t) → (∀ x, ∃ s ∈ S, x ∈ s) → 4 ≤ S.card →
      a ∈ S → b ∈ S → a ≠ b →
      (∀ a' ∈ S, ∀ b' ∈ S, a' ≠ b' → qCriterion S Dc a b ≤ qCriterion S Dc a' b') →
      ∃ u v, G.Adj u v ∧ side G ι u v = a ∪ b)
    {S : Finset (Finset X)} {Dc : Finset X → Finset X → ℝ} {C : Finset (Finset X)}
    (hrun : NJRun D S Dc C) (hS : S.card ≤ 3) (A : Finset X) :
    (A ∈ C ∨ Finset.univ \ A ∈ C) ↔
      ∃ a b, G.Adj a b ∧ a ∉ Set.range ι ∧ b ∉ Set.range ι ∧
        ∀ x, x ∈ A ↔ (G.deleteEdges {s(a, b)}).Reachable (ι x) a := by
  have hSS := splitSys_side hT
  have hI : Inv (fun t : G.Dart => side G ι t.fst t.snd) S C := by
    clear hS
    induction hrun with
    | init => exact inv_init hSS
    | join hr h4 ha hb hab hmin ih =>
      obtain ⟨u, v, huv, hU⟩ := hjoin hr (fun s hs => by
          obtain ⟨t, ht⟩ := ih.part.side s hs
          exact ⟨t.fst, t.snd, t.adj, ht⟩) ih.part.disj ih.part.cover h4 ha hb hab hmin
      exact inv_join hSS ih h4 ha hb hab (eU := ⟨(u, v), huv⟩) hU
  exact splits_iff_of_inv hT hI hS A

end Cslib.Bioinformatics.Phylogenetics.NeighborJoining
