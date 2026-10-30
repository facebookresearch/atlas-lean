/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
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
cherry, and NJ returns exactly the splits of the internal edges of the tree.

Sources: N. Saitou and M. Nei, "The neighbor-joining method: a new method for reconstructing
phylogenetic trees", Mol. Biol. Evol. 4 (1987) 406–425; J. A. Studier and K. J. Keppler,
"A note on the neighbor-joining algorithm of Saitou and Nei", Mol. Biol. Evol. 5 (1988)
729–731; O. Gascuel, "A note on Sattath and Tversky's, Saitou and Nei's, and Studier and
Keppler's algorithms for inferring phylogenies from evolutionary distances", Mol. Biol. Evol.
11 (1994) 961–963; D. Bryant, "On the uniqueness of the selection criterion in
neighbor-joining", J. Classif. 22 (2005) 3–15; C. Semple and M. Steel, *Phylogenetics*
(2003), ch. 7.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MathlibExt.Biology.Phylogenetics.NeighborJoiningWanted

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

/-- `G` with the taxon placement `ι` is a **binary phylogenetic `X`-tree**: `G` is a tree,
`ι` is injective, the leaves (degree-one vertices) are exactly the taxa, and every other
vertex has degree three. -/
def IsBinaryPhylogeneticTree {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ι : X → V) : Prop :=
  G.IsTree ∧ Function.Injective ι ∧ (∀ v, G.degree v = 1 ↔ v ∈ Set.range ι) ∧
    ∀ v, v ∉ Set.range ι → G.degree v = 3

/-- **Neighbor joining is exact on tree metrics.** Let `d` be the path-length metric of a
binary phylogenetic `X`-tree `(G, ι)` with positive edge lengths `w`. Then every complete run
of neighbor joining (stopped with at most three clusters) forms exactly the splits of the
internal edges of the tree: a set of taxa `A` or its complement is a formed cluster if and
only if `A` is the set of taxa on the `a`-side of an edge `{a, b}` with both endpoints
internal.

Source: Saitou & Nei (1987); Studier & Keppler (1988); Gascuel (1994); Bryant (2005). -/
theorem_wanted njRun_splits [Fintype X] {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {ι : X → V} (hT : IsBinaryPhylogeneticTree G ι) {w : Sym2 V → ℝ}
    (hw : ∀ e ∈ G.edgeSet, 0 < w e) {d : X → X → ℝ}
    (hd : ∀ x y (p : G.Walk (ι x) (ι y)), p.IsPath → d x y = (p.edges.map w).sum)
    {S : Finset (Finset X)} {D : Finset X → Finset X → ℝ} {C : Finset (Finset X)}
    (hrun : NJRun d S D C) (hS : S.card ≤ 3) (A : Finset X) :
    (A ∈ C ∨ Finset.univ \ A ∈ C) ↔
      ∃ a b, G.Adj a b ∧ a ∉ Set.range ι ∧ b ∉ Set.range ι ∧
        ∀ x, x ∈ A ↔ (G.deleteEdges {s(a, b)}).Reachable (ι x) a

end MathlibExt.Biology.Phylogenetics.NeighborJoiningWanted
