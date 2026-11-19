/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Phylogenetics.TreeBridge
import all CSLibExtTest.Bioinformatics.Phylogenetics.NeighborJoining

/-!
# Tests for the neighbor-joining / unrooted-tree bridge

Both fixtures are reused from existing tests:

* the quartet tree `01|23` of `CSLibExtTest.Bioinformatics.Phylogenetics.NeighborJoining`
  (leaves `0, 1` on vertex `4`, leaves `2, 3` on vertex `5`, with its proof
  `quartet_isBinaryPhylogeneticTree`), converted to an `UnrootedBinaryTree`;
* the three-taxon star of `MathlibExtTest.Biology.Phylogenetics.UnrootedTreeCount`, copied
  here as a local fixture (test libraries do not import each other across library boundaries)
  and converted to a neighbor-joining tree.

On the quartet, the split of the internal edge `{4, 5}` is computed twice from the definitions,
once as the neighbor-joining `side` (reachability after deleting the edge) and once as the split
`edgeSide` (comparison of distances), and both give `{0, 1}`, as `side_eq_edgeSide` predicts.
-/

namespace CSLibExtTest.Bioinformatics.Phylogenetics.TreeBridge

open Finset
open MathlibExt.Biology.Phylogenetics.UnrootedTreeCount
open Cslib.Bioinformatics.Phylogenetics.NeighborJoining
open Cslib.Bioinformatics.Phylogenetics.Splits
open Cslib.Bioinformatics.Phylogenetics.TreeBridge

/-! ## Neighbor joining to unrooted: the quartet -/

/-- The quartet tree as an `UnrootedBinaryTree` (non-vacuity of `toUnrootedBinaryTree`). -/
noncomputable def quartetT : UnrootedBinaryTree (Fin 4) :=
  toUnrootedBinaryTree quartet_isBinaryPhylogeneticTree

/-- The converted quartet keeps the placement: taxon `2` labels vertex `2`. -/
example : (quartetT.label 2).1 = (2 : Fin 6) :=
  toUnrootedBinaryTree_label quartet_isBinaryPhylogeneticTree 2

/-- Round trip: the placement read back from the converted quartet is `quartetLeaf`. -/
example : (fun x => (quartetT.label x).1) = quartetLeaf :=
  funext (toUnrootedBinaryTree_label quartet_isBinaryPhylogeneticTree)

/-- The NJ side of the internal edge, from the definition: taxa `0, 1` reach vertex `4` without
the edge `{4, 5}`, taxa `2, 3` reach vertex `5`, and the two sides partition the taxa. -/
theorem side_quartet_four_five : side quartet quartetLeaf 4 5 = {0, 1} := by
  classical
  have hsub : ∀ {a b : Fin 6} {z : Fin 4} (_ : quartet.Adj (quartetLeaf z) a)
      (_ : s(quartetLeaf z, a) ≠ s(a, b)), z ∈ side quartet quartetLeaf a b :=
    fun hz hne => by
      simp only [side, mem_filter, mem_univ, true_and]
      exact SimpleGraph.Adj.reachable (by simpa [hne] using hz)
  have h0 : (0 : Fin 4) ∈ side quartet quartetLeaf 4 5 := hsub (by decide) (by decide)
  have h1 : (1 : Fin 4) ∈ side quartet quartetLeaf 4 5 := hsub (by decide) (by decide)
  have h2 : (2 : Fin 4) ∈ side quartet quartetLeaf 5 4 := hsub (by decide) (by decide)
  have h3 : (3 : Fin 4) ∈ side quartet quartetLeaf 5 4 := hsub (by decide) (by decide)
  rw [side_swap quartet_isBinaryPhylogeneticTree.1 (by decide : quartet.Adj 4 5)] at h2 h3
  ext z
  fin_cases z <;> simp_all

/-- A taxon whose leaf is adjacent to `v` but not to `p` is on the `v`-side of `p – v`. -/
private theorem mem_edgeSide_quartetT {p v : Fin 6} {z : Fin 4}
    (hv : quartet.Adj (quartetLeaf z) v) (hp : ¬ quartet.Adj (quartetLeaf z) p)
    (hne : quartetLeaf z ≠ p) : z ∈ edgeSide quartetT p v := by
  simp only [edgeSide, mem_filter, mem_univ, true_and]
  change quartet.dist (quartetLeaf z) v < quartet.dist (quartetLeaf z) p
  have h1 : quartet.dist (quartetLeaf z) v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hv
  have hp1 : quartet.dist (quartetLeaf z) p ≠ 1 := fun h =>
    hp (SimpleGraph.dist_eq_one_iff_adj.mp h)
  have hp0 : quartet.dist (quartetLeaf z) p ≠ 0 := fun h =>
    hne ((SimpleGraph.Connected.dist_eq_zero_iff
      quartet_isBinaryPhylogeneticTree.1.connected).mp h)
  omega

/-- The split side of the internal edge, from the definition: taxa `0, 1` are at distance `1`
from vertex `4` and farther from vertex `5`, symmetrically for `2, 3`, and the two sides are
complementary. -/
theorem edgeSide_quartetT_five_four : edgeSide quartetT (5 : Fin 6) (4 : Fin 6) = {0, 1} := by
  classical
  have h0 : (0 : Fin 4) ∈ edgeSide quartetT (5 : Fin 6) (4 : Fin 6) :=
    mem_edgeSide_quartetT (by decide) (by decide) (by decide)
  have h1 : (1 : Fin 4) ∈ edgeSide quartetT (5 : Fin 6) (4 : Fin 6) :=
    mem_edgeSide_quartetT (by decide) (by decide) (by decide)
  have h2 : (2 : Fin 4) ∈ edgeSide quartetT (4 : Fin 6) (5 : Fin 6) :=
    mem_edgeSide_quartetT (by decide) (by decide) (by decide)
  have h3 : (3 : Fin 4) ∈ edgeSide quartetT (4 : Fin 6) (5 : Fin 6) :=
    mem_edgeSide_quartetT (by decide) (by decide) (by decide)
  rw [← compl_edgeSide quartetT (p := (5 : Fin 6)) (v := (4 : Fin 6))
    (by decide : quartet.Adj 5 4)] at h2 h3
  ext z
  fin_cases z <;> simp_all

/-- The bridge theorem on the quartet agrees with both computations, in the orientation
`side G ι a b = edgeSide T b a`. -/
example : side quartet quartetLeaf 4 5 = edgeSide quartetT (5 : Fin 6) (4 : Fin 6) :=
  side_eq_edgeSide quartet_isBinaryPhylogeneticTree (by decide)

example : side quartet quartetLeaf 4 5 = edgeSide quartetT (5 : Fin 6) (4 : Fin 6) := by
  rw [side_quartet_four_five, edgeSide_quartetT_five_four]

/-- The split `{0, 1}` is an NJ edge split of the quartet and an edge split of the converted
tree. -/
example : ({0, 1} : Finset (Fin 4)) ∈ sideSplits quartet quartetLeaf ∧
    ({0, 1} : Finset (Fin 4)) ∈ edgeSplits quartetT := by
  have hmem : ({0, 1} : Finset (Fin 4)) ∈ sideSplits quartet quartetLeaf := by
    rw [← side_quartet_four_five]
    exact mem_image.mpr ⟨(4, 5), mem_filter.mpr ⟨by simp, by decide⟩, rfl⟩
  exact ⟨hmem, sideSplits_eq_edgeSplits quartet_isBinaryPhylogeneticTree ▸ hmem⟩

/-! ## Unrooted to neighbor joining: the star -/

/-! Local fixture, copied from the star tree of
`MathlibExtTest/Biology/Phylogenetics/UnrootedTreeCount.lean`. -/

/-- The star with center `3` and leaves `0, 1, 2`. -/
def starGraph : SimpleGraph (Fin 4) := SimpleGraph.fromRel fun i _ => i = 3

theorem starGraph_adj (i j : Fin 4) :
    starGraph.Adj i j ↔ i ≠ j ∧ (i = 3 ∨ j = 3) := by
  rw [starGraph, SimpleGraph.fromRel_adj]

instance : DecidableRel starGraph.Adj := fun i j =>
  decidable_of_iff _ (starGraph_adj i j).symm

theorem starGraph_degree :
    ∀ v : Fin 4, starGraph.degree v = if v = 3 then 3 else 1 := by
  decide

theorem starGraph_isTree : starGraph.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  have h : ∀ v, starGraph.Reachable v 3 := by
    intro v
    by_cases hv : v = 3
    · subst hv; rfl
    · exact SimpleGraph.Adj.reachable ((starGraph_adj _ _).2 ⟨hv, Or.inr rfl⟩)
  refine ⟨⟨fun u v => (h u).trans (h v).symm⟩, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
    (by decide : starGraph.edgeFinset.card = 3)]
  simp

/-- The labeling of the leaves of the star. -/
def starLabel : Fin 3 → {v : Fin 4 // starGraph.degree v = 1} :=
  fun i => ⟨i.castSucc, by revert i; decide⟩

theorem starLabel_bijective : Function.Bijective starLabel := by decide

/-- The star with three leaves as an unrooted binary phylogenetic tree on three taxa. -/
noncomputable def star : UnrootedBinaryTree (Fin 3) where
  V := Fin 4
  G := starGraph
  isTree := starGraph_isTree
  label := Equiv.ofBijective _ starLabel_bijective
  degree_eq_three v hv := by
    rw [starGraph_degree] at hv ⊢
    split_ifs at hv ⊢ <;> simp_all

/-- The three-taxon star is a binary phylogenetic tree in the NJ sense (non-vacuity of
`isBinaryPhylogeneticTree_of_unrooted`). -/
example : IsBinaryPhylogeneticTree star.G fun x => (star.label x : star.V) :=
  isBinaryPhylogeneticTree_of_unrooted star

/-- Round trip: converting the star to NJ and back gives an isomorphic tree. -/
example : (toUnrootedBinaryTree (isBinaryPhylogeneticTree_of_unrooted star)).Iso star :=
  toUnrootedBinaryTree_iso star

end CSLibExtTest.Bioinformatics.Phylogenetics.TreeBridge
