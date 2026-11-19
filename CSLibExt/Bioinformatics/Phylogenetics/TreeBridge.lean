/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Bioinformatics.Phylogenetics.NeighborJoining
public import CSLibExt.Bioinformatics.Phylogenetics.Splits

/-!
# Bridge between neighbor-joining trees and unrooted binary trees

Two files describe the same objects in two ways. `NeighborJoining` works with a graph `G` on a
finite vertex type and a taxon placement `ι : X → V` satisfying `IsBinaryPhylogeneticTree G ι`
(a tree, `ι` injective, leaves exactly the placed taxa, other vertices of degree three). The
counting and split files work with the bundled `UnrootedBinaryTree X`, whose leaves carry a
labeling `label : X ≃ {v // G.degree v = 1}`.

This file converts both ways on the same graph and compares the two notions of the sides of an
edge. On the neighbor-joining side, `side G ι a b` is the set of taxa still joined to `a` once
the edge `{a, b}` is deleted; on the split side, `edgeSide T p v` is the set of taxa closer to
`v` than to `p`. In a tree, deleting the edge `{a, b}` leaves `z` joined to `a` exactly when `z`
is closer to `a` than to `b` (`reachable_deleteEdges_iff_dist_lt`), so
`side G ι a b = edgeSide T b a`: the near endpoint `a` of `side` is the `v` of `edgeSide`, and
the far endpoint `b` is its `p`.

## Main results

* `toUnrootedBinaryTree`, `isBinaryPhylogeneticTree_of_unrooted`: the two conversions.
* `toUnrootedBinaryTree_label`, `toUnrootedBinaryTree_iso`: the round trips.
* `reachable_deleteEdges_iff_dist_lt`: in a tree, the component of `a` after deleting the edge
  `{a, b}` is the set of vertices closer to `a` than to `b`.
* `side_eq_edgeSide`, `edgeSide_eq_side`: the side of an edge in both languages.
* `sideSplits_eq_edgeSplits`: the sides of all edges of a neighbor-joining tree are the edge
  splits of the converted tree.
-/

@[expose] public section

namespace Cslib.Bioinformatics.Phylogenetics.TreeBridge

open Finset
open MathlibExt.Biology.Phylogenetics.UnrootedTreeCount
open Cslib.Bioinformatics.Phylogenetics.NeighborJoining
open Cslib.Bioinformatics.Phylogenetics.Splits

/-! ### Conversions -/

section Conversions

variable {X V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {ι : X → V}

/-- A binary phylogenetic tree in the neighbor-joining sense, bundled as an
`UnrootedBinaryTree` on the same vertex type and graph; the taxon `x` labels the leaf `ι x`. -/
noncomputable def toUnrootedBinaryTree (h : IsBinaryPhylogeneticTree G ι) :
    UnrootedBinaryTree X where
  V := V
  G := G
  isTree := h.1
  label := Equiv.ofBijective (fun x => ⟨ι x, (h.2.2.1 (ι x)).mpr ⟨x, rfl⟩⟩)
    ⟨fun x y hxy => h.2.1 (congrArg Subtype.val hxy),
      fun v => by
        obtain ⟨x, hx⟩ := (h.2.2.1 v.1).mp v.2
        exact ⟨x, Subtype.ext hx⟩⟩
  degree_eq_three v hv := h.2.2.2 v fun hr => hv ((h.2.2.1 v).mpr hr)

/-- **Round trip from neighbor joining.** The converted tree has the same graph, and its leaf
labeling places each taxon where `ι` did. -/
theorem toUnrootedBinaryTree_label (h : IsBinaryPhylogeneticTree G ι) (x : X) :
    ((toUnrootedBinaryTree h).label x).1 = ι x :=
  rfl

theorem toUnrootedBinaryTree_G (h : IsBinaryPhylogeneticTree G ι) :
    (toUnrootedBinaryTree h).G = G :=
  rfl

end Conversions

/-- The leaf labeling of an `UnrootedBinaryTree`, read as a taxon placement, makes its graph a
binary phylogenetic tree in the neighbor-joining sense. -/
theorem isBinaryPhylogeneticTree_of_unrooted {X : Type} (T : UnrootedBinaryTree X) :
    IsBinaryPhylogeneticTree T.G fun x => (T.label x : T.V) := by
  refine ⟨T.isTree, fun x y hxy => T.label.injective (Subtype.ext hxy), fun v => ?_,
    fun v hv => T.degree_eq_three v fun h1 => hv ?_⟩
  · refine ⟨fun h1 => ⟨T.label.symm ⟨v, h1⟩, by simp⟩, ?_⟩
    rintro ⟨x, rfl⟩
    exact (T.label x).2
  · exact ⟨T.label.symm ⟨v, h1⟩, by simp⟩

/-- **Round trip from unrooted trees.** Converting the labeled leaves to a placement and back
gives a tree isomorphic to the original, by the identity graph isomorphism. -/
theorem toUnrootedBinaryTree_iso {X : Type} (T : UnrootedBinaryTree X) :
    (toUnrootedBinaryTree (isBinaryPhylogeneticTree_of_unrooted T)).Iso T :=
  ⟨SimpleGraph.Iso.refl, fun _ => rfl⟩

/-- The same isomorphism, in the other direction. -/
theorem iso_toUnrootedBinaryTree {X : Type} (T : UnrootedBinaryTree X) :
    T.Iso (toUnrootedBinaryTree (isBinaryPhylogeneticTree_of_unrooted T)) :=
  ⟨SimpleGraph.Iso.refl, fun _ => rfl⟩

/-! ### Deleting an edge of a tree -/

section TreeDistance

variable {V : Type} {G : SimpleGraph V}

/-- A vertex on a walk splits its length into two parts, each at least a distance. -/
private theorem dist_add_dist_le_length {x y c : V} (q : G.Walk x y) (hc : c ∈ q.support) :
    G.dist x c + G.dist c y ≤ q.length := by
  classical
  have h := congrArg SimpleGraph.Walk.length (q.take_spec hc)
  rw [SimpleGraph.Walk.length_append] at h
  have h1 := SimpleGraph.dist_le (q.takeUntil c hc)
  have h2 := SimpleGraph.dist_le (q.dropUntil c hc)
  omega

/-- If `z` is closer to `a` than to its neighbor `b`, a shortest walk from `z` to `a` avoids
the edge `{a, b}`. -/
private theorem reachable_of_dist_lt (hG : G.Connected) {a b z : V} (hab : G.Adj a b)
    (hlt : G.dist z a < G.dist z b) : (G.deleteEdges {s(a, b)}).Reachable z a := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist z a
  have hnot : s(a, b) ∉ p.edges := by
    intro he
    have hb := dist_add_dist_le_length p (p.snd_mem_support_of_mem_edges he)
    have h1 : G.dist b a = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hab.symm
    omega
  exact ⟨p.toDeleteEdge _ hnot⟩

/-- **Deleting an edge of a tree.** After deleting the edge `{a, b}` of a tree, the vertices
still joined to `a` are exactly those closer to `a` than to `b`. -/
theorem reachable_deleteEdges_iff_dist_lt (hG : G.IsTree) {a b : V} (hab : G.Adj a b) (z : V) :
    (G.deleteEdges {s(a, b)}).Reachable z a ↔ G.dist z a < G.dist z b := by
  refine ⟨fun hr => ?_, reachable_of_dist_lt hG.connected hab⟩
  rcases hG.dist_eq_dist_add_one_of_adj z hab with h | h
  · exfalso
    have hrb := reachable_of_dist_lt hG.connected hab.symm (by omega : G.dist z b < G.dist z a)
    rw [Sym2.eq_swap] at hrb
    exact SimpleGraph.isBridge_iff.mp
      (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hG.isAcyclic hab) (hr.symm.trans hrb)
  · omega

end TreeDistance

/-! ### Sides of edges -/

section Sides

variable {X V : Type} [Fintype X] [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {ι : X → V}

/-- **Sides of an edge.** On a binary phylogenetic tree, the neighbor-joining side `side G ι a b`
(taxa still joined to `a` once `{a, b}` is deleted) is the split side `edgeSide T b a` (taxa
closer to `a` than to `b`) of the converted tree. -/
theorem side_eq_edgeSide (h : IsBinaryPhylogeneticTree G ι) {a b : V} (hab : G.Adj a b) :
    side G ι a b = edgeSide (toUnrootedBinaryTree h) b a := by
  ext z
  classical
  simp only [side, edgeSide, mem_filter, mem_univ, true_and]
  exact reachable_deleteEdges_iff_dist_lt h.1 hab (ι z)

/-- The split side `edgeSide T p v` of an unrooted binary tree is the neighbor-joining side
`side T.G _ v p` for the leaf placement of `T`. -/
theorem edgeSide_eq_side (T : UnrootedBinaryTree X) {p v : T.V} (hpv : T.G.Adj p v) :
    edgeSide T p v = side T.G (fun x => (T.label x : T.V)) v p := by
  ext z
  classical
  simp only [side, edgeSide, mem_filter, mem_univ, true_and]
  exact (reachable_deleteEdges_iff_dist_lt T.isTree hpv.symm (T.label z)).symm

/-- The neighbor-joining split family: the sides `side G ι a b` of all edges, both
orientations. It mirrors `edgeSplits` on an `UnrootedBinaryTree`. -/
noncomputable def sideSplits [DecidableEq X] (G : SimpleGraph V) [DecidableRel G.Adj] (ι : X → V) :
    Finset (Finset X) :=
  ((univ ×ˢ univ).filter fun e : V × V => G.Adj e.1 e.2).image fun e => side G ι e.1 e.2

/-- **Splits correspondence.** The sides of the edges of a binary phylogenetic tree are the edge
splits of the converted tree. -/
theorem sideSplits_eq_edgeSplits [DecidableEq X] (h : IsBinaryPhylogeneticTree G ι) :
    sideSplits G ι = edgeSplits (toUnrootedBinaryTree h) := by
  ext A
  simp only [sideSplits, edgeSplits, mem_image, mem_filter, mem_product, mem_univ, true_and,
    Prod.exists]
  constructor
  · rintro ⟨a, b, hab, rfl⟩
    exact ⟨b, a, hab.symm, (side_eq_edgeSide h hab).symm⟩
  · rintro ⟨p, v, hpv, rfl⟩
    exact ⟨v, p, hpv.symm, side_eq_edgeSide h hpv.symm⟩

end Sides

end Cslib.Bioinformatics.Phylogenetics.TreeBridge
