/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Graph.Connected.EdgeCut
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Paths
import all Mathlib.Combinatorics.Graph.Connected.EdgeCut
import Mathlib.Data.Fintype.EquivFin

/-!
# Blobs and the tree of blobs of a multigraph

A **blob** of a multigraph `G` (Allman–Baños–Mitchell–Rhodes 2023, Definition 7) is a maximal
connected subgraph of `G` that contains no cut edge of `G`. This differs slightly from the blobs of
Gusfield–Bansal–Bafna–Song 2007, maximal edge sets built from cycles that share edges, under which
two cycles meeting at a single vertex are two blobs rather than one. Here a cut edge is Mathlib's
`Graph.IsBridge`, an edge that alone forms an edge cut; on a finite graph this is exactly an edge
whose deletion increases the number of connected components
(`Graph.isBridge_iff_natCard_connectedComponent_lt`). Connectivity of a multigraph is that of
its simple graph `Graph.toSimpleGraph`, which only forgets loops and parallel edges.

The blobs are the connected components of the graph left after deleting every cut edge
(`Graph.isBlob_iff`; Allman et al. note that they are also its 2-edge-connected components, after
Xu–Ané), so every vertex lies in exactly one blob (`Graph.exists_isBlob_mem`,
`Graph.IsBlob.eq_of_mem`). An edge is incident to a blob `H` if exactly one of its ends lies in
`H`: these are the edges of the edge cut `G.edgeCut V(H)`. A blob is an `m`-blob if it has exactly
`m` incident cut edges (`Graph.IsMBlob`); in a rooted graph, the blob containing the root counts
the root as one more incident edge (`Graph.IsRootedMBlob`). These counts are cardinalities in
`ℕ∞` (`Set.encard`), so a blob with infinitely many incident cut edges is an `m`-blob for no `m`.

The **tree of blobs** `Graph.treeOfBlobs` contracts every blob to a single vertex: its vertices
are the blobs, two of them adjacent when an edge of `G` joins them (Xu–Ané 2023 give this
description; for a connected graph it is a tree). `SimpleGraph.suppressDegreeTwo` suppresses the
vertices of degree two of a graph, replacing each maximal path through such vertices by one edge;
applied to the tree of blobs of a phylogenetic network it gives the reduced tree of blobs.

## Main results

* `Graph.isBridge_iff_not_reachable`: an edge is a cut edge iff its ends are no longer joined
  once it is deleted.
* `Graph.isBridge_iff_natCard_connectedComponent_lt`: on a finite graph, an edge is a cut edge
  iff deleting it increases the number of connected components.
* `Graph.isBlob_iff`: the blobs are the components of the graph without its cut edges.
* `Graph.IsBlob.vertexSet_subset`: blobs do not cross cut edges.
* `Graph.isTrivialBlob_induce_singleton`: a vertex all of whose edges are cut edges is a trivial
  blob.
* `Graph.subsingleton_neighborSet_treeOfBlobs`: a vertex with a single incident edge, which is
  not a loop, lies in a blob with at most one neighbour in the tree of blobs.

## References

* D. Gusfield, V. Bansal, V. Bafna and Y. S. Song, *A decomposition theory for phylogenetic
  networks and incompatible characters*, J. Comput. Biol. 14 (2007), 1247–1272.
* E. S. Allman, H. Baños, J. D. Mitchell and J. A. Rhodes, *The tree of blobs of a species
  network: identifiability under the coalescent*, J. Math. Biol. 86 (2023), 10, Definitions 2, 7
  and 10.
* J. Xu and C. Ané, *Identifiability of local and global features of phylogenetic networks from
  average distances*, J. Math. Biol. 86 (2023), 12.
-/

@[expose] public section

open Set

namespace Graph

variable {α β : Type*} {G H K : Graph α β} {e f : β} {u v x y : α}

/-! ### Reachability -/

/-- Two vertices of `G` are joined in its simple graph exactly when a chain of adjacencies of `G`
joins them. -/
theorem toSimpleGraph_reachable_iff {x y : V(G)} :
    G.toSimpleGraph.Reachable x y ↔ Relation.ReflTransGen G.Adj x y := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact .refl
    | cons h _ ih => exact .head h.2 ih
  · intro h
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    simp only at h
    induction h with
    | refl => rfl
    | @tail b c _ hbc ih =>
      refine (ih hbc.left_mem).trans ?_
      by_cases hb : b = c
      · subst hb
        rfl
      · exact SimpleGraph.Adj.reachable ⟨fun h ↦ hb (congrArg Subtype.val h), hbc⟩

/-! ### Cut edges -/

/-- The edges between a set of vertices and its complement form an edge cut. -/
theorem isEdgeCut_edgeCut (G : Graph α β) (S : Set α) : G.IsEdgeCut (G.edgeCut S) := ⟨S, rfl⟩

/-- An edge is a cut edge exactly when it is the only edge between some set of vertices and its
complement. -/
theorem isBridge_iff_exists_edgeCut_eq : G.IsBridge e ↔ ∃ S, G.edgeCut S = {e} := Iff.rfl

/-- **An edge is a cut edge iff deleting it separates its ends**: the edge `e` with ends `u` and
`v` is a bridge of `G` exactly when no chain of adjacencies of `G` without `e` joins `u` to `v`. -/
theorem isBridge_iff_not_reachable (he : G.IsLink e u v) :
    G.IsBridge e ↔ ¬ Relation.ReflTransGen (G.deleteEdges {e}).Adj u v := by
  constructor
  · rintro ⟨S, hS⟩ hreach
    -- along a chain avoiding `e`, membership in `S` never changes
    have hstep : ∀ ⦃a b⦄, (G.deleteEdges {e}).Adj a b → (a ∈ S ↔ b ∈ S) := by
      rintro a b ⟨f, hf, hfe⟩
      have hcut : ∀ ⦃p q⦄, G.IsLink f p q → p ∈ S → q ∈ S := by
        intro p q hpq hp
        by_contra hq
        exact hfe (hS ▸ (show f ∈ G.edgeCut S from ⟨p, q, hpq, hp, hq⟩))
      exact ⟨hcut hf, hcut hf.symm⟩
    have hiff : ∀ w, Relation.ReflTransGen (G.deleteEdges {e}).Adj u w → (u ∈ S ↔ w ∈ S) := by
      intro w hw
      induction hw with
      | refl => rfl
      | tail _ hbc ih => exact ih.trans (hstep hbc)
    have hiff := hiff v hreach
    have heS : e ∈ G.edgeCut S := hS ▸ rfl
    rw [he.mem_edgeCut_iff] at heS
    tauto
  · intro hreach
    refine ⟨{w | Relation.ReflTransGen (G.deleteEdges {e}).Adj u w}, ?_⟩
    ext f
    simp only [mem_edgeCut_iff, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨p, q, hpq, hp, hq⟩
      by_contra hfe
      exact hq (hp.tail ⟨f, hpq, hfe⟩)
    · rintro rfl
      exact ⟨u, v, he, .refl, hreach⟩

/-- A loop is not a cut edge. -/
theorem not_isBridge_of_isLink_self (he : G.IsLink e x x) : ¬ G.IsBridge e := by
  rintro ⟨S, hS⟩
  have heS : e ∈ G.edgeCut S := hS ▸ rfl
  rw [he.mem_edgeCut_iff] at heS
  tauto

/-- Deleting an edge whose ends stay joined does not disconnect anything: every chain of
adjacencies of `G` gives one of `G` without `e`. -/
theorem reflTransGen_deleteEdges_of_reachable (he : G.IsLink e u v)
    (huv : Relation.ReflTransGen (G.deleteEdges {e}).Adj u v)
    (h : Relation.ReflTransGen G.Adj x y) :
    Relation.ReflTransGen (G.deleteEdges {e}).Adj x y := by
  induction h with
  | refl => exact .refl
  | @tail b c _ hbc ih =>
    obtain ⟨f, hf⟩ := hbc
    by_cases hfe : f = e
    · subst hfe
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := he.eq_and_eq_or_eq_and_eq hf
      · exact ih.trans huv
      · exact ih.trans (symm huv)
    · exact ih.tail ⟨f, hf, hfe⟩

/-- The identity map of the vertices, as a homomorphism from the simple graph of `G` without some
edges to that of `G`. -/
private def deleteEdgesToSimpleGraphHom (G : Graph α β) (F : Set β) :
    (G.deleteEdges F).toSimpleGraph →g G.toSimpleGraph where
  toFun x := x
  map_rel' h := ⟨h.1, h.2.mono deleteEdges_le⟩

/-- **A cut edge is an edge whose deletion increases the number of connected components.** For
an edge `e` of a graph with finitely many vertices, `G.IsBridge e` holds exactly when `G` without
`e` has more connected components than `G`. -/
theorem isBridge_iff_natCard_connectedComponent_lt [Finite α] (he : e ∈ E(G)) :
    G.IsBridge e ↔ Nat.card G.toSimpleGraph.ConnectedComponent <
      Nat.card (G.deleteEdges {e}).toSimpleGraph.ConnectedComponent := by
  obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet he
  let φ := SimpleGraph.ConnectedComponent.map (G.deleteEdgesToSimpleGraphHom {e})
  have hsurj : Function.Surjective φ := by
    intro c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h w => exact ⟨(G.deleteEdges {e}).toSimpleGraph.connectedComponentMk w, rfl⟩
  have : Fintype G.toSimpleGraph.ConnectedComponent := Fintype.ofFinite _
  have : Fintype (G.deleteEdges {e}).toSimpleGraph.ConnectedComponent := Fintype.ofFinite _
  simp only [Nat.card_eq_fintype_card]
  rw [isBridge_iff_not_reachable huv]
  constructor
  · intro hreach
    refine Fintype.card_lt_of_surjective_not_injective φ hsurj fun hinj ↦ hreach ?_
    have hne : u ≠ v := by
      rintro rfl
      exact hreach .refl
    let u' : V(G.deleteEdges {e}) := ⟨u, huv.left_mem⟩
    let v' : V(G.deleteEdges {e}) := ⟨v, huv.right_mem⟩
    have heq : φ ((G.deleteEdges {e}).toSimpleGraph.connectedComponentMk u') =
        φ ((G.deleteEdges {e}).toSimpleGraph.connectedComponentMk v') := by
      simp only [φ, SimpleGraph.ConnectedComponent.map_mk]
      exact SimpleGraph.ConnectedComponent.sound
        (SimpleGraph.Adj.reachable ⟨fun h ↦ hne (congrArg Subtype.val h), huv.adj⟩)
    have := SimpleGraph.ConnectedComponent.exact (hinj heq)
    exact toSimpleGraph_reachable_iff.1 this
  · intro hlt hreach
    refine hlt.ne' (Fintype.card_congr (Equiv.ofBijective φ ⟨fun c d hcd ↦ ?_, hsurj⟩))
    induction c using SimpleGraph.ConnectedComponent.ind with | h a =>
    induction d using SimpleGraph.ConnectedComponent.ind with | h b =>
    simp only [φ, SimpleGraph.ConnectedComponent.map_mk] at hcd
    have hab := toSimpleGraph_reachable_iff.1 (SimpleGraph.ConnectedComponent.exact hcd)
    exact SimpleGraph.ConnectedComponent.sound (toSimpleGraph_reachable_iff.2
      (reflTransGen_deleteEdges_of_reachable huv hreach hab))

/-! ### Blobs -/

/-- A **blob** of `G` (Allman–Baños–Mitchell–Rhodes 2023, Definition 7): a subgraph `H` of `G`
that is connected, contains no cut edge (`Graph.IsBridge`) of `G`, and is maximal for the
subgraph order with these two properties. The blobs of `G` are the components of `G` without its
cut edges (`Graph.isBlob_iff`). -/
def IsBlob (G H : Graph α β) : Prop :=
  Maximal (fun K : Graph α β ↦ K ≤ G ∧ K.toSimpleGraph.Connected ∧ ∀ e ∈ E(K), ¬ G.IsBridge e) H

/-- A blob is **trivial** if it consists of a single vertex. -/
def IsTrivialBlob (G H : Graph α β) : Prop :=
  G.IsBlob H ∧ ∃ v, V(H) = {v}

/-- An **`m`-blob** of an unrooted graph: a blob with exactly `m` incident cut edges. An edge is
incident to the blob `H` when exactly one of its ends lies in `H`, that is, when it lies in the
edge cut `G.edgeCut V(H)`. The count is a cardinality in `ℕ∞`, so a blob with infinitely many
incident cut edges is an `m`-blob for no `m`. -/
def IsMBlob (G : Graph α β) (m : ℕ) (H : Graph α β) : Prop :=
  G.IsBlob H ∧ (G.edgeCut V(H) ∩ {e | G.IsBridge e}).encard = m

/-- An **`m`-blob** of a graph rooted at `r` (Allman–Baños–Mitchell–Rhodes 2023, Definition 7): a
blob with exactly `m` incident cut edges that does not contain the root, or with exactly `m - 1`
incident cut edges that contains it (the count plus one is `m`, rather than the count is `m - 1`
in truncated subtraction, so that no blob containing the root is a `0`-blob). The count is a
cardinality in `ℕ∞`, so a blob with infinitely many incident cut edges is an `m`-blob for no `m`.
So the root of a rooted binary tree, with its two cut edges, is a trivial `3`-blob. -/
def IsRootedMBlob (G : Graph α β) (r : α) (m : ℕ) (H : Graph α β) : Prop :=
  G.IsBlob H ∧
    (r ∉ V(H) ∧ (G.edgeCut V(H) ∩ {e | G.IsBridge e}).encard = m ∨
      r ∈ V(H) ∧ (G.edgeCut V(H) ∩ {e | G.IsBridge e}).encard + 1 = m)

section characterization

/-- The component of `x` in `G` without its cut edges, as an induced subgraph of that graph. -/
private abbrev comp (G : Graph α β) (x : α) : Graph α β :=
  (G.deleteEdges {e | G.IsBridge e}).induce
    {y | Relation.ReflTransGen (G.deleteEdges {e | G.IsBridge e}).Adj x y}

/-- A subgraph of `G` with no cut edge of `G` is a subgraph of `G` without its cut edges. -/
private theorem le_deleteEdges_isBridge (hKG : K ≤ G) (hK : ∀ e ∈ E(K), ¬ G.IsBridge e) :
    K ≤ G.deleteEdges {e | G.IsBridge e} where
  vertexSet_mono := hKG.vertexSet_mono
  isLink_mono _ _ _ h := ⟨h.mono hKG, hK _ h.edge_mem⟩

/-- A connected subgraph of `G` without cut edges, through `x`, lies in the component of `x` in
`G` without its cut edges. -/
private theorem le_comp (hKG : K ≤ G) (hconn : K.toSimpleGraph.Connected)
    (hK : ∀ e ∈ E(K), ¬ G.IsBridge e) (hx : x ∈ V(K)) : K ≤ comp G x := by
  have hle := le_deleteEdges_isBridge hKG hK
  have hreach : ∀ y ∈ V(K), Relation.ReflTransGen (G.deleteEdges {e | G.IsBridge e}).Adj x y :=
    fun y hy ↦ Relation.ReflTransGen.mono (fun _ _ h ↦ h.mono hle) _ _
      (toSimpleGraph_reachable_iff.1 (hconn.preconnected ⟨x, hx⟩ ⟨y, hy⟩))
  exact ⟨fun y hy ↦ hreach y hy, fun e a b h ↦
    ⟨h.mono hle, hreach a h.left_mem, hreach b h.right_mem⟩⟩

/-- The component of a vertex in `G` without its cut edges is a connected subgraph of `G` with
no cut edge. -/
private theorem comp_prop (hx : x ∈ V(G)) :
    comp G x ≤ G ∧ (comp G x).toSimpleGraph.Connected ∧ ∀ e ∈ E(comp G x), ¬ G.IsBridge e := by
  set G' := G.deleteEdges {e | G.IsBridge e}
  set C := {y | Relation.ReflTransGen G'.Adj x y}
  -- a chain from `x` in `G'` is a chain in the induced subgraph
  have hind : ∀ y, Relation.ReflTransGen G'.Adj x y →
      Relation.ReflTransGen (G'.induce C).Adj x y := by
    intro y h
    induction h with
    | refl => exact .refl
    | @tail b c hxb hbc ih =>
      obtain ⟨f, hf⟩ := hbc
      exact ih.tail ⟨f, hf, hxb, hxb.tail ⟨f, hf⟩⟩
  have hCV : C ⊆ V(G) := by
    intro y hy
    induction hy with
    | refl => exact hx
    | tail _ hbc _ => exact hbc.right_mem
  change G'.induce C ≤ G ∧ (G'.induce C).toSimpleGraph.Connected ∧
    ∀ e ∈ E(G'.induce C), ¬ G.IsBridge e
  refine ⟨(induce_le (G := G') hCV).trans deleteEdges_le, ?_, fun e he hbr ↦ ?_⟩
  · have : Nonempty V(G'.induce C) := ⟨⟨x, Relation.ReflTransGen.refl⟩⟩
    refine ⟨fun a b ↦ toSimpleGraph_reachable_iff.2 ?_⟩
    exact (symm (hind _ a.2)).trans (hind _ b.2)
  · obtain ⟨a, b, hab⟩ := exists_isLink_of_mem_edgeSet he
    exact hab.1.2 hbr

/-- The component of a vertex in `G` without its cut edges is a blob. -/
private theorem isBlob_comp (hx : x ∈ V(G)) : G.IsBlob (comp G x) :=
  ⟨comp_prop hx, fun _ hK hle ↦ le_comp hK.1 hK.2.1 hK.2.2
    (hle.vertexSet_mono (Relation.ReflTransGen.refl : Relation.ReflTransGen _ x x))⟩

/-- **The blobs are the components of the graph without its cut edges**: `H` is a blob of `G`
exactly when it is, for some vertex `x` of `G`, the subgraph induced by the cut-edge-free graph
on the vertices it joins to `x` (Allman–Baños–Mitchell–Rhodes 2023, after Definition 7). -/
theorem isBlob_iff :
    G.IsBlob H ↔ ∃ x ∈ V(G), H = (G.deleteEdges {e | G.IsBridge e}).induce
      {y | Relation.ReflTransGen (G.deleteEdges {e | G.IsBridge e}).Adj x y} := by
  constructor
  · intro hH
    obtain ⟨hHG, hconn, hbr⟩ := hH.prop
    obtain ⟨⟨x, hx⟩⟩ := hconn.nonempty
    refine ⟨x, hHG.vertexSet_mono hx, ?_⟩
    have hle := le_comp hHG hconn hbr hx
    exact le_antisymm hle (hH.2 (comp_prop (hHG.vertexSet_mono hx)) hle)
  · rintro ⟨x, hx, rfl⟩
    exact isBlob_comp hx

end characterization

/-- A blob is a subgraph. -/
theorem IsBlob.le (hH : G.IsBlob H) : H ≤ G := hH.prop.1

/-- A blob is connected. -/
theorem IsBlob.connected (hH : G.IsBlob H) : H.toSimpleGraph.Connected := hH.prop.2.1

/-- A blob contains no cut edge. -/
theorem IsBlob.not_isBridge (hH : G.IsBlob H) (he : e ∈ E(H)) : ¬ G.IsBridge e :=
  hH.prop.2.2 e he

/-- Every vertex lies in a blob. -/
theorem exists_isBlob_mem (hx : x ∈ V(G)) : ∃ H, G.IsBlob H ∧ x ∈ V(H) :=
  ⟨_, isBlob_iff.2 ⟨x, hx, rfl⟩, Relation.ReflTransGen.refl⟩

/-- Two blobs that share a vertex are equal. -/
theorem IsBlob.eq_of_mem (hH : G.IsBlob H) (hK : G.IsBlob K) (hxH : x ∈ V(H)) (hxK : x ∈ V(K)) :
    H = K := by
  obtain ⟨a, -, rfl⟩ := isBlob_iff.1 hH
  obtain ⟨b, -, rfl⟩ := isBlob_iff.1 hK
  have hcomp : ∀ {a}, Relation.ReflTransGen (G.deleteEdges {e | G.IsBridge e}).Adj a x →
      {y | Relation.ReflTransGen (G.deleteEdges {e | G.IsBridge e}).Adj a y} =
        {y | Relation.ReflTransGen (G.deleteEdges {e | G.IsBridge e}).Adj x y} := by
    intro a hax
    ext y
    exact ⟨fun hay ↦ (symm hax).trans hay, fun hxy ↦ hax.trans hxy⟩
  change Relation.ReflTransGen _ a x at hxH
  change Relation.ReflTransGen _ b x at hxK
  rw [hcomp hxH, hcomp hxK]

/-- The blob containing a vertex `x` of `G`. -/
noncomputable def blobOf (G : Graph α β) (hx : x ∈ V(G)) : {H // G.IsBlob H} :=
  ⟨(exists_isBlob_mem hx).choose, (exists_isBlob_mem hx).choose_spec.1⟩

theorem mem_blobOf (hx : x ∈ V(G)) : x ∈ V((G.blobOf hx).1) :=
  (exists_isBlob_mem hx).choose_spec.2

/-- A blob containing `x` is the blob of `x`. -/
theorem IsBlob.eq_blobOf (hH : G.IsBlob H) (hxH : x ∈ V(H)) (hx : x ∈ V(G)) :
    H = (G.blobOf hx).1 :=
  hH.eq_of_mem (G.blobOf hx).2 hxH (mem_blobOf hx)

/-- There are finitely many blobs in a graph with finitely many vertices. -/
instance finite_isBlob [Finite α] : Finite {H // G.IsBlob H} := by
  refine Finite.of_surjective (fun x : V(G) ↦ G.blobOf x.2) fun B ↦ ?_
  obtain ⟨⟨x, hx⟩⟩ := B.2.connected.nonempty
  exact ⟨⟨x, B.2.le.vertexSet_mono hx⟩, Subtype.ext (B.2.eq_blobOf hx _).symm⟩

/-- **A vertex all of whose edges are cut edges is a trivial blob**: the subgraph consisting of
the vertex `x` alone is then a blob of `G`. -/
theorem isTrivialBlob_induce_singleton (hx : x ∈ V(G))
    (h : ∀ e y, G.IsLink e x y → G.IsBridge e) : G.IsTrivialBlob (G.induce {x}) := by
  -- a connected subgraph without cut edges through `x` has no edge at `x`, so it is `x` alone
  have hK : ∀ K, K ≤ G → K.toSimpleGraph.Connected → (∀ e ∈ E(K), ¬ G.IsBridge e) →
      x ∈ V(K) → K ≤ G.induce {x} := by
    intro K hKG hconn hbr hxK
    have hV : ∀ y ∈ V(K), y = x := by
      intro y hy
      by_contra hyx
      have hreach : Relation.ReflTransGen K.Adj x y :=
        toSimpleGraph_reachable_iff.1 (hconn.preconnected ⟨x, hxK⟩ ⟨y, hy⟩)
      obtain ⟨z, ⟨f, hf⟩, -⟩ := (Relation.ReflTransGen.cases_head hreach).resolve_left
        (fun h ↦ hyx h.symm)
      exact hbr f hf.edge_mem (h f z (hf.mono hKG))
    refine ⟨fun y hy ↦ hV y hy, fun e a b hab ↦ ?_⟩
    obtain rfl := hV a hab.left_mem
    obtain rfl := hV b hab.right_mem
    exact absurd (h e _ (hab.mono hKG)) (hbr e hab.edge_mem)
  have hprop : G.induce {x} ≤ G ∧ (G.induce {x}).toSimpleGraph.Connected ∧
      ∀ e ∈ E(G.induce {x}), ¬ G.IsBridge e := by
    refine ⟨induce_le (by simpa using hx), ?_, fun e he ↦ ?_⟩
    · have : Nonempty V(G.induce {x}) := ⟨⟨x, rfl⟩⟩
      refine ⟨fun a b ↦ ?_⟩
      obtain ⟨a, rfl⟩ := a
      obtain ⟨b, rfl⟩ := b
      rfl
    · obtain ⟨a, b, hab, rfl, rfl⟩ := he
      exact not_isBridge_of_isLink_self hab
  exact ⟨⟨hprop, fun K hKP hle ↦ hK K hKP.1 hKP.2.1 hKP.2.2 (hle.vertexSet_mono rfl)⟩, x, rfl⟩

/-! ### The tree of blobs -/

/-- The **tree of blobs** of `G` (Gusfield et al. 2007; Allman–Baños–Mitchell–Rhodes 2023,
Definition 10), obtained by contracting every blob to a single vertex: its vertices are the blobs
of `G`, and two distinct blobs are adjacent when an edge of `G` has one end in each. Such an edge
is a cut edge, as the edges that are not lie inside blobs, and no two cut edges join the same two
blobs, so contracting the blobs leaves a simple graph; for a connected graph it is a tree. -/
def treeOfBlobs (G : Graph α β) : SimpleGraph {H // G.IsBlob H} where
  Adj H K := H ≠ K ∧ ∃ e x y, G.IsLink e x y ∧ x ∈ V(H.1) ∧ y ∈ V(K.1)
  symm := ⟨fun _ _ ⟨hne, e, x, y, h, hx, hy⟩ ↦ ⟨hne.symm, e, y, x, h.symm, hy, hx⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- **A pendant edge is a cut edge**: an edge `e` joining `x` to another vertex is a cut edge when
it is the only edge at `x`. -/
theorem isBridge_of_forall_isLink_eq (he : G.IsLink e x y) (hxy : x ≠ y)
    (h : ∀ f z, G.IsLink f x z → f = e) : G.IsBridge e := by
  refine ⟨{x}, ?_⟩
  ext f
  simp only [mem_edgeCut_iff, mem_singleton_iff]
  constructor
  · rintro ⟨a, b, hab, rfl, -⟩
    exact h f b hab
  · rintro rfl
    exact ⟨x, y, he, rfl, hxy.symm⟩

/-- A blob contains both ends of every edge at it that is not a cut edge. -/
theorem IsBlob.mem_of_isLink (hH : G.IsBlob H) (hu : u ∈ V(H)) (he : G.IsLink e u v)
    (hbr : ¬ G.IsBridge e) : v ∈ V(H) := by
  obtain ⟨x, -, rfl⟩ := isBlob_iff.1 hH
  exact Relation.ReflTransGen.tail hu ⟨e, he, hbr⟩

/-- **Blobs do not cross cut edges**: if every edge between a set `S` of vertices and its complement
is a cut edge, a blob that meets `S` lies in `S`. -/
theorem IsBlob.vertexSet_subset (hH : G.IsBlob H) {S : Set α} (hx : x ∈ V(H)) (hxS : x ∈ S)
    (hS : ∀ e ∈ G.edgeCut S, G.IsBridge e) : V(H) ⊆ S := by
  intro y hy
  have hreach : Relation.ReflTransGen H.Adj x y :=
    toSimpleGraph_reachable_iff.1 (hH.connected.preconnected ⟨x, hx⟩ ⟨y, hy⟩)
  induction hreach with
  | refl => exact hxS
  | @tail b c _ hbc ih =>
    obtain ⟨f, hf⟩ := hbc
    by_contra hc
    exact hH.not_isBridge hf.edge_mem
      (hS f ⟨b, c, hf.mono hH.le, ih hf.left_mem, hc⟩)

/-- If every edge at `x` is one and the same edge, which is not a loop, then the blob containing `x`
consists of `x` alone. -/
theorem IsBlob.vertexSet_eq_singleton (hB : G.IsBlob H) (hxH : x ∈ V(H))
    (hx : ∀ e f y z, G.IsLink e x y → G.IsLink f x z → e = f) (hloop : ∀ e, ¬ G.IsLink e x x) :
    V(H) = {x} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨hxH, fun y hy ↦ ?_⟩
  by_contra hyx
  have hreach : Relation.ReflTransGen H.Adj x y :=
    toSimpleGraph_reachable_iff.1 (hB.connected.preconnected ⟨x, hxH⟩ ⟨y, hy⟩)
  obtain ⟨z, ⟨f, hf⟩, -⟩ := (Relation.ReflTransGen.cases_head hreach).resolve_left
    (fun h ↦ hyx h.symm)
  have hfG : G.IsLink f x z := hf.mono hB.le
  exact hB.not_isBridge hf.edge_mem (isBridge_of_forall_isLink_eq hfG
    (fun hxz ↦ hloop f (hxz ▸ hfG)) fun g w hg ↦ hx _ _ _ _ hg hfG)

/-- **A pendant vertex is a blob of degree at most one in the tree of blobs.** If every edge at
`x` is one and the same edge, which is not a loop, then the blob containing `x` consists of `x`
alone and is adjacent to at most one blob in the tree of blobs (to none when `x` is isolated). -/
theorem subsingleton_neighborSet_treeOfBlobs (B : {H // G.IsBlob H}) (hxB : x ∈ V(B.1))
    (hx : ∀ e f y z, G.IsLink e x y → G.IsLink f x z → e = f) (hloop : ∀ e, ¬ G.IsLink e x x) :
    (G.treeOfBlobs.neighborSet B).Subsingleton := by
  have hV := B.2.vertexSet_eq_singleton hxB hx hloop
  rintro K₁ ⟨-, e₁, p₁, q₁, h₁, hp₁, hq₁⟩ K₂ ⟨-, e₂, p₂, q₂, h₂, hp₂, hq₂⟩
  rw [hV, mem_singleton_iff] at hp₁ hp₂
  subst hp₁ hp₂
  obtain rfl := hx _ _ _ _ h₁ h₂
  obtain rfl := h₁.right_unique h₂
  exact Subtype.ext (K₁.2.eq_of_mem K₂.2 hq₁ hq₂)

end Graph

namespace SimpleGraph

variable {V : Type*}

/-- **Suppressing the vertices of degree two** of `G`. The vertices are those of `G` whose degree
(the number of neighbours, `(G.neighborSet v).ncard`) is not `2`; two of them are adjacent when a
path of `G` joins them through vertices of degree two only. For a finite tree this is the tree
obtained by repeatedly replacing a vertex of degree two and its two edges by a single edge
between its two neighbours. -/
def suppressDegreeTwo (G : SimpleGraph V) : SimpleGraph {v : V // (G.neighborSet v).ncard ≠ 2} where
  Adj u v := u ≠ v ∧ ∃ p : G.Walk u v, p.IsPath ∧
    ∀ w ∈ p.support, w ≠ u.1 → w ≠ v.1 → (G.neighborSet w).ncard = 2
  symm := ⟨fun _ _ ⟨hne, p, hp, hw⟩ ↦ ⟨hne.symm, p.reverse, hp.reverse,
    fun w hw' h1 h2 ↦ hw w (by simpa using hw') h2 h1⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- Two adjacent vertices that are kept stay adjacent after suppressing the vertices of degree
two. -/
theorem suppressDegreeTwo_adj_of_adj (G : SimpleGraph V)
    {u v : {v : V // (G.neighborSet v).ncard ≠ 2}} (h : G.Adj u v) :
    G.suppressDegreeTwo.Adj u v := by
  refine ⟨fun huv ↦ h.ne (congrArg Subtype.val huv), h.toWalk, h.isPath_toWalk,
    fun w hw hu hv ↦ ?_⟩
  simp only [Adj.toWalk, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hw
  rcases hw with rfl | rfl
  · exact absurd rfl hu
  · exact absurd rfl hv

end SimpleGraph
