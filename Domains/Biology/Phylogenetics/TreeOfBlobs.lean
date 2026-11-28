/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Digraph.FiniteDAG
public import MathlibExt.Combinatorics.Graph.Blob
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Chain

/-!
# Blobs and the reduced unrooted tree of blobs of a phylogenetic network

A topological rooted binary phylogenetic network `N⁺` on a taxon set `X`
(`RootedBinaryNetwork`) is a finite connected directed acyclic multigraph with a root of
in-degree `0` and out-degree `2`, leaves of in-degree `1` and out-degree `0` labelled
bijectively by `X`, tree nodes of in-degree `1` and out-degree `2`, and hybrid nodes of
in-degree `2` and out-degree `1` (Allman–Baños–Mitchell–Rhodes 2023, Definition 1). Parallel
edges are allowed: a hybrid node may have both its parents equal, which makes a `2`-cycle. An edge
is a hybrid edge if its child is a hybrid node (`RootedBinaryNetwork.IsHybridEdge`), and a tree
edge otherwise. Every node lies below the root, so the network is connected
(`RootedBinaryNetwork.connected`).

* The **lowest stable ancestor** `RootedBinaryNetwork.lsa` is the node, among those that lie on
  every directed path from the root to a leaf, that lies below all the others; it exists and is
  unique (`RootedBinaryNetwork.existsUnique_isLSA`).
* The **LSA network** `N⊕` deletes the nodes and edges above the LSA and is rooted at the LSA;
  `RootedBinaryNetwork.lsaNetwork` is its underlying multigraph. The **semidirected unrooted
  network** `N⁻` (`RootedBinaryNetwork.semidirected`) undirects its tree edges, keeps the
  directions of its hybrid edges, and suppresses its root: the root and its two edges are replaced
  by one edge between the root's two children, directed when one of the two edges is hybrid.
* Cut edges, blobs, trivial blobs, incident edges, `m`-blobs and the tree of blobs of a multigraph
  are in `MathlibExt.Combinatorics.Graph.Blob`; the `m`-blobs of the rooted networks `N⁺` and
  `N⊕` are `Graph.IsRootedMBlob` with their roots, those of `N⁻` are `Graph.IsMBlob`.
* The **tree of blobs** `T(N⁻)` (`RootedBinaryNetwork.unrootedTreeOfBlobs`) contracts every blob
  of `N⁻` to a vertex, and the **reduced unrooted tree of blobs** `T_rd(N⁻)`
  (`RootedBinaryNetwork.reducedUnrootedTreeOfBlobs`) suppresses its vertices of degree two. When
  `X` has at least two taxa, the blob of each leaf has degree at most one in `T(N⁻)`, so it is a
  vertex of `T_rd(N⁻)` (`RootedBinaryNetwork.taxonVertex`).
* Four distinct taxa form a **B-quartet** (`RootedBinaryNetwork.IsBQuartet`) when the quartet
  they induce on `T_rd(N⁻)` is unresolved: none of the three pairings `ab|cd`, `ac|bd`, `ad|bc`
  is displayed, a pairing `ab|cd` being displayed (`DisplaysQuartet`) when the path joining `a`
  and `b` in `T_rd(N⁻)` and the path joining `c` and `d` have no vertex in common. Otherwise they
  form a **T-quartet** (`RootedBinaryNetwork.IsTQuartet`), and their induced quartet is resolved
  (`RootedBinaryNetwork.IsTQuartet.displaysQuartet`).

Edge lengths and hybridization parameters, which make the network metric under the network
multispecies coalescent, play no role in these topological definitions.

## References

* E. S. Allman, H. Baños, J. D. Mitchell and J. A. Rhodes, *The tree of blobs of a species
  network: identifiability under the coalescent*, J. Math. Biol. 86 (2023), 10, Definitions
  1–13.
* M. Steel, *Phylogeny: Discrete and Random Processes in Evolution*, SIAM, 2016 (lowest stable
  ancestors).
* C. Solís-Lemus and C. Ané, *Inferring phylogenetic networks with maximum pseudolikelihood under
  incomplete lineage sorting*, PLoS Genet. 12 (2016), e1005896.
* H. Baños, *Identifying species network features from gene tree quartets under the coalescent
  model*, Bull. Math. Biol. 81 (2019), 494–534.
-/

@[expose] public section

open Graph

namespace Domains.Biology.Phylogenetics.TreeOfBlobs

/-- A **topological rooted binary phylogenetic network** on the taxon set `X`
(Allman–Baños–Mitchell–Rhodes 2023, Definition 1; Solís-Lemus–Ané 2016; Baños 2019): a finite
directed acyclic multigraph with vertices `V` and edges `E`, the edge `e` running from its parent
`src e` to its child `tgt e`, such that

* the root has in-degree `0` and out-degree `2`;
* the leaves, the nodes of in-degree `1` and out-degree `0`, are labelled bijectively by `X`;
* every other node is a tree node, of in-degree `1` and out-degree `2`, or a hybrid node, of
  in-degree `2` and out-degree `1`.

Several edges may join the same two nodes. The network is connected
(`RootedBinaryNetwork.connected`), as every node lies below the root. -/
structure RootedBinaryNetwork (X V E : Type*) [Finite V] [Finite E] where
  /-- The parent of an edge: the node it leaves. -/
  src : E → V
  /-- The child of an edge: the node it enters. -/
  tgt : E → V
  /-- The root. -/
  root : V
  /-- The leaf labelled by each taxon. -/
  leaf : X → V
  /-- Distinct taxa label distinct leaves. -/
  leaf_injective : Function.Injective leaf
  /-- The labelled nodes are exactly the nodes of in-degree `1` and out-degree `0`. -/
  mem_range_leaf : ∀ v, v ∈ Set.range leaf ↔
    Nat.card {e // tgt e = v} = 1 ∧ Nat.card {e // src e = v} = 0
  /-- The root has in-degree `0`. -/
  indeg_root : Nat.card {e // tgt e = root} = 0
  /-- The root has out-degree `2`. -/
  outdeg_root : Nat.card {e // src e = root} = 2
  /-- Every other node is a leaf, a tree node or a hybrid node. -/
  degree_cases : ∀ v, v ≠ root →
    (Nat.card {e // tgt e = v} = 1 ∧ Nat.card {e // src e = v} = 0) ∨
      (Nat.card {e // tgt e = v} = 1 ∧ Nat.card {e // src e = v} = 2) ∨
      (Nat.card {e // tgt e = v} = 2 ∧ Nat.card {e // src e = v} = 1)
  /-- There is no directed cycle. -/
  acyclic : ∀ v, ¬ Relation.TransGen (fun a b ↦ ∃ e, src e = a ∧ tgt e = b) v v

/-- A **semidirected network**: a multigraph in which some edges carry a direction, `IsArc e x y`
saying that the edge `e` is directed from `x` to `y`. No edge carries both directions, so no loop
is directed. -/
structure SemidirectedNetwork (V E : Type*) where
  /-- The underlying undirected multigraph. -/
  graph : Graph V E
  /-- `IsArc e x y`: the edge `e` is directed from `x` to `y`. -/
  IsArc : E → V → V → Prop
  /-- An edge directed from `x` to `y` has ends `x` and `y`. -/
  isLink_of_isArc : ∀ ⦃e x y⦄, IsArc e x y → graph.IsLink e x y
  /-- An edge directed from `x` to `y` is not also directed from `y` to `x`. -/
  isArc_asymm : ∀ ⦃e x y⦄, IsArc e x y → ¬ IsArc e y x

/-- A graph `T`, in practice a tree, **displays the quartet** `ab|cd` on four of its vertices when
a path joining `a` and `b` and a path joining `c` and `d` have no vertex in common. In a tree the
paths are unique, and `T` displays `ab|cd` exactly when the quartet it induces on `a, b, c, d` is
the resolved quartet with cherries `{a, b}` and `{c, d}`. -/
def DisplaysQuartet {W : Type*} (T : SimpleGraph W) (a b c d : W) : Prop :=
  ∃ (p : T.Walk a b) (q : T.Walk c d), p.IsPath ∧ q.IsPath ∧ p.support.Disjoint q.support

namespace RootedBinaryNetwork

variable {X V E : Type*} [Finite V] [Finite E] (N : RootedBinaryNetwork X V E)

/-! ### The network as a digraph and as a multigraph -/

/-- The digraph of the network: `u → v` when some edge has parent `u` and child `v`. -/
def toDigraph : Digraph V where
  Adj u v := ∃ e, N.src e = u ∧ N.tgt e = v

/-- The underlying undirected multigraph of the network: every node is a vertex, and every edge
has its parent and child as ends. -/
def toGraph : Graph V E where
  vertexSet := Set.univ
  IsLink e x y := N.src e = x ∧ N.tgt e = y ∨ N.src e = y ∧ N.tgt e = x
  isLink_symm _ _ := ⟨fun _ _ h ↦ Or.symm h⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e x y v w (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> tauto
  left_mem_of_isLink _ _ _ _ := trivial

/-- An edge is a **hybrid edge** when its child is a hybrid node, of in-degree `2`; the other edges
are tree edges. -/
def IsHybridEdge (e : E) : Prop :=
  Nat.card {f // N.tgt f = N.tgt e} = 2

theorem isAcyclic : N.toDigraph.IsAcyclic := N.acyclic

theorem wellFounded_adj : WellFounded N.toDigraph.Adj :=
  Digraph.isAcyclic_iff_wellFounded.1 N.isAcyclic

/-- Descending along edges also terminates. -/
theorem wellFounded_flip_adj : WellFounded (flip N.toDigraph.Adj) := by
  have : (Digraph.mk (flip N.toDigraph.Adj)).IsAcyclic := fun v hv ↦
    N.isAcyclic v (Relation.transGen_swap.1 hv)
  exact Digraph.isAcyclic_iff_wellFounded.1 this

theorem outdeg_le_two (v : V) : Nat.card {e // N.src e = v} ≤ 2 := by
  by_cases hv : v = N.root
  · subst hv
    exact N.outdeg_root.le
  · rcases N.degree_cases v hv with h | h | h <;> omega

theorem indeg_le_two (v : V) : Nat.card {e // N.tgt e = v} ≤ 2 := by
  by_cases hv : v = N.root
  · subst hv
    rw [N.indeg_root]
    omega
  · rcases N.degree_cases v hv with h | h | h <;> omega

/-- A leaf has no child. -/
theorem src_ne_leaf (x : X) (e : E) : N.src e ≠ N.leaf x := by
  intro he
  have h0 := ((N.mem_range_leaf (N.leaf x)).1 ⟨x, rfl⟩).2
  rw [Nat.card_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact h0.false ⟨e, he⟩
  · exact (not_finite_iff_infinite.2 h0) inferInstance

/-- A leaf has exactly one parent edge. -/
theorem existsUnique_tgt_eq_leaf (x : X) : ∃! e, N.tgt e = N.leaf x := by
  have h1 := ((N.mem_range_leaf (N.leaf x)).1 ⟨x, rfl⟩).1
  obtain ⟨hsub, ⟨⟨e, he⟩⟩⟩ := Nat.card_eq_one_iff_unique.1 h1
  exact ⟨e, he, fun f hf ↦ congrArg Subtype.val (hsub.elim ⟨f, hf⟩ ⟨e, he⟩)⟩

/-- Every node is reached from the root along edges. -/
theorem reflTransGen_root (v : V) : Relation.ReflTransGen N.toDigraph.Adj N.root v := by
  induction v using N.wellFounded_adj.induction with
  | h v ih =>
    by_cases hv : v = N.root
    · subst hv
      exact .refl
    · have hpos : 0 < Nat.card {e // N.tgt e = v} := by
        rcases N.degree_cases v hv with h | h | h <;> omega
      obtain ⟨⟨e, he⟩⟩ := Nat.card_pos_iff.1 hpos |>.1
      have hadj : N.toDigraph.Adj (N.src e) v := ⟨e, rfl, he⟩
      exact (ih _ hadj).tail hadj

/-- No node lies above the root. -/
theorem not_transGen_root (v : V) : ¬ Relation.TransGen N.toDigraph.Adj v N.root := by
  intro h
  obtain ⟨u, -, ⟨e, -, he⟩⟩ := Relation.TransGen.tail'_iff.1 h
  have h0 := N.indeg_root
  rw [Nat.card_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact h0.false ⟨e, he⟩
  · exact (not_finite_iff_infinite.2 h0) inferInstance

/-- **A rooted binary phylogenetic network is connected**: its underlying undirected multigraph
is connected. -/
theorem connected : N.toGraph.toSimpleGraph.Connected := by
  have hrel : ∀ {a b}, Relation.ReflTransGen N.toDigraph.Adj a b →
      Relation.ReflTransGen N.toGraph.Adj a b := by
    intro a b h
    induction h with
    | refl => exact .refl
    | tail _ hbc ih =>
      obtain ⟨e, rfl, rfl⟩ := hbc
      exact ih.tail ⟨e, Or.inl ⟨rfl, rfl⟩⟩
  have : Nonempty V(N.toGraph) := ⟨⟨N.root, trivial⟩⟩
  refine ⟨fun a b ↦ toSimpleGraph_reachable_iff.2 ?_⟩
  exact (symm (hrel (N.reflTransGen_root a))).trans
    (hrel (N.reflTransGen_root b))

/-! ### The lowest stable ancestor -/

/-- `v` lies on every directed path from the root to a leaf. -/
def IsOnEveryRootLeafPath (v : V) : Prop :=
  ∀ x : X, ∀ p ∈ N.toDigraph.paths, p.head? = some N.root → p.getLast? = some (N.leaf x) → v ∈ p

/-- `v` is the **lowest stable ancestor** of the network (Steel 2016;
Allman–Baños–Mitchell–Rhodes 2023, Definition 4): it lies on every directed path from the root to
a leaf, and lies below every other node that does. -/
def IsLSA (v : V) : Prop :=
  N.IsOnEveryRootLeafPath v ∧
    ∀ u, N.IsOnEveryRootLeafPath u → u ≠ v → Relation.TransGen N.toDigraph.Adj u v

omit [Finite V] in
/-- In a chain, every vertex is reached from the head. -/
private theorem reflTransGen_of_mem_isChain {R : V → V → Prop} {c b : V} {l : List V}
    (hl : (c :: l).IsChain R) (hb : b ∈ c :: l) : Relation.ReflTransGen R c b := by
  rcases List.mem_cons.1 hb with rfl | hb
  · exact .refl
  · exact List.IsChain.cons_induction (Relation.ReflTransGen R c) l hl
      (fun _ _ h hc ↦ hc.tail h) .refl b hb

omit [Finite V] in
/-- Two vertices of a chain are reached one from the other. -/
private theorem reflTransGen_or_of_mem_isChain {R : V → V → Prop} :
    ∀ {l : List V}, l.IsChain R → ∀ {a b : V}, a ∈ l → b ∈ l →
      Relation.ReflTransGen R a b ∨ Relation.ReflTransGen R b a
  | [], _, _, _, ha, _ => absurd ha (List.not_mem_nil)
  | c :: l, hl, a, b, ha, hb => by
    rcases List.mem_cons.1 ha with rfl | ha'
    · exact Or.inl (reflTransGen_of_mem_isChain hl hb)
    rcases List.mem_cons.1 hb with rfl | hb'
    · exact Or.inr (reflTransGen_of_mem_isChain hl ha)
    exact reflTransGen_or_of_mem_isChain hl.tail ha' hb'

/-- Every node has a directed path down to a leaf. -/
theorem exists_isChain_leaf (v : V) :
    ∃ x : X, ∃ l, (v :: l).IsChain N.toDigraph.Adj ∧ (v :: l).getLast (by simp) = N.leaf x := by
  induction v using N.wellFounded_flip_adj.induction with
  | h v ih =>
    by_cases h0 : Nat.card {e // N.src e = v} = 0
    · have hv : v ≠ N.root := fun h ↦ by rw [h, N.outdeg_root] at h0; omega
      have hleaf : v ∈ Set.range N.leaf := by
        rcases N.degree_cases v hv with h | h | h
        · exact (N.mem_range_leaf v).2 h
        all_goals omega
      obtain ⟨x, rfl⟩ := hleaf
      exact ⟨x, [], .singleton _, rfl⟩
    · obtain ⟨⟨e, he⟩⟩ := Nat.card_pos_iff.1 (Nat.pos_of_ne_zero h0) |>.1
      have hadj : N.toDigraph.Adj v (N.tgt e) := ⟨e, he, rfl⟩
      obtain ⟨x, l, hl, hlast⟩ := ih (N.tgt e) hadj
      exact ⟨x, N.tgt e :: l, .cons_cons hadj hl, by rwa [List.getLast_cons_cons]⟩

/-- There is a directed path from the root to a leaf. -/
theorem exists_rootLeafPath : ∃ x : X, ∃ p ∈ N.toDigraph.paths,
    p.head? = some N.root ∧ p.getLast? = some (N.leaf x) := by
  obtain ⟨x, l, hl, hlast⟩ := N.exists_isChain_leaf N.root
  refine ⟨x, N.root :: l, ⟨hl, N.isAcyclic.nodup_of_isChain hl⟩, rfl, ?_⟩
  rw [List.getLast?_eq_some_getLast (by simp), hlast]

/-- **The lowest stable ancestor exists and is unique.** -/
theorem existsUnique_isLSA : ∃! v, N.IsLSA v := by
  set D := {v | N.IsOnEveryRootLeafPath v}
  have hroot : N.root ∈ D := by
    intro x p _ hhead _
    exact List.mem_of_head? hhead
  -- the nodes on every root–leaf path are totally ordered by ancestry
  have htotal : ∀ u ∈ D, ∀ w ∈ D, Relation.ReflTransGen N.toDigraph.Adj u w ∨
      Relation.ReflTransGen N.toDigraph.Adj w u := by
    obtain ⟨x, p, hp, hhead, hlast⟩ := N.exists_rootLeafPath
    intro u hu w hw
    exact reflTransGen_or_of_mem_isChain hp.1 (hu x p hp hhead hlast) (hw x p hp hhead hlast)
  -- a lowest such node
  have hwf : WellFounded (Relation.TransGen (flip N.toDigraph.Adj)) :=
    N.wellFounded_flip_adj.transGen
  obtain ⟨v, hvD, hmin⟩ := hwf.has_min D ⟨N.root, hroot⟩
  have hlsa : N.IsLSA v := by
    refine ⟨hvD, fun u hu huv ↦ ?_⟩
    rcases htotal u hu v hvD with h | h
    · exact (Relation.reflTransGen_iff_eq_or_transGen.1 h).resolve_left (Ne.symm huv)
    · rcases Relation.reflTransGen_iff_eq_or_transGen.1 h with h | h
      · exact absurd h huv
      · exact absurd (Relation.transGen_swap.2 h) (hmin u hu)
  refine ⟨v, hlsa, fun w hw ↦ ?_⟩
  by_contra hwv
  exact N.isAcyclic w ((hlsa.2 w hw.1 hwv).trans (hw.2 v hlsa.1 (Ne.symm hwv)))

/-- The **lowest stable ancestor** `LSA(N⁺)` of the network. -/
noncomputable def lsa : V :=
  N.existsUnique_isLSA.exists.choose

theorem isLSA_lsa : N.IsLSA N.lsa :=
  N.existsUnique_isLSA.exists.choose_spec

/-- A node that lies on every root–leaf path and lies below every other such node is the LSA. -/
theorem IsLSA.eq_lsa {v : V} (hv : N.IsLSA v) : v = N.lsa :=
  N.existsUnique_isLSA.unique hv N.isLSA_lsa

/-- With at least two taxa, no leaf is the lowest stable ancestor. -/
theorem leaf_ne_lsa [Nontrivial X] (x : X) : N.leaf x ≠ N.lsa := by
  intro hx
  obtain ⟨y, hyx⟩ := exists_ne x
  obtain ⟨l, hl, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen
    (N.reflTransGen_root (N.leaf y))
  have hmem : N.leaf x ∈ N.root :: l := by
    rw [hx]
    refine N.isLSA_lsa.1 y _ ⟨hl, N.isAcyclic.nodup_of_isChain hl⟩ rfl ?_
    rw [List.getLast?_eq_some_getLast (by simp), hlast]
  obtain ⟨l₁, l₂, hsplit⟩ := List.mem_iff_append.1 hmem
  cases l₂ with
  | nil =>
    have h₁ : (N.root :: l).getLast? = some (N.leaf y) := by
      rw [List.getLast?_eq_some_getLast (by simp), hlast]
    rw [hsplit, List.getLast?_append, List.getLast?_singleton] at h₁
    exact hyx (N.leaf_injective (Option.some_injective _ (by simpa using h₁))).symm
  | cons z l₃ =>
    rw [hsplit, List.isChain_append_cons_cons] at hl
    obtain ⟨e, he, -⟩ := hl.2.1
    exact N.src_ne_leaf x e he

/-! ### The LSA network and the semidirected network -/

/-- The underlying multigraph of the **LSA network** `N⊕` (Baños 2019; Allman–Baños–Mitchell–Rhodes
2023, Definition 5): the multigraph of the network left after deleting every node above the lowest
stable ancestor, that is, every node from which a directed path of positive length leads to it,
together with the edges at those nodes. `N⊕` itself is rooted at `N.lsa` and keeps the directions
of `N` (`N.src`, `N.tgt`). -/
noncomputable def lsaNetwork : Graph V E :=
  N.toGraph.induce {v | ¬ Relation.TransGen N.toDigraph.Adj v N.lsa}

/-- The edge that replaces the root of `N⊕` when it is suppressed joins `x` and `y`: these are
the children of the lowest stable ancestor along two distinct edges. -/
def IsRootSuppressionLink (x y : V) : Prop :=
  ∃ e₁ e₂, e₁ ≠ e₂ ∧ N.src e₁ = N.lsa ∧ N.src e₂ = N.lsa ∧ N.tgt e₁ = x ∧ N.tgt e₂ = y

/-- Among elements of a type with at most two elements, a third equals one of two distinct
ones. -/
private theorem eq_or_eq_of_natCard_le_two {T : Type*} [Finite T] (h : Nat.card T ≤ 2)
    {a b c : T} (hbc : b ≠ c) : a = b ∨ a = c := by
  classical
  by_contra hne
  push Not at hne
  have := Fintype.ofFinite T
  rw [Nat.card_eq_fintype_card] at h
  have hcard := Finset.card_le_univ ({a, b, c} : Finset T)
  rw [Finset.card_insert_of_notMem (by simp [hne.1, hne.2]), Finset.card_pair hbc] at hcard
  omega

theorem tgt_ne_lsa_of_src_eq {e : E} (he : N.src e = N.lsa) : N.tgt e ≠ N.lsa := by
  intro h
  exact N.isAcyclic _ (.single ⟨e, he, h⟩)

theorem not_transGen_tgt_lsa_of_src_eq {e : E} (he : N.src e = N.lsa) :
    ¬ Relation.TransGen N.toDigraph.Adj (N.tgt e) N.lsa := fun h ↦
  N.isAcyclic _ (Relation.TransGen.head ⟨e, he, rfl⟩ h)

/-- The undirected multigraph of the semidirected network `N⁻`: the LSA network without its root,
whose two edges are replaced by one new edge (`none`) joining the root's two children. -/
noncomputable def semidirectedGraph : Graph V (Option E) where
  vertexSet := V(N.lsaNetwork) \ {N.lsa}
  IsLink o x y := o.elim (N.IsRootSuppressionLink x y)
    fun e ↦ N.lsaNetwork.IsLink e x y ∧ x ≠ N.lsa ∧ y ≠ N.lsa
  isLink_symm o _ := by
    cases o with
    | none => exact ⟨fun x y ⟨e₁, e₂, h, h₁, h₂, hx, hy⟩ ↦ ⟨e₂, e₁, h.symm, h₂, h₁, hy, hx⟩⟩
    | some e => exact ⟨fun x y ⟨h, hx, hy⟩ ↦ ⟨h.symm, hy, hx⟩⟩
  eq_or_eq_of_isLink_of_isLink o x y v w h h' := by
    cases o with
    | none =>
      obtain ⟨e₁, e₂, -, h₁, -, rfl, -⟩ := h
      obtain ⟨e₃, e₄, h34, h₃, h₄, rfl, rfl⟩ := h'
      have hle : Nat.card {e // N.src e = N.lsa} ≤ 2 := N.outdeg_le_two _
      rcases eq_or_eq_of_natCard_le_two hle (a := ⟨e₁, h₁⟩) (b := ⟨e₃, h₃⟩) (c := ⟨e₄, h₄⟩)
        (fun h ↦ h34 (congrArg Subtype.val h)) with h | h
      · exact Or.inl (congrArg (N.tgt ∘ Subtype.val) h)
      · exact Or.inr (congrArg (N.tgt ∘ Subtype.val) h)
    | some e => exact h.1.left_eq_or_eq h'.1
  left_mem_of_isLink o x y h := by
    cases o with
    | none =>
      obtain ⟨e₁, -, -, h₁, -, rfl, -⟩ := h
      exact ⟨N.not_transGen_tgt_lsa_of_src_eq h₁, N.tgt_ne_lsa_of_src_eq h₁⟩
    | some e => exact ⟨h.1.left_mem, h.2.1⟩

/-- The **semidirected unrooted network** `N⁻` (Baños 2019; Allman–Baños–Mitchell–Rhodes 2023,
Definition 5), obtained from the LSA network by undirecting its tree edges, keeping the
directions of its hybrid edges, and suppressing its root. Suppressing the root replaces it and
its two edges by a single edge (`none`) between its two children; when one of the two edges is a
hybrid edge, the new edge takes its direction, from the child along the tree edge to the hybrid
child. With a single taxon the LSA is its leaf, and `N⁻` has no vertex. -/
noncomputable def semidirected : SemidirectedNetwork V (Option E) where
  graph := N.semidirectedGraph
  IsArc o x y := o.elim
    (∃ e₁ e₂, e₁ ≠ e₂ ∧ N.src e₁ = N.lsa ∧ N.src e₂ = N.lsa ∧ N.tgt e₁ = x ∧ N.tgt e₂ = y ∧
      ¬ N.IsHybridEdge e₁ ∧ N.IsHybridEdge e₂)
    fun e ↦ N.semidirectedGraph.IsLink (some e) x y ∧ N.IsHybridEdge e ∧ N.src e = x ∧ N.tgt e = y
  isLink_of_isArc o x y h := by
    cases o with
    | none =>
      obtain ⟨e₁, e₂, h, h₁, h₂, hx, hy, -⟩ := h
      exact ⟨e₁, e₂, h, h₁, h₂, hx, hy⟩
    | some e => exact h.1
  isArc_asymm o x y h h' := by
    cases o with
    | none =>
      -- whether an edge is hybrid depends only on its child
      obtain ⟨e₁, -, -, -, -, hx, -, hnot, -⟩ := h
      obtain ⟨-, e₄, -, -, -, -, hx', -, hhyb⟩ := h'
      apply hnot
      unfold IsHybridEdge at hhyb ⊢
      rwa [hx, ← hx']
    | some e =>
      obtain ⟨-, -, hx, hy⟩ := h
      obtain ⟨-, -, hy', -⟩ := h'
      exact N.isAcyclic _ (.single ⟨e, rfl, hy.trans (hy'.symm)⟩)

theorem mem_semidirected_vertexSet {v : V} :
    v ∈ V(N.semidirected.graph) ↔ ¬ Relation.TransGen N.toDigraph.Adj v N.lsa ∧ v ≠ N.lsa :=
  Iff.rfl

@[simp]
theorem semidirected_isLink_some {e : E} {x y : V} :
    N.semidirected.graph.IsLink (some e) x y ↔ N.toGraph.IsLink e x y ∧
      ¬ Relation.TransGen N.toDigraph.Adj x N.lsa ∧ ¬ Relation.TransGen N.toDigraph.Adj y N.lsa ∧
      x ≠ N.lsa ∧ y ≠ N.lsa := by
  change (N.toGraph.IsLink e x y ∧ _ ∧ _) ∧ _ ∧ _ ↔ _
  tauto

@[simp]
theorem semidirected_isLink_none {x y : V} :
    N.semidirected.graph.IsLink none x y ↔ N.IsRootSuppressionLink x y :=
  Iff.rfl

/-- With at least two taxa, every leaf is a vertex of `N⁻`. -/
theorem leaf_mem_semidirected [Nontrivial X] (x : X) :
    N.leaf x ∈ V(N.semidirected.graph) := by
  refine ⟨fun h ↦ ?_, N.leaf_ne_lsa x⟩
  obtain ⟨_, ⟨e, he, -⟩, -⟩ := Relation.TransGen.head'_iff.1 h
  exact N.src_ne_leaf x e he

/-- With at least two taxa, a leaf has at most one edge in `N⁻`, and it is not a loop. -/
theorem semidirected_isLink_leaf [Nontrivial X] (x : X) :
    (∀ o o' y z, N.semidirected.graph.IsLink o (N.leaf x) y →
      N.semidirected.graph.IsLink o' (N.leaf x) z → o = o') ∧
      ∀ o, ¬ N.semidirected.graph.IsLoopAt o (N.leaf x) := by
  obtain ⟨e₀, he₀, hu⟩ := N.existsUnique_tgt_eq_leaf x
  -- an edge of `N⁺` at a leaf is its parent edge
  have hedge : ∀ e y, N.toGraph.IsLink e (N.leaf x) y → e = e₀ ∧ N.src e₀ = y := by
    rintro e y (⟨h, -⟩ | ⟨rfl, h⟩)
    · exact absurd h (N.src_ne_leaf x e)
    · obtain rfl := hu e h
      exact ⟨rfl, rfl⟩
  -- the edges of `N⁻` at the leaf
  have hcases : ∀ o y, N.semidirected.graph.IsLink o (N.leaf x) y →
      (o = some e₀ ∧ N.src e₀ ≠ N.lsa) ∨ (o = none ∧ N.src e₀ = N.lsa) := by
    rintro (_ | e) y h
    · obtain ⟨e₁, e₂, -, h₁, -, hx, -⟩ := h
      obtain rfl := hu e₁ hx
      exact Or.inr ⟨rfl, h₁⟩
    · obtain ⟨h, -, hy⟩ := h
      obtain ⟨rfl, rfl⟩ := hedge e y h.1
      exact Or.inl ⟨rfl, hy⟩
  refine ⟨fun o o' y z h h' ↦ ?_, fun o h ↦ ?_⟩
  · rcases hcases o y h with ⟨rfl, h₁⟩ | ⟨rfl, h₁⟩ <;>
      rcases hcases o' z h' with ⟨rfl, h₂⟩ | ⟨rfl, h₂⟩
    all_goals first | rfl | exact absurd h₁ (by simp [h₂])
  · cases o with
    | none =>
      obtain ⟨e₁, e₂, h12, -, -, hx, hy⟩ := h
      exact h12 ((hu e₁ hx).trans (hu e₂ hy).symm)
    | some e =>
      obtain ⟨h, -, -⟩ := h
      rcases h.1 with ⟨h, -⟩ | ⟨h, -⟩ <;> exact N.src_ne_leaf x e h

/-! ### The reduced unrooted tree of blobs and blob quartets -/

/-- The **tree of blobs** `T(N⁻)` of the network (Allman–Baños–Mitchell–Rhodes 2023,
Definition 10): the tree obtained from the semidirected network `N⁻` by contracting each of its
blobs to a vertex. -/
noncomputable def unrootedTreeOfBlobs : SimpleGraph {H // N.semidirected.graph.IsBlob H} :=
  N.semidirected.graph.treeOfBlobs

/-- The **reduced unrooted tree of blobs** `T_rd(N⁻)` of the network
(Allman–Baños–Mitchell–Rhodes 2023, Definition 11): the tree of blobs `T(N⁻)` with its vertices of
degree two suppressed. -/
noncomputable def reducedUnrootedTreeOfBlobs :
    SimpleGraph {B // (N.unrootedTreeOfBlobs.neighborSet B).ncard ≠ 2} :=
  N.unrootedTreeOfBlobs.suppressDegreeTwo

/-- With at least two taxa, the blob of a leaf has at most one neighbour in `T(N⁻)`. -/
theorem subsingleton_neighborSet_blobOf_leaf [Nontrivial X] (x : X) :
    (N.unrootedTreeOfBlobs.neighborSet
      (N.semidirected.graph.blobOf (N.leaf_mem_semidirected x))).Subsingleton :=
  subsingleton_neighborSet_treeOfBlobs _ (mem_blobOf _)
    (fun e f y z ↦ (N.semidirected_isLink_leaf x).1 e f y z) (N.semidirected_isLink_leaf x).2

/-- The vertex of `T_rd(N⁻)` labelled by a taxon: the blob of its leaf, which is not suppressed
as it has at most one neighbour. -/
noncomputable def taxonVertex [Nontrivial X] (x : X) :
    {B // (N.unrootedTreeOfBlobs.neighborSet B).ncard ≠ 2} :=
  ⟨N.semidirected.graph.blobOf (N.leaf_mem_semidirected x), by
    have h := N.subsingleton_neighborSet_blobOf_leaf x
    have := (Set.ncard_le_one_iff h.finite).2 fun ha hb ↦ h ha hb
    omega⟩

/-- Four distinct taxa `a, b, c, d` form a **B-quartet** (blob quartet) on the network when the
quartet they induce on the reduced unrooted tree of blobs `T_rd(N⁻)` is unresolved: `T_rd(N⁻)`
displays none of the three quartets `ab|cd`, `ac|bd` and `ad|bc`. Allman–Baños–Mitchell–Rhodes
(2023, Definition 12) define B-quartets by a blob whose incident cut edges, once deleted, leave the
four taxa in four distinct components, and state this condition on `T_rd(N⁻)` as an equivalent
one; the definition here takes the latter. -/
def IsBQuartet [Nontrivial X] (a b c d : X) : Prop :=
  [a, b, c, d].Nodup ∧
    ¬ DisplaysQuartet N.reducedUnrootedTreeOfBlobs
      (N.taxonVertex a) (N.taxonVertex b) (N.taxonVertex c) (N.taxonVertex d) ∧
    ¬ DisplaysQuartet N.reducedUnrootedTreeOfBlobs
      (N.taxonVertex a) (N.taxonVertex c) (N.taxonVertex b) (N.taxonVertex d) ∧
    ¬ DisplaysQuartet N.reducedUnrootedTreeOfBlobs
      (N.taxonVertex a) (N.taxonVertex d) (N.taxonVertex b) (N.taxonVertex c)

/-- Four distinct taxa form a **T-quartet** (tree-like quartet) on the network when they do not
form a B-quartet (Allman–Baños–Mitchell–Rhodes 2023, Definition 13). -/
def IsTQuartet [Nontrivial X] (a b c d : X) : Prop :=
  [a, b, c, d].Nodup ∧ ¬ N.IsBQuartet a b c d

/-- **The quartet induced by a T-quartet is resolved**: the reduced unrooted tree of blobs
displays one of the quartets `ab|cd`, `ac|bd` and `ad|bc`. -/
theorem IsTQuartet.displaysQuartet [Nontrivial X] {a b c d : X} (h : N.IsTQuartet a b c d) :
    DisplaysQuartet N.reducedUnrootedTreeOfBlobs
        (N.taxonVertex a) (N.taxonVertex b) (N.taxonVertex c) (N.taxonVertex d) ∨
      DisplaysQuartet N.reducedUnrootedTreeOfBlobs
        (N.taxonVertex a) (N.taxonVertex c) (N.taxonVertex b) (N.taxonVertex d) ∨
      DisplaysQuartet N.reducedUnrootedTreeOfBlobs
        (N.taxonVertex a) (N.taxonVertex d) (N.taxonVertex b) (N.taxonVertex c) := by
  by_contra hcon
  push Not at hcon
  exact h.2 ⟨h.1, hcon.1, hcon.2.1, hcon.2.2⟩

end RootedBinaryNetwork

end Domains.Biology.Phylogenetics.TreeOfBlobs
