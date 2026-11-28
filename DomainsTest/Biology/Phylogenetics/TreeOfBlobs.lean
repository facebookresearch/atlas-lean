/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.Phylogenetics.TreeOfBlobs
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic.FinCases

/-!
# Tests for blobs and the reduced unrooted tree of blobs of a phylogenetic network

Five networks witness that the structure is satisfiable:

* `quartetTree`, the rooted binary tree `((a, b), (c, d))`. Its LSA is the root, and the root is a
  trivial `3`-blob, as the page says. Every edge of its semidirected network is a cut edge, and
  `{a, b, c, d}` is a T-quartet: the reduced unrooted tree of blobs displays `ab|cd`.
* `twoCycleNetwork`, whose root has two parallel edges to a hybrid node (a `2`-cycle) above a
  cherry `(a, b)`. Its LSA is the parent of the cherry, below the root, so the LSA network drops the
  root and the hybrid node, and in the semidirected network the edge replacing the LSA joins the
  two leaves. The two parallel edges are not cut edges: with the root they form a `2`-blob of the
  rooted network.
* `fourBlobNetwork`, with a `4`-cycle through three tree nodes and a hybrid node, below the root,
  meeting the four taxa through four cut edges. Its LSA is the root, the cycle is a `4`-blob of the
  semidirected network and a vertex of the reduced tree of blobs, `{a, b, c, d}` is a B-quartet, and
  the semidirected network keeps the direction of a hybrid edge but not of a tree edge.
* `hybridChildNetwork`, whose root, the LSA, has a tree child and a hybrid child. The edge that
  replaces the root in the semidirected network is directed from the tree child to the hybrid child.
* `singleTaxonNetwork`, with a single taxon below a `2`-cycle. Its LSA is the leaf, which has no
  child; the semidirected network is that leaf alone, and its reduced tree of blobs is a tree with
  one vertex, labelled by the taxon.
-/

@[expose] public section

open Graph Domains.Biology.Phylogenetics.TreeOfBlobs

namespace DomainsTest.Biology.Phylogenetics.TreeOfBlobs

/-- A multigraph all of whose edges go from a smaller node to a larger one has no directed
cycle. -/
theorem acyclic_of_lt {V E : Type*} [LinearOrder V] (src tgt : E → V) (h : ∀ e, src e < tgt e)
    (v : V) : ¬ Relation.TransGen (fun a b ↦ ∃ e, src e = a ∧ tgt e = b) v v := by
  have key : ∀ {a b}, Relation.TransGen (fun a b ↦ ∃ e, src e = a ∧ tgt e = b) a b → a < b := by
    intro a b hab
    induction hab with
    | single h' =>
      obtain ⟨e, rfl, rfl⟩ := h'
      exact h e
    | tail _ h' ih =>
      obtain ⟨e, rfl, rfl⟩ := h'
      exact ih.trans (h e)
  exact fun hv ↦ lt_irrefl _ (key hv)

section general

variable {X V E : Type*} [Finite V] [Finite E] (N : RootedBinaryNetwork X V E)

/-- The root is the LSA when every other node is avoided by some directed path from the root to a
leaf. -/
theorem lsa_eq_root (h : ∀ u, u ≠ N.root → ∃ x, ∃ p ∈ N.toDigraph.paths,
    p.head? = some N.root ∧ p.getLast? = some (N.leaf x) ∧ u ∉ p) : N.lsa = N.root := by
  refine (RootedBinaryNetwork.IsLSA.eq_lsa N ⟨fun x p _ hhead _ ↦ List.mem_of_head? hhead,
    fun u hu hne ↦ ?_⟩).symm
  obtain ⟨x, p, hp, hhead, hlast, hup⟩ := h u hne
  exact absurd (hu x p hp hhead hlast) hup

/-- A node from which every edge into a leaf leaves lies on every directed path from the root to a
leaf. -/
theorem isOnEveryRootLeafPath_of_forall_tgt_eq_leaf {v : V}
    (h : ∀ e x, N.tgt e = N.leaf x → N.src e = v) : N.IsOnEveryRootLeafPath v := by
  intro x p hp hhead hlast
  obtain ⟨q, rfl⟩ : ∃ q, p = q ++ [N.leaf x] := by
    obtain ⟨q, y, rfl⟩ := List.eq_nil_or_concat p |>.resolve_left (by rintro rfl; simp at hhead)
    rw [List.concat_eq_append, List.getLast?_append, List.getLast?_singleton] at hlast
    simp only [Option.some_or, Option.some.injEq] at hlast
    exact ⟨q, by rw [List.concat_eq_append, hlast]⟩
  obtain ⟨q, y, rfl⟩ := List.eq_nil_or_concat q |>.resolve_left (by
    rintro rfl
    simp only [List.nil_append, List.head?_cons, Option.some.injEq] at hhead
    have h1 := ((N.mem_range_leaf (N.leaf x)).1 ⟨x, rfl⟩).1
    rw [hhead, N.indeg_root] at h1
    omega)
  have hchain := hp.1
  rw [List.concat_eq_append, List.append_assoc, List.singleton_append,
    List.isChain_append_cons_cons] at hchain
  obtain ⟨e, he, hex⟩ := hchain.2.1
  rw [← h e x hex, he]
  simp

/-- When the LSA is the root, an edge that does not leave the root is an edge of `N⁻` with the
same ends. -/
theorem semidirected_isLink_of_lsa_eq_root (hlsa : N.lsa = N.root) {e : E}
    (he : N.src e ≠ N.root) : N.semidirected.graph.IsLink (some e) (N.src e) (N.tgt e) := by
  rw [RootedBinaryNetwork.semidirected_isLink_some, hlsa]
  refine ⟨Or.inl ⟨rfl, rfl⟩, N.not_transGen_root _, N.not_transGen_root _, he, fun h ↦ ?_⟩
  exact N.not_transGen_root (N.src e) (.single ⟨e, rfl, h⟩)

/-- An edge leaving the LSA is not an edge of `N⁻`. -/
theorem some_notMem_semidirected_edgeSet {e : E} (he : N.src e = N.lsa) :
    some e ∉ E(N.semidirected.graph) := by
  intro h
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet h
  rw [RootedBinaryNetwork.semidirected_isLink_some] at hxy
  obtain ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -, -, hx, hy⟩ := hxy
  · exact hx he
  · exact hy he

/-- An edge of the network lies in the edge cut of a set of nodes when exactly one of its ends
does. -/
theorem toGraph_mem_edgeCut_iff {e : E} {S : Set V} :
    e ∈ N.toGraph.edgeCut S ↔ N.src e ∈ S ∧ N.tgt e ∉ S ∨ N.tgt e ∈ S ∧ N.src e ∉ S :=
  (show N.toGraph.IsLink e (N.src e) (N.tgt e) from Or.inl ⟨rfl, rfl⟩).mem_edgeCut_iff

/-- A vertex of a graph has degree other than two when it has three distinct neighbours. -/
theorem ncard_ne_two_of_adj {W : Type*} [Finite W] {T : SimpleGraph W} {v a b c : W}
    (ha : T.Adj v a) (hb : T.Adj v b) (hc : T.Adj v c) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : (T.neighborSet v).ncard ≠ 2 := by
  classical
  have hsub : ({a, b, c} : Set W) ⊆ T.neighborSet v := by
    rintro w (rfl | rfl | rfl) <;> assumption
  have h3 : ({a, b, c} : Set W).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [hab, hac]), Set.ncard_pair hbc]
  have := Set.ncard_le_ncard hsub
  omega

/-- If the only neighbour of a kept vertex `A` is the kept vertex `Z`, every walk from `A` to
another vertex of the graph with its vertices of degree two suppressed passes through `Z`. -/
theorem mem_support_of_forall_adj_eq {W : Type*} {T : SimpleGraph W}
    {A B Z : {v : W // (T.neighborSet v).ncard ≠ 2}} (hA : ∀ K, T.Adj A.1 K → K = Z.1)
    (hAB : A ≠ B) (p : T.suppressDegreeTwo.Walk A B) : Z ∈ p.support := by
  cases p with
  | nil => exact absurd rfl hAB
  | @cons _ W₁ _ h q =>
    obtain ⟨hne, r, -, hdeg⟩ := h
    have hnil : ¬ r.Nil := SimpleGraph.Walk.not_nil_of_ne fun h ↦ hne (Subtype.ext h)
    have hsnd := r.adj_snd hnil
    have hZ := hA _ hsnd
    by_cases hW : W₁.1 = Z.1
    · obtain rfl : W₁ = Z := Subtype.ext hW
      exact List.mem_cons_of_mem _ q.start_mem_support
    · refine absurd (hdeg Z.1 ?_ (fun h ↦ hsnd.ne (hZ.trans h).symm) (Ne.symm hW)) Z.2
      rw [← hZ]
      exact r.getVert_mem_support 1

end general

/-! ### A rooted binary tree on four taxa -/

/-- The rooted binary tree `((a, b), (c, d))`: the root `0` has children `1` and `2`, which are the
parents of the leaves `a = 3`, `b = 4` and `c = 5`, `d = 6`. -/
def quartetTree : RootedBinaryNetwork (Fin 4) (Fin 7) (Fin 6) where
  src := ![0, 0, 1, 1, 2, 2]
  tgt := ![1, 2, 3, 4, 5, 6]
  root := 0
  leaf := ![3, 4, 5, 6]
  leaf_injective := by decide
  mem_range_leaf := by simp only [Nat.card_eq_fintype_card, Set.mem_range]; decide
  indeg_root := by simp only [Nat.card_eq_fintype_card]; decide
  outdeg_root := by simp only [Nat.card_eq_fintype_card]; decide
  degree_cases := by simp only [Nat.card_eq_fintype_card]; decide
  acyclic := acyclic_of_lt _ _ (by decide)

theorem quartetTree_adj (u v : Fin 7) :
    quartetTree.toDigraph.Adj u v ↔ ∃ e, quartetTree.src e = u ∧ quartetTree.tgt e = v :=
  Iff.rfl

instance : DecidableRel quartetTree.toDigraph.Adj := fun u v ↦
  decidable_of_iff _ (quartetTree_adj u v).symm

/-- The LSA of `((a, b), (c, d))` is its root. -/
theorem quartetTree_lsa : quartetTree.lsa = 0 := by
  refine lsa_eq_root _ fun u hu ↦ ?_
  have hpath : ∀ (x : Fin 4) (p : List (Fin 7)), p.IsChain quartetTree.toDigraph.Adj → p.Nodup →
      p.head? = some 0 → p.getLast? = some (quartetTree.leaf x) → u ∉ p →
      ∃ x, ∃ p ∈ quartetTree.toDigraph.paths, p.head? = some quartetTree.root ∧
        p.getLast? = some (quartetTree.leaf x) ∧ u ∉ p :=
    fun x p h₁ h₂ h₃ h₄ h₅ ↦ ⟨x, p, ⟨h₁, h₂⟩, h₃, h₄, h₅⟩
  fin_cases u
  · exact absurd rfl hu
  · exact hpath 2 [0, 2, 5] (by decide) (by decide) rfl rfl (by decide)
  · exact hpath 0 [0, 1, 3] (by decide) (by decide) rfl rfl (by decide)
  · exact hpath 2 [0, 2, 5] (by decide) (by decide) rfl rfl (by decide)
  · exact hpath 2 [0, 2, 5] (by decide) (by decide) rfl rfl (by decide)
  · exact hpath 0 [0, 1, 3] (by decide) (by decide) rfl rfl (by decide)
  · exact hpath 0 [0, 1, 3] (by decide) (by decide) rfl rfl (by decide)

/-! #### The root is a trivial `3`-blob -/

theorem quartetTree_isBridge_root (e : Fin 6) (he : e = 0 ∨ e = 1) :
    quartetTree.toGraph.IsBridge e := by
  rw [isBridge_iff_exists_edgeCut_eq]
  rcases he with rfl | rfl
  · refine ⟨{1, 3, 4}, ?_⟩
    ext f
    rw [toGraph_mem_edgeCut_iff]
    fin_cases f <;> simp [quartetTree]
  · refine ⟨{2, 5, 6}, ?_⟩
    ext f
    rw [toGraph_mem_edgeCut_iff]
    fin_cases f <;> simp [quartetTree]

theorem quartetTree_isTrivialBlob_root :
    quartetTree.toGraph.IsTrivialBlob (quartetTree.toGraph.induce {quartetTree.root}) := by
  refine isTrivialBlob_induce_singleton trivial fun e y he ↦ quartetTree_isBridge_root e ?_
  rcases he with ⟨he, -⟩ | ⟨-, he⟩ <;> fin_cases e <;> simp_all [quartetTree]

/-- **The root of a rooted binary tree is a trivial `3`-blob**: its blob is the root alone, with two
incident cut edges, and the root counts as one more. -/
example : quartetTree.toGraph.IsRootedMBlob quartetTree.root 3
    (quartetTree.toGraph.induce {quartetTree.root}) := by
  refine ⟨quartetTree_isTrivialBlob_root.1, Or.inr ⟨rfl, ?_⟩⟩
  have : quartetTree.toGraph.edgeCut V(quartetTree.toGraph.induce {quartetTree.root}) ∩
      {e | quartetTree.toGraph.IsBridge e} = {0, 1} := by
    ext f
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, toGraph_mem_edgeCut_iff]
    constructor
    · rintro ⟨hf, -⟩
      fin_cases f <;> simp_all [quartetTree]
    · intro hf
      refine ⟨?_, quartetTree_isBridge_root f (by simpa using hf)⟩
      rcases hf with rfl | rfl <;> simp [quartetTree]
  rw [this, Set.encard_pair (by decide)]
  rfl

/-! #### `{a, b, c, d}` is a T-quartet -/

/-- Every edge of the semidirected network of `((a, b), (c, d))` is a cut edge. -/
theorem quartetTree_isBridge (o : Option (Fin 6)) (ho : o ∈ E(quartetTree.semidirected.graph)) :
    quartetTree.semidirected.graph.IsBridge o := by
  have hlsa := quartetTree_lsa
  rw [isBridge_iff_exists_edgeCut_eq]
  -- the links of the semidirected network
  have hlink : ∀ e : Fin 6, quartetTree.src e ≠ 0 →
      quartetTree.semidirected.graph.IsLink (some e) (quartetTree.src e) (quartetTree.tgt e) :=
    fun e he ↦ semidirected_isLink_of_lsa_eq_root _ hlsa he
  have hnone : quartetTree.semidirected.graph.IsLink none 1 2 := by
    rw [RootedBinaryNetwork.semidirected_isLink_none]
    exact ⟨0, 1, by decide, by rw [hlsa]; rfl, by rw [hlsa]; rfl, rfl, rfl⟩
  have hroot : ∀ e : Fin 6, quartetTree.src e = 0 → some e ∉ E(quartetTree.semidirected.graph) :=
    fun e he ↦ some_notMem_semidirected_edgeSet _ (he.trans hlsa.symm)
  -- the edge cut of a set `S` of nodes
  have hcut : ∀ S : Set (Fin 7), ∀ o, o ∈ quartetTree.semidirected.graph.edgeCut S ↔
      match o with
      | none => (1 ∈ S ∧ 2 ∉ S ∨ 2 ∈ S ∧ 1 ∉ S)
      | some e => quartetTree.src e ≠ 0 ∧ (quartetTree.src e ∈ S ∧ quartetTree.tgt e ∉ S ∨
          quartetTree.tgt e ∈ S ∧ quartetTree.src e ∉ S) := by
    intro S o
    cases o with
    | none => exact hnone.mem_edgeCut_iff
    | some e =>
      by_cases he : quartetTree.src e = 0
      · simp only [he, ne_eq, not_true_eq_false, false_and, iff_false]
        exact fun h ↦ hroot e he (edgeCut_subset_edgeSet h)
      · simp only [ne_eq, he, not_false_eq_true, true_and]
        exact (hlink e he).mem_edgeCut_iff
  cases o with
  | none =>
    refine ⟨{1, 3, 4}, Set.ext fun o ↦ ?_⟩
    rw [hcut]
    cases o with
    | none => simp
    | some e => fin_cases e <;> simp [quartetTree]
  | some e =>
    by_cases he : quartetTree.src e = 0
    · exact absurd ho (hroot e he)
    refine ⟨{quartetTree.tgt e}, Set.ext fun o ↦ ?_⟩
    rw [hcut]
    cases o with
    | none => fin_cases e <;> simp_all [quartetTree]
    | some f => fin_cases e <;> fin_cases f <;> simp_all [quartetTree]

theorem quartetTree_mem (v : Fin 7) (hv : v ≠ 0) : v ∈ V(quartetTree.semidirected.graph) := by
  rw [RootedBinaryNetwork.mem_semidirected_vertexSet, quartetTree_lsa]
  exact ⟨quartetTree.not_transGen_root v, fun h ↦ hv h.1⟩

/-- The blob of a node of the semidirected network of `((a, b), (c, d))`: the node alone. -/
noncomputable def quartetTreeBlob (v : Fin 7) (hv : v ≠ 0) : {H // quartetTree.semidirected.graph.IsBlob H} :=
  ⟨_, (isTrivialBlob_induce_singleton (quartetTree_mem v hv)
    fun o _ h ↦ quartetTree_isBridge o h.edge_mem).1⟩

theorem quartetTreeBlob_ne {u v : Fin 7} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    quartetTreeBlob u hu ≠ quartetTreeBlob v hv := by
  intro h
  have : ({u} : Set (Fin 7)) = {v} := congrArg (fun B : {H // _} ↦ V(B.1)) h
  exact huv (Set.singleton_eq_singleton_iff.1 this)

theorem quartetTreeBlob_adj {u v : Fin 7} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) {o : Option (Fin 6)}
    (h : quartetTree.semidirected.graph.IsLink o u v) :
    quartetTree.unrootedTreeOfBlobs.Adj (quartetTreeBlob u hu) (quartetTreeBlob v hv) :=
  ⟨quartetTreeBlob_ne hu hv huv, o, u, v, h, rfl, rfl⟩

theorem quartetTree_blobOf_leaf (x : Fin 4) :
    quartetTree.semidirected.graph.blobOf (quartetTree.leaf_mem_semidirected x) =
      quartetTreeBlob (quartetTree.leaf x) (by fin_cases x <;> decide) :=
  Subtype.ext ((quartetTreeBlob _ _).2.eq_blobOf rfl).symm

/-- The two inner nodes have three distinct neighbours in the tree of blobs, so their degree is not
two and they are not suppressed. -/
theorem quartetTree_ncard_ne_two (v : Fin 7) (hv : v = 1 ∨ v = 2) :
    (quartetTree.unrootedTreeOfBlobs.neighborSet (quartetTreeBlob v (by rcases hv with rfl | rfl <;> decide))).ncard ≠ 2 := by
  have hlink : ∀ e : Fin 6, quartetTree.src e ≠ 0 →
      quartetTree.semidirected.graph.IsLink (some e) (quartetTree.src e) (quartetTree.tgt e) :=
    fun e he ↦ semidirected_isLink_of_lsa_eq_root _ quartetTree_lsa he
  have hnone : quartetTree.semidirected.graph.IsLink none 1 2 := by
    rw [RootedBinaryNetwork.semidirected_isLink_none]
    exact ⟨0, 1, by decide, by rw [quartetTree_lsa]; rfl, by rw [quartetTree_lsa]; rfl, rfl, rfl⟩
  rcases hv with rfl | rfl
  · exact ncard_ne_two_of_adj (quartetTreeBlob_adj _ (by decide : (3 : Fin 7) ≠ 0) (by decide) (hlink 2 (by decide)))
      (quartetTreeBlob_adj _ (by decide : (4 : Fin 7) ≠ 0) (by decide) (hlink 3 (by decide)))
      (quartetTreeBlob_adj _ (by decide : (2 : Fin 7) ≠ 0) (by decide) hnone)
      (quartetTreeBlob_ne _ _ (by decide)) (quartetTreeBlob_ne _ _ (by decide))
      (quartetTreeBlob_ne _ _ (by decide))
  · exact ncard_ne_two_of_adj (quartetTreeBlob_adj _ (by decide : (5 : Fin 7) ≠ 0) (by decide) (hlink 4 (by decide)))
      (quartetTreeBlob_adj _ (by decide : (6 : Fin 7) ≠ 0) (by decide) (hlink 5 (by decide)))
      (quartetTreeBlob_adj _ (by decide : (1 : Fin 7) ≠ 0) (by decide) hnone.symm)
      (quartetTreeBlob_ne _ _ (by decide)) (quartetTreeBlob_ne _ _ (by decide))
      (quartetTreeBlob_ne _ _ (by decide))

/-- **`{a, b, c, d}` is a T-quartet of `((a, b), (c, d))`**: the reduced unrooted tree of blobs
displays `ab|cd`, through the paths `a - 1 - b` and `c - 2 - d`. -/
theorem quartetTree_displaysQuartet :
    DisplaysQuartet quartetTree.reducedUnrootedTreeOfBlobs (quartetTree.taxonVertex 0)
      (quartetTree.taxonVertex 1) (quartetTree.taxonVertex 2) (quartetTree.taxonVertex 3) := by
  set T := quartetTree.reducedUnrootedTreeOfBlobs
  set U : {B // (quartetTree.unrootedTreeOfBlobs.neighborSet B).ncard ≠ 2} :=
    ⟨quartetTreeBlob 1 (by decide), quartetTree_ncard_ne_two 1 (Or.inl rfl)⟩
  set W : {B // (quartetTree.unrootedTreeOfBlobs.neighborSet B).ncard ≠ 2} :=
    ⟨quartetTreeBlob 2 (by decide), quartetTree_ncard_ne_two 2 (Or.inr rfl)⟩
  have hlink : ∀ e : Fin 6, quartetTree.src e ≠ 0 →
      quartetTree.semidirected.graph.IsLink (some e) (quartetTree.src e) (quartetTree.tgt e) :=
    fun e he ↦ semidirected_isLink_of_lsa_eq_root _ quartetTree_lsa he
  -- the vertex sets of the blobs, which tell the vertices of `T` apart
  have hV : ∀ x : Fin 4, V((quartetTree.taxonVertex x).1.1) = {quartetTree.leaf x} := fun x ↦ by
    simp only [RootedBinaryNetwork.taxonVertex, quartetTree_blobOf_leaf]
    rfl
  have hadj : ∀ (x : Fin 4) (P : {B // (quartetTree.unrootedTreeOfBlobs.neighborSet B).ncard ≠ 2})
      (v : Fin 7) (hv : v ≠ 0) (hP : P.1 = quartetTreeBlob v hv) (e : Fin 6),
      quartetTree.src e = v → quartetTree.tgt e = quartetTree.leaf x →
      T.Adj (quartetTree.taxonVertex x) P := by
    intro x P v hv hP e hsrc htgt
    refine SimpleGraph.suppressDegreeTwo_adj_of_adj _ ?_
    rw [hP]
    simp only [RootedBinaryNetwork.taxonVertex, quartetTree_blobOf_leaf]
    have := hlink e (by rw [hsrc]; exact hv)
    rw [hsrc, htgt] at this
    exact quartetTreeBlob_adj _ _ (fun h ↦ quartetTree.src_ne_leaf x e (hsrc.trans h.symm))
      this.symm
  have hA : T.Adj (quartetTree.taxonVertex 0) U := hadj 0 U 1 (by decide) rfl 2 rfl rfl
  have hB : T.Adj U (quartetTree.taxonVertex 1) := (hadj 1 U 1 (by decide) rfl 3 rfl rfl).symm
  have hC : T.Adj (quartetTree.taxonVertex 2) W := hadj 2 W 2 (by decide) rfl 4 rfl rfl
  have hD : T.Adj W (quartetTree.taxonVertex 3) := (hadj 3 W 2 (by decide) rfl 5 rfl rfl).symm
  have hU : V(U.1.1) = {1} := rfl
  have hW : V(W.1.1) = {2} := rfl
  let f : {B // (quartetTree.unrootedTreeOfBlobs.neighborSet B).ncard ≠ 2} → Set (Fin 7) :=
    fun P ↦ V(P.1.1)
  refine ⟨.cons hA (.cons hB .nil), .cons hC (.cons hD .nil), ?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def]
    refine List.Nodup.of_map f ?_
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.map_cons,
      List.map_nil, f, hV, hU]
    simp [quartetTree]
  · rw [SimpleGraph.Walk.isPath_def]
    refine List.Nodup.of_map f ?_
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.map_cons,
      List.map_nil, f, hV, hW]
    simp [quartetTree]
  · intro P hP hQ
    have hP' := List.mem_map_of_mem (f := f) hP
    have hQ' := List.mem_map_of_mem (f := f) hQ
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.map_cons,
      List.map_nil, f, hV, hU, hW, List.mem_cons, List.not_mem_nil, or_false] at hP' hQ'
    rcases hP' with h | h | h <;> rw [h] at hQ' <;> simp [quartetTree] at hQ'

/-- So `{a, b, c, d}` is a T-quartet of `((a, b), (c, d))`. -/
example : quartetTree.IsTQuartet 0 1 2 3 :=
  ⟨by decide, fun h ↦ h.2.1 quartetTree_displaysQuartet⟩

/-! ### A `2`-cycle above the lowest stable ancestor -/

/-- The root `0` has two parallel edges to the hybrid node `1`, whose child `2` is the parent of
the leaves `a = 3` and `b = 4`. -/
def twoCycleNetwork : RootedBinaryNetwork (Fin 2) (Fin 5) (Fin 5) where
  src := ![0, 0, 1, 2, 2]
  tgt := ![1, 1, 2, 3, 4]
  root := 0
  leaf := ![3, 4]
  leaf_injective := by decide
  mem_range_leaf := by simp only [Nat.card_eq_fintype_card, Set.mem_range]; decide
  indeg_root := by simp only [Nat.card_eq_fintype_card]; decide
  outdeg_root := by simp only [Nat.card_eq_fintype_card]; decide
  degree_cases := by simp only [Nat.card_eq_fintype_card]; decide
  acyclic := acyclic_of_lt _ _ (by decide)

instance : DecidableRel twoCycleNetwork.toDigraph.Adj := fun u v ↦
  decidable_of_iff (∃ e, twoCycleNetwork.src e = u ∧ twoCycleNetwork.tgt e = v) Iff.rfl

/-- The node `1` is a hybrid node: both of its parent edges are hybrid edges. -/
example : twoCycleNetwork.IsHybridEdge 0 ∧ twoCycleNetwork.IsHybridEdge 1 := by
  simp only [RootedBinaryNetwork.IsHybridEdge, Nat.card_eq_fintype_card]
  decide

/-- **The LSA is the parent of the cherry**, below the root and the `2`-cycle. -/
theorem twoCycleNetwork_lsa : twoCycleNetwork.lsa = 2 := by
  refine (RootedBinaryNetwork.IsLSA.eq_lsa _ ⟨isOnEveryRootLeafPath_of_forall_tgt_eq_leaf _
    (by decide), fun u hu hne ↦ ?_⟩).symm
  have havoid : ∀ (x : Fin 2) (p : List (Fin 5)), p.IsChain twoCycleNetwork.toDigraph.Adj →
      p.Nodup → p.head? = some 0 → p.getLast? = some (twoCycleNetwork.leaf x) → u ∉ p →
      Relation.TransGen twoCycleNetwork.toDigraph.Adj u 2 :=
    fun x p h₁ h₂ h₃ h₄ h₅ ↦ absurd (hu x p ⟨h₁, h₂⟩ h₃ h₄) h₅
  fin_cases u
  · exact .head ⟨0, rfl, rfl⟩ (.single ⟨2, rfl, rfl⟩)
  · exact .single ⟨2, rfl, rfl⟩
  · exact absurd rfl hne
  · exact havoid 1 [0, 1, 2, 4] (by decide) (by decide) rfl rfl (by decide)
  · exact havoid 0 [0, 1, 2, 3] (by decide) (by decide) rfl rfl (by decide)

/-- The LSA network drops the root and the hybrid node, which lie above the LSA. -/
example : 0 ∉ V(twoCycleNetwork.lsaNetwork) ∧ 1 ∉ V(twoCycleNetwork.lsaNetwork) ∧
    2 ∈ V(twoCycleNetwork.lsaNetwork) := by
  refine ⟨fun h ↦ h ?_, fun h ↦ h ?_, fun h ↦ ?_⟩
  · rw [twoCycleNetwork_lsa]
    exact .head ⟨0, rfl, rfl⟩ (.single ⟨2, rfl, rfl⟩)
  · rw [twoCycleNetwork_lsa]
    exact .single ⟨2, rfl, rfl⟩
  · rw [twoCycleNetwork_lsa] at h
    exact twoCycleNetwork.isAcyclic 2 h

/-- Suppressing the root of the LSA network gives an edge between the two leaves. -/
example : twoCycleNetwork.semidirected.graph.IsLink none 3 4 := by
  rw [RootedBinaryNetwork.semidirected_isLink_none]
  exact ⟨3, 4, by decide, by rw [twoCycleNetwork_lsa]; rfl, by rw [twoCycleNetwork_lsa]; rfl,
    rfl, rfl⟩

/-- Neither of the two parallel edges is a cut edge of the network. -/
theorem twoCycleNetwork_not_isBridge (e : Fin 5) (he : e = 0 ∨ e = 1) :
    ¬ twoCycleNetwork.toGraph.IsBridge e := by
  have hlink : ∀ f : Fin 5, f = 0 ∨ f = 1 → twoCycleNetwork.toGraph.IsLink f 0 1 := by
    rintro f (rfl | rfl) <;> exact Or.inl ⟨rfl, rfl⟩
  rw [isBridge_iff_not_reachable (hlink e he), not_not]
  rcases he with rfl | rfl
  · exact .single ⟨1, hlink 1 (Or.inr rfl), by decide⟩
  · exact .single ⟨0, hlink 0 (Or.inl rfl), by decide⟩

/-- **The `2`-cycle and the root form a `2`-blob of the rooted network**: its blob is `{0, 1}`, with
one incident cut edge, and the root counts as a second. -/
example : twoCycleNetwork.toGraph.IsRootedMBlob 0 2 (twoCycleNetwork.toGraph.blobOf
    (x := (0 : Fin 5)) trivial).1 := by
  set B := twoCycleNetwork.toGraph.blobOf (x := (0 : Fin 5)) trivial
  have hcut : twoCycleNetwork.toGraph.edgeCut {0, 1} = {2} := by
    ext f
    rw [toGraph_mem_edgeCut_iff]
    fin_cases f <;> simp [twoCycleNetwork]
  have hbr : twoCycleNetwork.toGraph.IsBridge 2 := isBridge_iff_exists_edgeCut_eq.2 ⟨_, hcut⟩
  have hV : V(B.1) = {0, 1} := by
    refine Set.Subset.antisymm (B.2.vertexSet_subset (mem_blobOf _) (by simp) ?_) ?_
    · rw [hcut]
      rintro e rfl
      exact hbr
    · rintro v (rfl | rfl)
      · exact mem_blobOf _
      · exact B.2.mem_of_isLink (mem_blobOf _) (Or.inl ⟨rfl, rfl⟩ : twoCycleNetwork.toGraph.IsLink 0 _ _)
          (twoCycleNetwork_not_isBridge 0 (Or.inl rfl))
  refine ⟨B.2, Or.inr ⟨by rw [hV]; simp, ?_⟩⟩
  rw [hV, hcut, Set.inter_eq_left.2 (by rintro e rfl; exact hbr), Set.encard_singleton]
  rfl

/-! ### A `4`-blob -/

/-- The root `0` has children `1` and the leaf `d = 8`; the tree nodes `1`, `2`, `3` and the hybrid
node `4` form the `4`-cycle `1 → 2 → 4 ← 3 ← 1`, and `2`, `3`, `4` are the parents of the leaves
`a = 5`, `b = 6` and `c = 7`. -/
def fourBlobNetwork : RootedBinaryNetwork (Fin 4) (Fin 9) (Fin 9) where
  src := ![0, 0, 1, 1, 2, 2, 3, 3, 4]
  tgt := ![1, 8, 2, 3, 5, 4, 4, 6, 7]
  root := 0
  leaf := ![5, 6, 7, 8]
  leaf_injective := by decide
  mem_range_leaf := by simp only [Nat.card_eq_fintype_card, Set.mem_range]; decide
  indeg_root := by simp only [Nat.card_eq_fintype_card]; decide
  outdeg_root := by simp only [Nat.card_eq_fintype_card]; decide
  degree_cases := by simp only [Nat.card_eq_fintype_card]; decide
  acyclic := acyclic_of_lt _ _ (by decide)

instance : DecidableRel fourBlobNetwork.toDigraph.Adj := fun u v ↦
  decidable_of_iff (∃ e, fourBlobNetwork.src e = u ∧ fourBlobNetwork.tgt e = v) Iff.rfl

theorem fourBlobNetwork_lsa : fourBlobNetwork.lsa = 0 := by
  refine lsa_eq_root _ fun u hu ↦ ?_
  have hpath : ∀ (x : Fin 4) (p : List (Fin 9)), p.IsChain fourBlobNetwork.toDigraph.Adj →
      p.Nodup → p.head? = some 0 → p.getLast? = some (fourBlobNetwork.leaf x) → u ∉ p →
      ∃ x, ∃ p ∈ fourBlobNetwork.toDigraph.paths, p.head? = some fourBlobNetwork.root ∧
        p.getLast? = some (fourBlobNetwork.leaf x) ∧ u ∉ p :=
    fun x p h₁ h₂ h₃ h₄ h₅ ↦ ⟨x, p, ⟨h₁, h₂⟩, h₃, h₄, h₅⟩
  fin_cases u
  · exact absurd rfl hu
  · exact hpath 3 [0, 8] (by decide) (by decide) rfl rfl (by decide)
  · exact hpath 1 [0, 1, 3, 6] (by decide) (by decide) rfl rfl (by decide)
  · exact hpath 0 [0, 1, 2, 5] (by decide) (by decide) rfl rfl (by decide)
  · exact hpath 3 [0, 8] (by decide) (by decide) rfl rfl (by decide)
  · exact hpath 3 [0, 8] (by decide) (by decide) rfl rfl (by decide)
  · exact hpath 3 [0, 8] (by decide) (by decide) rfl rfl (by decide)
  · exact hpath 3 [0, 8] (by decide) (by decide) rfl rfl (by decide)
  · exact hpath 0 [0, 1, 2, 5] (by decide) (by decide) rfl rfl (by decide)

theorem fourBlobNetwork_isLink (e : Fin 9) (he : fourBlobNetwork.src e ≠ 0) :
    fourBlobNetwork.semidirected.graph.IsLink (some e) (fourBlobNetwork.src e)
      (fourBlobNetwork.tgt e) :=
  semidirected_isLink_of_lsa_eq_root _ fourBlobNetwork_lsa he

/-- The edge replacing the root joins its children `1` and `d = 8`. -/
theorem fourBlobNetwork_isLink_none : fourBlobNetwork.semidirected.graph.IsLink none 1 8 := by
  rw [RootedBinaryNetwork.semidirected_isLink_none]
  exact ⟨0, 1, by decide, by rw [fourBlobNetwork_lsa]; rfl, by rw [fourBlobNetwork_lsa]; rfl,
    rfl, rfl⟩

/-- An edge of the semidirected network that is not deleted. -/
theorem fourBlobNetwork_adj (e f : Fin 9) (he : fourBlobNetwork.src e ≠ 0) (hef : e ≠ f) :
    (fourBlobNetwork.semidirected.graph.deleteEdges {some f}).Adj (fourBlobNetwork.src e)
      (fourBlobNetwork.tgt e) :=
  ⟨some e, fourBlobNetwork_isLink e he, by simpa using hef⟩

/-- The edges `1 - 2`, `1 - 3` and `2 - 4` of the cycle are not cut edges. -/
theorem fourBlobNetwork_not_isBridge (e : Fin 9) (he : e = 2 ∨ e = 3 ∨ e = 5) :
    ¬ fourBlobNetwork.semidirected.graph.IsBridge (some e) := by
  rw [isBridge_iff_not_reachable (fourBlobNetwork_isLink e (by rcases he with rfl | rfl | rfl <;>
    decide)), not_not]
  rcases he with rfl | rfl | rfl
  · -- `1 - 3 - 4 - 2`
    exact (Relation.ReflTransGen.single (fourBlobNetwork_adj 3 2 (by decide) (by decide))).tail
      (fourBlobNetwork_adj 6 2 (by decide) (by decide)) |>.tail
      (fourBlobNetwork_adj 5 2 (by decide) (by decide)).symm
  · -- `1 - 2 - 4 - 3`
    exact (Relation.ReflTransGen.single (fourBlobNetwork_adj 2 3 (by decide) (by decide))).tail
      (fourBlobNetwork_adj 5 3 (by decide) (by decide)) |>.tail
      (fourBlobNetwork_adj 6 3 (by decide) (by decide)).symm
  · -- `2 - 1 - 3 - 4`
    exact (Relation.ReflTransGen.single (fourBlobNetwork_adj 2 5 (by decide) (by decide)).symm).tail
      (fourBlobNetwork_adj 3 5 (by decide) (by decide)) |>.tail
      (fourBlobNetwork_adj 6 5 (by decide) (by decide))

theorem fourBlobNetwork_mem_one : (1 : Fin 9) ∈ V(fourBlobNetwork.semidirected.graph) := by
  rw [RootedBinaryNetwork.mem_semidirected_vertexSet, fourBlobNetwork_lsa]
  exact ⟨fourBlobNetwork.not_transGen_root 1, fun h ↦ absurd h.1 (by decide)⟩

/-- The blob of the cycle, the blob of the node `1`. -/
noncomputable def fourBlobNetworkCycle : {H // fourBlobNetwork.semidirected.graph.IsBlob H} :=
  fourBlobNetwork.semidirected.graph.blobOf fourBlobNetwork_mem_one

/-- The cycle `1 - 2 - 4 - 3` lies in one blob. -/
theorem fourBlobNetwork_mem_cycle (v : Fin 9) (hv : v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4) :
    v ∈ V(fourBlobNetworkCycle.1) := by
  have h1 : (1 : Fin 9) ∈ V(fourBlobNetworkCycle.1) := mem_blobOf _
  have h2 : (2 : Fin 9) ∈ V(fourBlobNetworkCycle.1) := fourBlobNetworkCycle.2.mem_of_isLink h1
    (fourBlobNetwork_isLink 2 (by decide)) (fourBlobNetwork_not_isBridge 2 (by decide))
  rcases hv with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact fourBlobNetworkCycle.2.mem_of_isLink h1 (fourBlobNetwork_isLink 3 (by decide))
      (fourBlobNetwork_not_isBridge 3 (by decide))
  · exact fourBlobNetworkCycle.2.mem_of_isLink h2 (fourBlobNetwork_isLink 5 (by decide))
      (fourBlobNetwork_not_isBridge 5 (by decide))

/-- The blob of a leaf is the leaf alone. -/
theorem fourBlobNetwork_vertexSet_leaf (x : Fin 4) :
    V((fourBlobNetwork.taxonVertex x).1.1) = {fourBlobNetwork.leaf x} :=
  (fourBlobNetwork.taxonVertex x).1.2.vertexSet_eq_singleton
    (mem_blobOf (fourBlobNetwork.leaf_mem_semidirected x))
    (fourBlobNetwork.semidirected_isLink_leaf x).1 (fourBlobNetwork.semidirected_isLink_leaf x).2

/-- The blob of each leaf is adjacent to the blob of the cycle in the tree of blobs. -/
theorem fourBlobNetwork_adj_cycle (x : Fin 4) :
    fourBlobNetwork.unrootedTreeOfBlobs.Adj (fourBlobNetwork.taxonVertex x).1
      fourBlobNetworkCycle := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have h1 := fourBlobNetwork_mem_cycle 1 (Or.inl rfl)
    rw [← h, fourBlobNetwork_vertexSet_leaf] at h1
    fin_cases x <;> simp [fourBlobNetwork] at h1
  · have hx := fourBlobNetwork_vertexSet_leaf x
    fin_cases x
    · exact ⟨some 4, 5, 2, (fourBlobNetwork_isLink 4 (by decide)).symm, by rw [hx]; rfl,
        fourBlobNetwork_mem_cycle 2 (by decide)⟩
    · exact ⟨some 7, 6, 3, (fourBlobNetwork_isLink 7 (by decide)).symm, by rw [hx]; rfl,
        fourBlobNetwork_mem_cycle 3 (by decide)⟩
    · exact ⟨some 8, 7, 4, (fourBlobNetwork_isLink 8 (by decide)).symm, by rw [hx]; rfl,
        fourBlobNetwork_mem_cycle 4 (by decide)⟩
    · exact ⟨none, 8, 1, fourBlobNetwork_isLink_none.symm, by rw [hx]; rfl,
        fourBlobNetwork_mem_cycle 1 (by decide)⟩

theorem fourBlobNetwork_taxonVertex_ne {x y : Fin 4} (hxy : x ≠ y) :
    fourBlobNetwork.taxonVertex x ≠ fourBlobNetwork.taxonVertex y := by
  intro h
  have := fourBlobNetwork_vertexSet_leaf x
  rw [h, fourBlobNetwork_vertexSet_leaf] at this
  exact hxy (fourBlobNetwork.leaf_injective (Set.singleton_eq_singleton_iff.1 this).symm)

/-- The blob of the cycle has degree at least three in the tree of blobs, so it is a vertex of the
reduced tree of blobs. -/
noncomputable def fourBlobNetworkCycleVertex :
    {B // (fourBlobNetwork.unrootedTreeOfBlobs.neighborSet B).ncard ≠ 2} :=
  ⟨fourBlobNetworkCycle, ncard_ne_two_of_adj (fourBlobNetwork_adj_cycle 0).symm
    (fourBlobNetwork_adj_cycle 1).symm (fourBlobNetwork_adj_cycle 2).symm
    (fun h ↦ fourBlobNetwork_taxonVertex_ne (by decide : (0 : Fin 4) ≠ 1) (Subtype.ext h))
    (fun h ↦ fourBlobNetwork_taxonVertex_ne (by decide : (0 : Fin 4) ≠ 2) (Subtype.ext h))
    (fun h ↦ fourBlobNetwork_taxonVertex_ne (by decide : (1 : Fin 4) ≠ 2) (Subtype.ext h))⟩

/-- The only neighbour of the blob of a leaf in the tree of blobs is the blob of the cycle. -/
theorem fourBlobNetwork_eq_cycle (x : Fin 4) (K : {H // fourBlobNetwork.semidirected.graph.IsBlob H})
    (hK : fourBlobNetwork.unrootedTreeOfBlobs.Adj (fourBlobNetwork.taxonVertex x).1 K) :
    K = fourBlobNetworkCycleVertex.1 :=
  fourBlobNetwork.subsingleton_neighborSet_blobOf_leaf x hK (fourBlobNetwork_adj_cycle x)

/-- **`{a, b, c, d}` is a B-quartet of the network with a `4`-blob**: every path between two leaves
of the reduced unrooted tree of blobs passes through the blob of the cycle, so no two such paths
are disjoint. -/
example : fourBlobNetwork.IsBQuartet 0 1 2 3 := by
  have hmem : ∀ x y : Fin 4, x ≠ y →
      ∀ p : fourBlobNetwork.reducedUnrootedTreeOfBlobs.Walk (fourBlobNetwork.taxonVertex x)
        (fourBlobNetwork.taxonVertex y), fourBlobNetworkCycleVertex ∈ p.support :=
    fun x y hxy p ↦ mem_support_of_forall_adj_eq (fourBlobNetwork_eq_cycle x)
      (fourBlobNetwork_taxonVertex_ne hxy) p
  refine ⟨by decide, ?_, ?_, ?_⟩ <;> rintro ⟨p, q, -, -, hpq⟩
  · exact hpq (hmem 0 1 (by decide) p) (hmem 2 3 (by decide) q)
  · exact hpq (hmem 0 2 (by decide) p) (hmem 1 3 (by decide) q)
  · exact hpq (hmem 0 3 (by decide) p) (hmem 1 2 (by decide) q)

/-- The edge cut of a set of nodes in the semidirected network of the network with a `4`-blob. -/
theorem fourBlobNetwork_mem_edgeCut_iff (S : Set (Fin 9)) (o : Option (Fin 9)) :
    o ∈ fourBlobNetwork.semidirected.graph.edgeCut S ↔
      match o with
      | none => (1 ∈ S ∧ 8 ∉ S ∨ 8 ∈ S ∧ 1 ∉ S)
      | some e => fourBlobNetwork.src e ≠ 0 ∧ (fourBlobNetwork.src e ∈ S ∧
          fourBlobNetwork.tgt e ∉ S ∨ fourBlobNetwork.tgt e ∈ S ∧ fourBlobNetwork.src e ∉ S) := by
  cases o with
  | none => exact fourBlobNetwork_isLink_none.mem_edgeCut_iff
  | some e =>
    by_cases he : fourBlobNetwork.src e = 0
    · simp only [he, ne_eq, not_true_eq_false, false_and, iff_false]
      exact fun h ↦ some_notMem_semidirected_edgeSet _ (he.trans fourBlobNetwork_lsa.symm)
        (edgeCut_subset_edgeSet h)
    · simp only [ne_eq, he, not_false_eq_true, true_and]
      exact (fourBlobNetwork_isLink e he).mem_edgeCut_iff

/-- The edge of a leaf is a cut edge. -/
theorem fourBlobNetwork_isBridge_leaf (x : Fin 4) {o : Option (Fin 9)} {v : Fin 9}
    (h : fourBlobNetwork.semidirected.graph.IsLink o (fourBlobNetwork.leaf x) v) :
    fourBlobNetwork.semidirected.graph.IsBridge o :=
  isBridge_of_forall_isLink_eq h (fun hv ↦ (fourBlobNetwork.semidirected_isLink_leaf x).2 o
    (hv ▸ h)) fun _ _ hf ↦ (fourBlobNetwork.semidirected_isLink_leaf x).1 _ _ _ _ hf h

/-- **The cycle is a `4`-blob of the semidirected network**: its blob is `{1, 2, 3, 4}`, and its
incident edges are the four cut edges to the leaves. -/
example : fourBlobNetwork.semidirected.graph.IsMBlob 4 fourBlobNetworkCycle.1 := by
  have hcut : fourBlobNetwork.semidirected.graph.edgeCut {1, 2, 3, 4} =
      {some 4, some 7, some 8, none} := by
    ext o
    rw [fourBlobNetwork_mem_edgeCut_iff]
    cases o with
    | none => simp
    | some e => fin_cases e <;> simp [fourBlobNetwork]
  have hbr : ∀ o ∈ fourBlobNetwork.semidirected.graph.edgeCut {1, 2, 3, 4},
      fourBlobNetwork.semidirected.graph.IsBridge o := by
    rw [hcut]
    rintro o (rfl | rfl | rfl | rfl)
    · exact fourBlobNetwork_isBridge_leaf 0 (fourBlobNetwork_isLink 4 (by decide)).symm
    · exact fourBlobNetwork_isBridge_leaf 1 (fourBlobNetwork_isLink 7 (by decide)).symm
    · exact fourBlobNetwork_isBridge_leaf 2 (fourBlobNetwork_isLink 8 (by decide)).symm
    · exact fourBlobNetwork_isBridge_leaf 3 fourBlobNetwork_isLink_none.symm
  have hV : V(fourBlobNetworkCycle.1) = {1, 2, 3, 4} := by
    refine Set.Subset.antisymm (fourBlobNetworkCycle.2.vertexSet_subset (mem_blobOf _) (by simp)
      hbr) ?_
    rintro v (rfl | rfl | rfl | rfl) <;> exact fourBlobNetwork_mem_cycle _ (by decide)
  refine ⟨fourBlobNetworkCycle.2, ?_⟩
  rw [hV, Set.inter_eq_left.2 fun o ho ↦ hbr o ho, hcut, Set.encard_insert_of_notMem (by simp),
    Set.encard_insert_of_notMem (by simp), Set.encard_pair (by simp)]
  rfl

/-- In the semidirected network the hybrid edge `2 → 4` keeps its direction, while the tree edge
`1 - 2` and the edge replacing the root, which joins two tree edges, are undirected. -/
example : fourBlobNetwork.semidirected.IsArc (some 5) 2 4 ∧
    (∀ x y, ¬ fourBlobNetwork.semidirected.IsArc (some 2) x y) ∧
    ∀ x y, ¬ fourBlobNetwork.semidirected.IsArc none x y := by
  have hhyb : ∀ e : Fin 9, fourBlobNetwork.IsHybridEdge e ↔ e = 5 ∨ e = 6 := by
    simp only [RootedBinaryNetwork.IsHybridEdge, Nat.card_eq_fintype_card]
    decide
  refine ⟨⟨fourBlobNetwork_isLink 5 (by decide), (hhyb 5).2 (Or.inl rfl), rfl, rfl⟩,
    fun x y h ↦ ?_, fun x y h ↦ ?_⟩
  · exact absurd ((hhyb 2).1 h.2.1) (by decide)
  · obtain ⟨e₁, e₂, -, -, h₂, -, -, -, hhyb₂⟩ := h
    rw [fourBlobNetwork_lsa] at h₂
    rcases (hhyb e₂).1 hhyb₂ with rfl | rfl <;> exact absurd h₂ (by decide)

/-! ### A hybrid child of the lowest stable ancestor -/

/-- The root `0` has the tree node `t = 1` and the hybrid node `h = 2` as children, and `t` is the
other parent of `h`; `t` and `h` are the parents of the leaves `a = 3` and `b = 4`. -/
def hybridChildNetwork : RootedBinaryNetwork (Fin 2) (Fin 5) (Fin 5) where
  src := ![0, 0, 1, 1, 2]
  tgt := ![1, 2, 2, 3, 4]
  root := 0
  leaf := ![3, 4]
  leaf_injective := by decide
  mem_range_leaf := by simp only [Nat.card_eq_fintype_card, Set.mem_range]; decide
  indeg_root := by simp only [Nat.card_eq_fintype_card]; decide
  outdeg_root := by simp only [Nat.card_eq_fintype_card]; decide
  degree_cases := by simp only [Nat.card_eq_fintype_card]; decide
  acyclic := acyclic_of_lt _ _ (by decide)

instance : DecidableRel hybridChildNetwork.toDigraph.Adj := fun u v ↦
  decidable_of_iff (∃ e, hybridChildNetwork.src e = u ∧ hybridChildNetwork.tgt e = v) Iff.rfl

/-- The LSA is the root: the path to `a` avoids `h`, and the path to `b` avoids `t`. -/
theorem hybridChildNetwork_lsa : hybridChildNetwork.lsa = 0 := by
  refine lsa_eq_root _ fun u hu ↦ ?_
  have hpath : ∀ (x : Fin 2) (p : List (Fin 5)), p.IsChain hybridChildNetwork.toDigraph.Adj →
      p.Nodup → p.head? = some 0 → p.getLast? = some (hybridChildNetwork.leaf x) → u ∉ p →
      ∃ x, ∃ p ∈ hybridChildNetwork.toDigraph.paths, p.head? = some hybridChildNetwork.root ∧
        p.getLast? = some (hybridChildNetwork.leaf x) ∧ u ∉ p :=
    fun x p h₁ h₂ h₃ h₄ h₅ ↦ ⟨x, p, ⟨h₁, h₂⟩, h₃, h₄, h₅⟩
  fin_cases u
  · exact absurd rfl hu
  · exact hpath 1 [0, 2, 4] (by decide) (by decide) rfl rfl (by decide)
  · exact hpath 0 [0, 1, 3] (by decide) (by decide) rfl rfl (by decide)
  · exact hpath 1 [0, 2, 4] (by decide) (by decide) rfl rfl (by decide)
  · exact hpath 0 [0, 1, 3] (by decide) (by decide) rfl rfl (by decide)

/-- **The edge replacing the root takes the direction of its hybrid edge**: it is directed from the
tree child `t` to the hybrid child `h`, and not from `h` to `t`. -/
example : hybridChildNetwork.semidirected.IsArc none 1 2 ∧
    ¬ hybridChildNetwork.semidirected.IsArc none 2 1 := by
  have hhyb : ∀ e : Fin 5, hybridChildNetwork.IsHybridEdge e ↔ e = 1 ∨ e = 2 := by
    simp only [RootedBinaryNetwork.IsHybridEdge, Nat.card_eq_fintype_card]
    decide
  have harc : hybridChildNetwork.semidirected.IsArc none 1 2 :=
    ⟨0, 1, by decide, by rw [hybridChildNetwork_lsa]; rfl, by rw [hybridChildNetwork_lsa]; rfl,
      rfl, rfl, fun h ↦ absurd ((hhyb 0).1 h) (by decide), (hhyb 1).2 (Or.inl rfl)⟩
  exact ⟨harc, hybridChildNetwork.semidirected.isArc_asymm harc⟩

/-! ### A single taxon -/

/-- The root `0` has two parallel edges to the hybrid node `1`, the parent of the only leaf
`a = 2`. -/
def singleTaxonNetwork : RootedBinaryNetwork (Fin 1) (Fin 3) (Fin 3) where
  src := ![0, 0, 1]
  tgt := ![1, 1, 2]
  root := 0
  leaf := ![2]
  leaf_injective := by decide
  mem_range_leaf := by simp only [Nat.card_eq_fintype_card, Set.mem_range]; decide
  indeg_root := by simp only [Nat.card_eq_fintype_card]; decide
  outdeg_root := by simp only [Nat.card_eq_fintype_card]; decide
  degree_cases := by simp only [Nat.card_eq_fintype_card]; decide
  acyclic := acyclic_of_lt _ _ (by decide)

/-- **With a single taxon, the LSA is its leaf.** -/
theorem singleTaxonNetwork_lsa : singleTaxonNetwork.lsa = 2 :=
  singleTaxonNetwork.lsa_eq_leaf 0

/-- The LSA has no child, as there is a single taxon. -/
example : ¬ ∃ e, singleTaxonNetwork.src e = singleTaxonNetwork.lsa := by
  rw [singleTaxonNetwork.exists_src_eq_lsa_iff, not_nontrivial_iff_subsingleton]
  infer_instance

/-- **The semidirected network keeps the leaf**, its only vertex: the LSA has no child, so there
is nothing to suppress. -/
theorem singleTaxonNetwork_vertexSet : V(singleTaxonNetwork.semidirected.graph) = {2} := by
  ext v
  rw [RootedBinaryNetwork.mem_semidirected_vertexSet, singleTaxonNetwork_lsa,
    Set.mem_singleton_iff]
  fin_cases v
  · exact iff_of_false (fun h ↦ h.1 (.head ⟨0, rfl, rfl⟩ (.single ⟨2, rfl, rfl⟩))) (by decide)
  · exact iff_of_false (fun h ↦ h.1 (.single ⟨2, rfl, rfl⟩)) (by decide)
  · exact iff_of_true ⟨singleTaxonNetwork.isAcyclic 2,
      fun ⟨_, e, he⟩ ↦ singleTaxonNetwork.src_ne_leaf 0 e he⟩ rfl

/-- The semidirected network has a single blob. -/
theorem singleTaxonNetwork_subsingleton_blob :
    Subsingleton {H // singleTaxonNetwork.semidirected.graph.IsBlob H} := by
  refine ⟨fun B₁ B₂ ↦ ?_⟩
  obtain ⟨⟨x, hx⟩⟩ := B₁.2.connected.nonempty
  obtain ⟨⟨y, hy⟩⟩ := B₂.2.connected.nonempty
  have hx' := B₁.2.le.vertexSet_mono hx
  have hy' := B₂.2.le.vertexSet_mono hy
  rw [singleTaxonNetwork_vertexSet, Set.mem_singleton_iff] at hx' hy'
  subst hx' hy'
  exact Subtype.ext (B₁.2.eq_of_mem B₂.2 hx hy)

/-- **The reduced unrooted tree of blobs of a single-taxon network is a tree with one vertex**,
the vertex labelled by the taxon. -/
example : singleTaxonNetwork.reducedUnrootedTreeOfBlobs.IsTree ∧
    ∀ B, B = singleTaxonNetwork.taxonVertex 0 := by
  have hsub : ∀ B C : {B // (singleTaxonNetwork.unrootedTreeOfBlobs.neighborSet B).ncard ≠ 2},
      B = C := fun B C ↦ Subtype.ext (singleTaxonNetwork_subsingleton_blob.elim _ _)
  have : Nonempty {B // (singleTaxonNetwork.unrootedTreeOfBlobs.neighborSet B).ncard ≠ 2} :=
    ⟨singleTaxonNetwork.taxonVertex 0⟩
  refine ⟨⟨⟨fun B C ↦ by rw [hsub B C]⟩, fun v c hc ↦ ?_⟩, fun B ↦ hsub _ _⟩
  cases c with
  | nil => exact SimpleGraph.Walk.not_isCycle_nil hc
  | cons h _ => exact h.ne (hsub _ _)

end DomainsTest.Biology.Phylogenetics.TreeOfBlobs
