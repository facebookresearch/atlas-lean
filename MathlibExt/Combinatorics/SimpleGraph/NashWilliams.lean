/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Order.CompletePartialOrder

@[expose] public section

section
namespace MathlibExt.Combinatorics.SimpleGraph.NashWilliamsWanted

/-!
# Nash–Williams arboricity
-/

/-- **Arboricity colorings.** Let $G$ be a simple graph and $k$ a natural number. A labeling of the
edges of $G$ with labels in $\{0, 1, \dots, k - 1\}$ is an arboricity coloring when, for each
label $i$, the graph on the vertices of $G$ whose edges are the edges of $G$ labeled $i$ is
acyclic, that is, a forest. -/
def IsArboricityColoring {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (C : G.EdgeLabeling (Fin k)) : Prop :=
  ∀ i : Fin k, (C.labelGraph i).IsAcyclic

/-- N1. Reachability in `L ⊔ edge a b`: either it already holds in `L`,
or it goes through the new edge in one direction or the other. -/
private theorem nw_reachable_sup_edge_cases {V : Type*} (L : SimpleGraph V)
    (a b p q : V) (h : (L ⊔ SimpleGraph.edge a b).Reachable p q) :
    L.Reachable p q ∨ (L.Reachable p a ∧ L.Reachable b q) ∨
      (L.Reachable p b ∧ L.Reachable a q) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  refine Relation.ReflTransGen.head_induction_on h
    (Or.inl (SimpleGraph.Reachable.refl _)) ?_
  intro x c hxc _ ih
  rw [SimpleGraph.sup_adj] at hxc
  rcases hxc with hL | he
  · have hxc' := hL.reachable
    rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (hxc'.trans h)
    · exact Or.inr (Or.inl ⟨hxc'.trans h1, h2⟩)
    · exact Or.inr (Or.inr ⟨hxc'.trans h1, h2⟩)
  · rw [SimpleGraph.edge_adj] at he
    obtain ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -⟩ := he
    · have hx : L.Reachable x x := SimpleGraph.Reachable.refl _
      rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr (Or.inl ⟨hx, h⟩)
      · exact Or.inl (h1.symm.trans h2)
      · exact Or.inl h2
    · have hx : L.Reachable x x := SimpleGraph.Reachable.refl _
      rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr (Or.inr ⟨hx, h⟩)
      · exact Or.inl h2
      · exact Or.inr (Or.inr ⟨hx, h2⟩)

/-- N2 auxiliary: given bridging `L`-paths `u ~ a` and `b ~ v`,
the two one-edge extensions have the same reachability. -/
private theorem nw_reachable_sup_edge_eq_aux {V : Type*} (L : SimpleGraph V)
    (a b u v : V) (huv : ¬ L.Reachable u v)
    (h1 : L.Reachable u a) (h2 : L.Reachable b v) (p q : V) :
    (L ⊔ SimpleGraph.edge a b).Reachable p q ↔
      (L ⊔ SimpleGraph.edge u v).Reachable p q := by
  have hne : u ≠ v := fun h => huv (h ▸ SimpleGraph.Reachable.refl _)
  have hneAB : a ≠ b := by
    intro h
    apply huv
    subst h
    exact h1.trans h2
  have habEdge : (L ⊔ SimpleGraph.edge a b).Adj a b :=
    SimpleGraph.sup_adj _ _ _ _ |>.mpr (Or.inr
      (SimpleGraph.edge_adj _ _ _ _ |>.mpr ⟨Or.inl ⟨rfl, rfl⟩, hneAB⟩))
  have hbaEdge : (L ⊔ SimpleGraph.edge a b).Adj b a :=
    SimpleGraph.sup_adj _ _ _ _ |>.mpr (Or.inr
      (SimpleGraph.edge_adj _ _ _ _ |>.mpr ⟨Or.inr ⟨rfl, rfl⟩, hneAB.symm⟩))
  have huvEdge : (L ⊔ SimpleGraph.edge u v).Adj u v :=
    SimpleGraph.sup_adj _ _ _ _ |>.mpr (Or.inr
      (SimpleGraph.edge_adj _ _ _ _ |>.mpr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩))
  have hvuEdge : (L ⊔ SimpleGraph.edge u v).Adj v u :=
    SimpleGraph.sup_adj _ _ _ _ |>.mpr (Or.inr
      (SimpleGraph.edge_adj _ _ _ _ |>.mpr ⟨Or.inr ⟨rfl, rfl⟩, hne.symm⟩))
  have key1 : ∀ x y : V, (L ⊔ SimpleGraph.edge a b).Adj x y →
      (L ⊔ SimpleGraph.edge u v).Reachable x y := by
    intro x y hxy
    rw [SimpleGraph.sup_adj] at hxy
    rcases hxy with hL2 | he
    · exact SimpleGraph.Reachable.mono le_sup_left hL2.reachable
    · rw [SimpleGraph.edge_adj] at he
      obtain ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -⟩ := he
      · exact ((SimpleGraph.Reachable.mono le_sup_left h1.symm).trans
          huvEdge.reachable).trans
          (SimpleGraph.Reachable.mono le_sup_left h2.symm)
      · exact ((SimpleGraph.Reachable.mono le_sup_left h2).trans
          hvuEdge.reachable).trans
          (SimpleGraph.Reachable.mono le_sup_left h1)
  have key2 : ∀ x y : V, (L ⊔ SimpleGraph.edge u v).Adj x y →
      (L ⊔ SimpleGraph.edge a b).Reachable x y := by
    intro x y hxy
    rw [SimpleGraph.sup_adj] at hxy
    rcases hxy with hL2 | he
    · exact SimpleGraph.Reachable.mono le_sup_left hL2.reachable
    · rw [SimpleGraph.edge_adj] at he
      obtain ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -⟩ := he
      · exact ((SimpleGraph.Reachable.mono le_sup_left h1).trans
          habEdge.reachable).trans
          (SimpleGraph.Reachable.mono le_sup_left h2)
      · exact ((SimpleGraph.Reachable.mono le_sup_left h2.symm).trans
          hbaEdge.reachable).trans
          (SimpleGraph.Reachable.mono le_sup_left h1.symm)
  constructor
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
    exact Relation.ReflTransGen.lift' id
      (fun x y hxy => (SimpleGraph.reachable_iff_reflTransGen x y).mp (key1 x y hxy)) _ _ h
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
    exact Relation.ReflTransGen.lift' id
      (fun x y hxy => (SimpleGraph.reachable_iff_reflTransGen x y).mp (key2 x y hxy)) _ _ h

/-- N2. Edge exchange preserves the connectivity partition. -/
private theorem nw_reachable_sup_edge_eq_of_not_reachable {V : Type*}
    (L : SimpleGraph V) (a b u v : V) (huv : ¬ L.Reachable u v)
    (hab : (L ⊔ SimpleGraph.edge a b).Reachable u v) (p q : V) :
    (L ⊔ SimpleGraph.edge a b).Reachable p q ↔
      (L ⊔ SimpleGraph.edge u v).Reachable p q := by
  rcases nw_reachable_sup_edge_cases L a b u v hab with hL | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd hL huv
  · exact nw_reachable_sup_edge_eq_aux L a b u v huv h1 h2 p q
  · -- mirror image: swap the roles of a and b via edge symmetry
    have ecomm : SimpleGraph.edge a b = SimpleGraph.edge b a := by
      apply SimpleGraph.edgeSet_inj.mp
      rw [SimpleGraph.edgeSet_edge, SimpleGraph.edgeSet_edge]
      ext e
      simp only [Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hmem, hdiag⟩
        exact ⟨hmem.trans Sym2.eq_swap, hdiag⟩
      · rintro ⟨hmem, hdiag⟩
        exact ⟨hmem.trans Sym2.eq_swap.symm, hdiag⟩
    rw [ecomm]
    exact nw_reachable_sup_edge_eq_aux L b a u v huv h1 h2 p q

/-- N3. Every edge of the unique path in a forest separates its ends. -/
private theorem nw_not_reachable_deleteEdges_of_mem_path {V : Type*}
    (F : SimpleGraph V) (hF : F.IsAcyclic) {u v : V} (p : F.Walk u v) (hp : p.IsPath)
    {g : Sym2 V} (hg : g ∈ p.edges) : ¬ (F.deleteEdges {g}).Reachable u v := by
  classical
  intro hcon
  refine Sym2.ind (fun a b => ?_) g hg hcon
  intro hg hcon
  rw [SimpleGraph.reachable_deleteEdges_iff_exists_walk] at hcon
  obtain ⟨q, hq⟩ := hcon
  have hsub := SimpleGraph.Walk.edges_toPath_subset_edges q
  have := hF.subsingleton_path u v
  have heq : (⟨p, hp⟩ : F.Path u v) = q.toPath := Subsingleton.elim _ _
  have hedg : p.edges = (q.toPath : F.Walk u v).edges :=
    congrArg (fun P : F.Path u v => (P : F.Walk u v).edges) heq
  rw [hedg] at hg
  exact hq (hsub hg)

/-- N4. A forest on a nonempty finite type has fewer edges than vertices. -/
private theorem nw_card_edgeSet_add_one_le_of_isAcyclic {W : Type*} [Finite W] [Nonempty W]
    (H : SimpleGraph W) (hH : H.IsAcyclic) :
    Nat.card H.edgeSet + 1 ≤ Nat.card W := by
  obtain ⟨T, hHT, -, hT⟩ :=
    SimpleGraph.Connected.exists_isTree_le_of_le_of_isAcyclic
      (G := SimpleGraph.completeGraph W) (H := H)
      SimpleGraph.connected_top (fun v w h => h.ne) hH
  classical
  let := Fintype.ofFinite W
  have h2 : T.edgeFinset.card + 1 = Fintype.card W := hT.card_edgeFinset
  have h1 : H.edgeFinset.card ≤ T.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hHT)
  have e1 : Nat.card H.edgeSet = H.edgeFinset.card := by
    rw [SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
  have e2 : Nat.card W = Fintype.card W := Nat.card_eq_fintype_card
  omega

/-- N5. The forward Nash–Williams bound: each color class restricted to `U`
is a forest, hence has at most `|U| - 1` edges. -/
private theorem nw_card_induce_le_of_isArboricityColoring {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (C : G.EdgeLabeling (Fin k)) (hC : ∀ i : Fin k, (C.labelGraph i).IsAcyclic)
    (U : Finset V) (hU : U.Nonempty) :
    (G.induce (U : Set V)).edgeFinset.card ≤ k * (U.card - 1) := by
  classical
  have h1U : 1 ≤ U.card := Finset.card_pos.mpr hU
  -- Per-class bound via N4 on the subtype of U.
  have hBi : ∀ i : Fin k,
      ((C.labelGraph i).induce (U : Set V)).edgeFinset.card ≤ U.card - 1 := by
    intro i
    have hAc := (hC i).induce (U : Set V)
    obtain ⟨x, hx⟩ := hU
    have hne : Nonempty ↥(U : Set V) := ⟨⟨x, Finset.mem_coe.mpr hx⟩⟩
    have hN := nw_card_edgeSet_add_one_le_of_isAcyclic
      ((C.labelGraph i).induce (U : Set V)) hAc
    rw [SimpleGraph.edgeFinset_card]
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hN
    have eU : Fintype.card ↥(U : Set V) = U.card := by
      rw [← Nat.card_eq_fintype_card]
      exact Set.ncard_coe_finset U
    omega
  -- Every edge of G[U] lies in some class.
  have hsub : (G.induce (U : Set V)).edgeFinset ⊆
      Finset.univ.biUnion (fun i => ((C.labelGraph i).induce (U : Set V)).edgeFinset) := by
    intro e he
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine Sym2.ind (fun x y => ?_) e he
    intro he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      SimpleGraph.induce_adj] at he
    refine ⟨C ⟨s(↑x, ↑y), he⟩, ?_⟩
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      SimpleGraph.induce_adj, SimpleGraph.EdgeLabeling.labelGraph_adj]
    exact ⟨he, rfl⟩
  calc (G.induce (U : Set V)).edgeFinset.card
      ≤ (Finset.univ.biUnion
          (fun i => ((C.labelGraph i).induce (U : Set V)).edgeFinset)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ i : Fin k, ((C.labelGraph i).induce (U : Set V)).edgeFinset.card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin k, (U.card - 1) := Finset.sum_le_sum (fun i _ => hBi i)
    _ = k * (U.card - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- `nwForest S R c x i`: color class `i` of the near-coloring `(S, x, c)`
restricted to `R`: the graph on edges of `S ∩ R` labeled `i`, minus `x`. -/
private def nwForest {V : Type*} {k : ℕ} (S : Finset (Sym2 V)) (R : Set (Sym2 V))
    (c : Sym2 V → Fin k) (x : Sym2 V) (i : Fin k) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | e ∈ S ∧ e ∈ R ∧ e ≠ x ∧ c e = i}

/-- `nwNear S c x`: `x ∈ S` and every class of `(S, x, c)` is a forest. -/
private def nwNear {V : Type*} {k : ℕ} (S : Finset (Sym2 V)) (c : Sym2 V → Fin k)
    (x : Sym2 V) : Prop :=
  x ∈ S ∧ ∀ i : Fin k, (nwForest S Set.univ c x i).IsAcyclic

/-- `nwFull k S`: `S` admits a full forest coloring. -/
private def nwFull {V : Type*} (k : ℕ) (S : Finset (Sym2 V)) : Prop :=
  ∃ c : Sym2 V → Fin k, ∀ i : Fin k,
    (SimpleGraph.fromEdgeSet {e | e ∈ S ∧ c e = i}).IsAcyclic

/-- `nwMove S`: one exchange step. From uncovered `x` (with `x = s(u,v)`),
relabel `x` with `y`'s color, making `y` uncovered; allowed when `u, v`
are disconnected in class `c y` with `y` removed. -/
private def nwMove {V : Type*} {k : ℕ} [DecidableEq V] (S : Finset (Sym2 V)) :
    (Sym2 V × (Sym2 V → Fin k)) → (Sym2 V × (Sym2 V → Fin k)) → Prop
  | (x, c), (y, c') => ∃ u v : V, x = s(u, v) ∧ y ∈ S ∧ y ≠ x ∧
      c' = Function.update c x (c y) ∧
      ¬ ((nwForest S Set.univ c x (c y)).deleteEdges {y}).Reachable u v

/-- `nwReached S s0`: edges uncovered in some state reachable from `s0`. -/
private def nwReached {V : Type*} {k : ℕ} [DecidableEq V] (S : Finset (Sym2 V))
    (s0 : Sym2 V × (Sym2 V → Fin k)) : Set (Sym2 V) :=
  {y | ∃ t, Relation.ReflTransGen (nwMove S) s0 t ∧ t.1 = y}

/-- N6(a). Other color classes are unchanged by a move. -/
private theorem nwForest_update_of_ne {V : Type*} {k : ℕ} [DecidableEq V]
    (S : Finset (Sym2 V)) (R : Set (Sym2 V)) (c : Sym2 V → Fin k) (x y : Sym2 V)
    (j : Fin k) (hji : j ≠ c y) :
    nwForest S R (Function.update c x (c y)) y j = nwForest S R c x j := by
  apply SimpleGraph.edgeSet_inj.mp
  ext e
  simp only [nwForest, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hS, hR, hney, hce⟩, hdiag⟩
    have hex : e ≠ x := by
      rintro rfl
      rw [Function.update_self] at hce
      exact hji hce.symm
    have hupd : Function.update c x (c y) e = c e := Function.update_of_ne hex _ _
    rw [hupd] at hce
    exact ⟨⟨hS, hR, hex, hce⟩, hdiag⟩
  · rintro ⟨⟨hS, hR, hex, hce⟩, hdiag⟩
    have hney : e ≠ y := by
      rintro rfl
      exact hji hce.symm
    have hupd : Function.update c x (c y) e = c e := Function.update_of_ne hex _ _
    rw [hupd]
    exact ⟨⟨hS, hR, hney, hce⟩, hdiag⟩

/-- N6(b). The updated class is the old class minus `y` plus the new edge. -/
private theorem nwForest_update_self {V : Type*} {k : ℕ} [DecidableEq V]
    (S : Finset (Sym2 V)) (R : Set (Sym2 V)) (c : Sym2 V → Fin k) (x y : Sym2 V)
    (hxS : x ∈ S) (hxR : x ∈ R) (hxy : y ≠ x) {u v : V} (hxuv : x = s(u, v)) :
    nwForest S R (Function.update c x (c y)) y (c y) =
      ((nwForest S R c x (c y)).deleteEdges {y}) ⊔ SimpleGraph.edge u v := by
  apply SimpleGraph.edgeSet_inj.mp
  ext e
  simp only [nwForest, SimpleGraph.edgeSet_fromEdgeSet, SimpleGraph.edgeSet_sup,
    SimpleGraph.edgeSet_deleteEdges, SimpleGraph.edgeSet_edge, Set.mem_sdiff,
    Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hS, hR, hney, hce⟩, hdiag⟩
    by_cases hex : e = x
    · subst hex
      exact Or.inr ⟨hxuv, hdiag⟩
    · have hupd : Function.update c x (c y) e = c e := Function.update_of_ne hex _ _
      rw [hupd] at hce
      exact Or.inl ⟨⟨⟨hS, hR, hex, hce⟩, hdiag⟩, hney⟩
  · rintro (⟨⟨⟨hS, hR, hex, hce⟩, hdiag⟩, hney⟩ | ⟨heu, hdiag⟩)
    · have hupd : Function.update c x (c y) e = c e := Function.update_of_ne hex _ _
      rw [hupd]
      exact ⟨⟨hS, hR, hney, hce⟩, hdiag⟩
    · have hex : e = x := heu.trans hxuv.symm
      subst hex
      rw [Function.update_self]
      exact ⟨⟨hxS, hxR, hxy.symm, rfl⟩, hdiag⟩

/-- N6(c). A class is itself minus `y` plus the edge `y`. -/
private theorem nwForest_eq_deleteEdges_sup_edge {V : Type*} {k : ℕ}
    (S : Finset (Sym2 V)) (R : Set (Sym2 V)) (c : Sym2 V → Fin k) (x y : Sym2 V)
    (hyS : y ∈ S) (hyR : y ∈ R) (hxy : y ≠ x) {a b : V} (hyab : y = s(a, b)) :
    nwForest S R c x (c y) =
      ((nwForest S R c x (c y)).deleteEdges {y}) ⊔ SimpleGraph.edge a b := by
  apply SimpleGraph.edgeSet_inj.mp
  ext e
  simp only [nwForest, SimpleGraph.edgeSet_fromEdgeSet, SimpleGraph.edgeSet_sup,
    SimpleGraph.edgeSet_deleteEdges, SimpleGraph.edgeSet_edge, Set.mem_sdiff,
    Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hS, hR, hnex, hce⟩, hdiag⟩
    by_cases hey : e = y
    · subst hey
      exact Or.inr ⟨hyab, hdiag⟩
    · exact Or.inl ⟨⟨⟨hS, hR, hnex, hce⟩, hdiag⟩, hey⟩
  · rintro (⟨⟨⟨hS, hR, hnex, hce⟩, hdiag⟩, _⟩ | ⟨heu, hdiag⟩)
    · exact ⟨⟨hS, hR, hnex, hce⟩, hdiag⟩
    · have hey : e = y := heu.trans hyab.symm
      subst hey
      exact ⟨⟨hyS, hyR, hxy, rfl⟩, hdiag⟩

/-- N6(d). Monotonicity of `nwForest` in `R`, and below `G`. -/
private theorem nwForest_mono_univ {V : Type*} {k : ℕ}
    (S : Finset (Sym2 V)) (R : Set (Sym2 V)) (c : Sym2 V → Fin k) (x : Sym2 V)
    (i : Fin k) : nwForest S R c x i ≤ nwForest S Set.univ c x i := by
  apply SimpleGraph.fromEdgeSet_mono
  intro e he
  obtain ⟨hS, hR, hnex, hce⟩ := he
  exact ⟨hS, Set.mem_univ e, hnex, hce⟩

private theorem nwForest_le_fromEdgeSet {V : Type*} {k : ℕ}
    (S : Finset (Sym2 V)) (R : Set (Sym2 V)) (c : Sym2 V → Fin k) (x : Sym2 V)
    (i : Fin k) : nwForest S R c x i ≤ SimpleGraph.fromEdgeSet R := by
  apply SimpleGraph.fromEdgeSet_mono
  intro e he
  obtain ⟨hS, hR, hnex, hce⟩ := he
  exact hR

private theorem nwForest_le_of_mem {V : Type*} {k : ℕ}
    (S : Finset (Sym2 V)) (R : Set (Sym2 V)) (c : Sym2 V → Fin k) (x : Sym2 V)
    (i : Fin k) (G : SimpleGraph V) (hSG : ∀ e : Sym2 V, e ∈ S → e ∈ G.edgeSet) :
    nwForest S R c x i ≤ G := by
  change SimpleGraph.fromEdgeSet {e | e ∈ S ∧ e ∈ R ∧ e ≠ x ∧ c e = i} ≤ G
  rw [SimpleGraph.fromEdgeSet_le]
  intro e he
  rw [Set.mem_sdiff] at he
  obtain ⟨⟨hS, _, _, _⟩, _⟩ := he
  exact hSG e hS

/-- N7. If some class cannot reach across the uncovered edge, we are done. -/
private theorem nw_full_of_not_reachable {V : Type*} {k : ℕ}
    (S : Finset (Sym2 V)) (c : Sym2 V → Fin k) (x : Sym2 V)
    (hn : nwNear S c x) {u v : V} (hxuv : x = s(u, v)) (i : Fin k)
    (hreach : ¬ (nwForest S Set.univ c x i).Reachable u v) : nwFull k S := by
  classical
  obtain ⟨hxS, hac⟩ := hn
  change ∃ c_ : Sym2 V → Fin k, ∀ i_ : Fin k,
    (SimpleGraph.fromEdgeSet {e | e ∈ S ∧ c_ e = i_}).IsAcyclic
  refine ⟨Function.update c x i, fun j => ?_⟩
  by_cases hji : i = j
  · subst hji
    have heq : SimpleGraph.fromEdgeSet {e | e ∈ S ∧ Function.update c x i e = i} =
        (nwForest S Set.univ c x i) ⊔ SimpleGraph.edge u v := by
      apply SimpleGraph.edgeSet_inj.mp
      ext e
      simp only [SimpleGraph.edgeSet_fromEdgeSet, SimpleGraph.edgeSet_sup,
        SimpleGraph.edgeSet_edge, Set.mem_sdiff, Set.mem_union, Set.mem_ofPred_eq,
        Set.mem_singleton_iff, nwForest]
      constructor
      · rintro ⟨⟨hS, hce⟩, hdiag⟩
        by_cases hex : e = x
        · subst hex
          exact Or.inr ⟨hxuv, hdiag⟩
        · have hupd : Function.update c x i e = c e :=
            Function.update_of_ne hex _ _
          rw [hupd] at hce
          exact Or.inl ⟨⟨hS, Set.mem_univ e, hex, hce⟩, hdiag⟩
      · rintro (⟨⟨hS, _, hex, hce⟩, hdiag⟩ | ⟨heu, hdiag⟩)
        · have hupd : Function.update c x i e = c e :=
            Function.update_of_ne hex _ _
          rw [hupd]
          exact ⟨⟨hS, hce⟩, hdiag⟩
        · have hex : e = x := heu.trans hxuv.symm
          subst hex
          rw [Function.update_self]
          exact ⟨⟨hxS, rfl⟩, hdiag⟩
    rw [heq]
    exact SimpleGraph.IsAcyclic.sup_edge_of_not_reachable hreach (hac i)
  · have heq : SimpleGraph.fromEdgeSet {e | e ∈ S ∧ Function.update c x i e = j} =
        nwForest S Set.univ c x j := by
      apply SimpleGraph.edgeSet_inj.mp
      ext e
      simp only [SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, Set.mem_ofPred_eq,
        nwForest]
      constructor
      · rintro ⟨⟨hS, hce⟩, hdiag⟩
        have hex : e ≠ x := by
          rintro rfl
          rw [Function.update_self] at hce
          exact hji hce
        have hupd : Function.update c x i e = c e := Function.update_of_ne hex _ _
        rw [hupd] at hce
        exact ⟨⟨hS, Set.mem_univ e, hex, hce⟩, hdiag⟩
      · rintro ⟨⟨hS, _, hex, hce⟩, hdiag⟩
        have hupd : Function.update c x i e = c e := Function.update_of_ne hex _ _
        rw [hupd]
        exact ⟨⟨hS, hce⟩, hdiag⟩
    rw [heq]
    exact hac j

/-- N8(a). Moves preserve near-colorings. -/
private theorem nw_near_of_move {V : Type*} {k : ℕ} [DecidableEq V]
    (S : Finset (Sym2 V)) (c : Sym2 V → Fin k) (x : Sym2 V)
    (hn : nwNear S c x) {y : Sym2 V} {c' : Sym2 V → Fin k}
    (hm : nwMove S (x, c) (y, c')) : nwNear S c' y := by
  obtain ⟨u, v, hxuv, hyS, hxy, rfl, hsep⟩ := hm
  refine ⟨hyS, fun j => ?_⟩
  by_cases hji : j = c y
  · subst hji
    rw [nwForest_update_self S Set.univ c x y hn.1 (Set.mem_univ x) hxy hxuv]
    exact SimpleGraph.IsAcyclic.sup_edge_of_not_reachable hsep
      ((hn.2 (c y)).anti (SimpleGraph.deleteEdges_le _))
  · rw [nwForest_update_of_ne S Set.univ c x y j hji]
    exact hn.2 j

/-- N8(b). All reached states are near-colorings. -/
private theorem nw_near_of_reached {V : Type*} {k : ℕ} [DecidableEq V]
    (S : Finset (Sym2 V)) (c0 : Sym2 V → Fin k) (x0 : Sym2 V)
    (hn0 : nwNear S c0 x0) (t : Sym2 V × (Sym2 V → Fin k))
    (ht : Relation.ReflTransGen (nwMove S) (x0, c0) t) : nwNear S t.2 t.1 := by
  induction ht with
  | refl => exact hn0
  | tail _ hmove ih => exact nw_near_of_move S _ _ ih hmove

/-- Constructor for `nwMove` with explicit components. -/
private theorem nwMove_intro {V : Type*} {k : ℕ} [DecidableEq V]
    (S : Finset (Sym2 V)) (x y : Sym2 V) (c c' : Sym2 V → Fin k)
    {u v : V} (hx : x = s(u, v)) (hyS : y ∈ S) (hxy : y ≠ x)
    (hc : c' = Function.update c x (c y))
    (hsep : ¬ ((nwForest S Set.univ c x (c y)).deleteEdges {y}).Reachable u v) :
    nwMove S (x, c) (y, c') := by
  change ∃ u_ v_ : V, x = s(u_, v_) ∧ y ∈ S ∧ y ≠ x ∧
    c' = Function.update c x (c y) ∧
    ¬ ((nwForest S Set.univ c x (c y)).deleteEdges {y}).Reachable u_ v_
  exact ⟨u, v, hx, hyS, hxy, hc, hsep⟩

/-- N9. Every reachable uncovered edge is joined in the restricted class. -/
private theorem nw_reachable_restricted {V : Type*} {k : ℕ} [DecidableEq V]
    (S : Finset (Sym2 V)) (s0 : Sym2 V × (Sym2 V → Fin k))
    (hNear : nwNear S s0.2 s0.1) (hNo : ¬ nwFull k S)
    (t : Sym2 V × (Sym2 V → Fin k))
    (ht : Relation.ReflTransGen (nwMove S) s0 t)
    (i : Fin k) {u v : V} (huv : t.1 = s(u, v)) :
    (nwForest S (nwReached S s0) t.2 t.1 i).Reachable u v := by
  have hnt := nw_near_of_reached S s0.2 s0.1 hNear t ht
  have hreach : (nwForest S Set.univ t.2 t.1 i).Reachable u v := by
    by_contra hcon
    exact hNo (nw_full_of_not_reachable S t.2 t.1 hnt huv i hcon)
  obtain ⟨p, hp⟩ := SimpleGraph.Reachable.exists_isPath hreach
  have htrans : ∀ g ∈ p.edges,
      g ∈ (nwForest S (nwReached S s0) t.2 t.1 i).edgeSet := by
    intro g hg
    have hgF := SimpleGraph.Walk.edges_subset_edgeSet p hg
    simp only [nwForest, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff,
      Set.mem_ofPred_eq] at hgF
    obtain ⟨⟨hgS, _, hgnet, hgi⟩, hgdiag⟩ := hgF
    have hsep : ¬ ((nwForest S Set.univ t.2 t.1 i).deleteEdges {g}).Reachable u v :=
      nw_not_reachable_deleteEdges_of_mem_path _ (hnt.2 i) p hp hg
    have hmove : nwMove S t (g, Function.update t.2 t.1 i) :=
      nwMove_intro S t.1 g t.2 _ huv hgS hgnet (by rw [hgi]) (by rw [hgi]; exact hsep)
    have hgR : g ∈ nwReached S s0 :=
      ⟨_, Relation.ReflTransGen.tail ht hmove, rfl⟩
    simp only [nwForest, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff,
      Set.mem_ofPred_eq]
    exact ⟨⟨hgS, hgR, hgnet, hgi⟩, hgdiag⟩
  exact SimpleGraph.Walk.reachable (SimpleGraph.Walk.transfer p _ htrans)

/-- Eliminator for `nwMove` with explicit components. -/
private theorem nwMove_elim {V : Type*} {k : ℕ} [DecidableEq V]
    (S : Finset (Sym2 V)) (t t' : Sym2 V × (Sym2 V → Fin k))
    (hm : nwMove S t t') :
    ∃ u v : V, t.1 = s(u, v) ∧ t'.1 ∈ S ∧ t'.1 ≠ t.1 ∧
      t'.2 = Function.update t.2 t.1 (t.2 t'.1) ∧
      ¬ ((nwForest S Set.univ t.2 t.1 (t.2 t'.1)).deleteEdges {t'.1}).Reachable u v := by
  obtain ⟨x, c⟩ := t
  obtain ⟨y, c'⟩ := t'
  exact hm

/-- N10. A move preserves restricted connectivity in every class. -/
private theorem nw_reachable_eq_of_move {V : Type*} {k : ℕ} [DecidableEq V]
    (S : Finset (Sym2 V)) (s0 : Sym2 V × (Sym2 V → Fin k))
    (hNear : nwNear S s0.2 s0.1) (hNo : ¬ nwFull k S)
    (t : Sym2 V × (Sym2 V → Fin k))
    (ht : Relation.ReflTransGen (nwMove S) s0 t)
    (t' : Sym2 V × (Sym2 V → Fin k))
    (hm : nwMove S t t') (i : Fin k) (p q : V) :
    (nwForest S (nwReached S s0) t.2 t.1 i).Reachable p q ↔
      (nwForest S (nwReached S s0) t'.2 t'.1 i).Reachable p q := by
  obtain ⟨u, v, huv, hyS, hxy, hc', hsep⟩ := nwMove_elim S t t' hm
  have hnt := nw_near_of_reached S s0.2 s0.1 hNear t ht
  have hxR : t.1 ∈ nwReached S s0 := ⟨t, ht, rfl⟩
  have ht' : Relation.ReflTransGen (nwMove S) s0 t' := ht.tail hm
  have hyR : t'.1 ∈ nwReached S s0 := ⟨t', ht', rfl⟩
  by_cases hi : i = t.2 t'.1
  · subst hi
    obtain ⟨a, b, hyab⟩ : ∃ a b : V, t'.1 = s(a, b) :=
      Sym2.ind (fun a b => ⟨a, b, rfl⟩) t'.1
    have hold : nwForest S (nwReached S s0) t.2 t.1 (t.2 t'.1) =
        ((nwForest S (nwReached S s0) t.2 t.1 (t.2 t'.1)).deleteEdges {t'.1}) ⊔
          SimpleGraph.edge a b :=
      nwForest_eq_deleteEdges_sup_edge S _ t.2 t.1 t'.1 hyS hyR hxy hyab
    have hnew : nwForest S (nwReached S s0) t'.2 t'.1 (t.2 t'.1) =
        ((nwForest S (nwReached S s0) t.2 t.1 (t.2 t'.1)).deleteEdges {t'.1}) ⊔
          SimpleGraph.edge u v := by
      rw [hc']
      exact nwForest_update_self S _ t.2 t.1 t'.1 hnt.1 hxR hxy huv
    have hLle : ((nwForest S (nwReached S s0) t.2 t.1 (t.2 t'.1)).deleteEdges {t'.1}) ≤
        ((nwForest S Set.univ t.2 t.1 (t.2 t'.1)).deleteEdges {t'.1}) :=
      SimpleGraph.deleteEdges_mono (nwForest_mono_univ S _ t.2 t.1 _)
    have hLsep : ¬ (((nwForest S (nwReached S s0) t.2 t.1
        (t.2 t'.1)).deleteEdges {t'.1}).Reachable u v) := by
      intro hcon
      exact hsep (SimpleGraph.Reachable.mono hLle hcon)
    have hab : (((nwForest S (nwReached S s0) t.2 t.1
        (t.2 t'.1)).deleteEdges {t'.1}) ⊔
        SimpleGraph.edge a b).Reachable u v := by
      rw [← hold]
      exact nw_reachable_restricted S s0 hNear hNo t ht _ huv
    have key := nw_reachable_sup_edge_eq_of_not_reachable _ a b u v hLsep hab p q
    rw [hold, hnew]
    exact key
  · have heq : nwForest S (nwReached S s0) t'.2 t'.1 i =
        nwForest S (nwReached S s0) t.2 t.1 i := by
      rw [hc']
      exact nwForest_update_of_ne S _ t.2 t.1 t'.1 i hi
    rw [heq]

/-- N11(a). Restricted connectivity at `s0` equals that at any reached state. -/
private theorem nw_reachable_base_a {V : Type*} {k : ℕ} [DecidableEq V]
    (S : Finset (Sym2 V)) (s0 : Sym2 V × (Sym2 V → Fin k))
    (hNear : nwNear S s0.2 s0.1) (hNo : ¬ nwFull k S)
    (t : Sym2 V × (Sym2 V → Fin k))
    (ht : Relation.ReflTransGen (nwMove S) s0 t)
    (i : Fin k) (p q : V) :
    (nwForest S (nwReached S s0) s0.2 s0.1 i).Reachable p q ↔
      (nwForest S (nwReached S s0) t.2 t.1 i).Reachable p q := by
  induction ht with
  | refl => exact Iff.rfl
  | tail h1 h2 ih =>
    exact ih.trans (nw_reachable_eq_of_move S s0 hNear hNo _ h1 _ h2 i p q)

/-- N11(b). Every `E*` edge is joined at the base state. -/
private theorem nw_reachable_base_b {V : Type*} {k : ℕ} [DecidableEq V]
    (S : Finset (Sym2 V)) (s0 : Sym2 V × (Sym2 V → Fin k))
    (hNear : nwNear S s0.2 s0.1) (hNo : ¬ nwFull k S)
    (y : Sym2 V) (hy : y ∈ nwReached S s0) {p q : V} (hyy : y = s(p, q))
    (i : Fin k) :
    (nwForest S (nwReached S s0) s0.2 s0.1 i).Reachable p q := by
  obtain ⟨t, ht, rfl⟩ := hy
  exact (nw_reachable_base_a S s0 hNear hNo t ht i p q).mpr
    (nw_reachable_restricted S s0 hNear hNo t ht i hyy)

/-- N12. The `E*`-component of `u0` is connected in every restricted class. -/
private theorem nw_component_connected {V : Type*} {k : ℕ} [DecidableEq V] [Finite V]
    (S : Finset (Sym2 V)) (s0 : Sym2 V × (Sym2 V → Fin k))
    (hNear : nwNear S s0.2 s0.1) (hNo : ¬ nwFull k S)
    {u0 v0 : V} (hx0 : s0.1 = s(u0, v0)) (hne : u0 ≠ v0) :
    ∃ U : Finset V, u0 ∈ U ∧ v0 ∈ U ∧
      ∀ i : Fin k, ((nwForest S (nwReached S s0) s0.2 s0.1 i).induce
        (U : Set V)).Connected := by
  classical
  let := Fintype.ofFinite V
  refine ⟨Finset.univ.filter
    (fun w => (SimpleGraph.fromEdgeSet (nwReached S s0)).Reachable u0 w), ?_, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact SimpleGraph.Reachable.refl _
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hx0R : s0.1 ∈ nwReached S s0 := ⟨s0, Relation.ReflTransGen.refl, rfl⟩
    rw [hx0] at hx0R
    have hadj : (SimpleGraph.fromEdgeSet (nwReached S s0)).Adj u0 v0 := by
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨hx0R, hne⟩
    exact hadj.reachable
  · intro i
    have key : ∀ a b : V, (SimpleGraph.fromEdgeSet (nwReached S s0)).Adj a b →
        (nwForest S (nwReached S s0) s0.2 s0.1 i).Reachable a b := by
      intro a b hadj
      rw [SimpleGraph.fromEdgeSet_adj] at hadj
      obtain ⟨hmem, _⟩ := hadj
      exact nw_reachable_base_b S s0 hNear hNo _ hmem rfl i
    have hiff : ∀ w : V, (SimpleGraph.fromEdgeSet (nwReached S s0)).Reachable u0 w ↔
        (nwForest S (nwReached S s0) s0.2 s0.1 i).Reachable u0 w := by
      intro w
      constructor
      · intro h
        rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
        exact Relation.ReflTransGen.lift' id
          (fun x y hxy => (SimpleGraph.reachable_iff_reflTransGen x y).mp
            (key x y hxy)) _ _ h
      · exact SimpleGraph.Reachable.mono
          (nwForest_le_fromEdgeSet S _ s0.2 s0.1 i)
    have hsupp : (↑(Finset.univ.filter
        (fun w => (SimpleGraph.fromEdgeSet (nwReached S s0)).Reachable u0 w)) : Set V) =
        ((nwForest S (nwReached S s0) s0.2 s0.1 i).connectedComponentMk u0).supp := by
      ext w
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff,
        SimpleGraph.ConnectedComponent.eq]
      constructor
      · intro h
        exact ((hiff w).mp h).symm
      · intro h
        exact (hiff w).mpr h.symm
    rw [hsupp]
    exact SimpleGraph.ConnectedComponent.connected_toSimpleGraph _

/-- N13. `k` edge-disjoint subgraphs connected on `U`, plus one extra edge,
force `k * (|U| - 1) + 1` edges in `G[U]`. -/
private theorem nw_card_induce_ge_of_connected {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (U : Finset V) (A : Fin k → SimpleGraph V)
    {u0 v0 : V} (hu0 : u0 ∈ U) (hv0 : v0 ∈ U)
    (hAG : ∀ i, A i ≤ G)
    (hdisj : ∀ i j : Fin k, i ≠ j → Disjoint (A i) (A j))
    (hno : ∀ i, ¬ (A i).Adj u0 v0)
    (hadj : G.Adj u0 v0)
    (hconn : ∀ i, ((A i).induce (U : Set V)).Connected) :
    k * (U.card - 1) + 1 ≤ (G.induce (U : Set V)).edgeFinset.card := by
  classical
  have hu0' : u0 ∈ (U : Set V) := Finset.mem_coe.mpr hu0
  have hv0' : v0 ∈ (U : Set V) := Finset.mem_coe.mpr hv0
  have h1U : 1 ≤ U.card := Finset.card_pos.mpr ⟨u0, hu0⟩
  -- The extra edge lies in G[U] but in no class.
  have he0Q : s(⟨u0, hu0'⟩, ⟨v0, hv0'⟩) ∈
      (G.induce (U : Set V)).edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      SimpleGraph.induce_adj]
    exact hadj
  have he0P : ∀ i : Fin k, s(⟨u0, hu0'⟩, ⟨v0, hv0'⟩) ∉
      ((A i).induce (U : Set V)).edgeFinset := by
    intro i hi
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      SimpleGraph.induce_adj] at hi
    exact hno i hi
  -- Each class has at least |U| - 1 edges on U.
  have hPi : ∀ i : Fin k, U.card - 1 ≤
      (((A i).induce (U : Set V)).edgeFinset.card) := by
    intro i
    have hle := SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one (hconn i)
    have eU : Nat.card ↥(U : Set V) = U.card := Set.ncard_coe_finset U
    have eP : (((A i).induce (U : Set V)).edgeFinset.card) =
        Nat.card ↥(((A i).induce (U : Set V)).edgeSet) := by
      rw [SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
    omega
  -- Classes sit inside G[U].
  have hPQ : ∀ i : Fin k, ((A i).induce (U : Set V)).edgeFinset ⊆
      (G.induce (U : Set V)).edgeFinset := by
    intro i e he
    rw [SimpleGraph.mem_edgeFinset] at he
    rw [SimpleGraph.mem_edgeFinset]
    revert he
    induction e using Sym2.ind
    next x y =>
      intro he
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj] at he
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj]
      exact hAG i he
  -- Classes are pairwise disjoint.
  have hdisjF : ∀ i j : Fin k, i ≠ j → Disjoint
      (((A i).induce (U : Set V)).edgeFinset)
      (((A j).induce (U : Set V)).edgeFinset) := by
    intro i j hij
    have hd := SimpleGraph.disjoint_edgeSet.mpr (hdisj i j hij)
    rw [Finset.disjoint_left]
    intro e hei hej
    rw [SimpleGraph.mem_edgeFinset] at hei hej
    revert hei hej
    induction e using Sym2.ind
    next x y =>
      intro hei hej
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj] at hei hej
      have m1 : s(↑x, ↑y) ∈ (A i).edgeSet := (SimpleGraph.mem_edgeSet _).mpr hei
      have m2 : s(↑x, ↑y) ∈ (A j).edgeSet := (SimpleGraph.mem_edgeSet _).mpr hej
      exact (Set.disjoint_left.mp hd) m1 m2
  have hnotmem : s(⟨u0, hu0'⟩, ⟨v0, hv0'⟩) ∉ Finset.univ.biUnion
      (fun i => ((A i).induce (U : Set V)).edgeFinset) := by
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    rintro ⟨i, hi⟩
    exact he0P i hi
  have hdisjU : (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
      (fun i => ((A i).induce (U : Set V)).edgeFinset) := by
    intro i _ j _ hij
    exact hdisjF i j hij
  have hsub : insert s(⟨u0, hu0'⟩, ⟨v0, hv0'⟩)
      (Finset.univ.biUnion (fun i => ((A i).induce (U : Set V)).edgeFinset)) ⊆
      (G.induce (U : Set V)).edgeFinset := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ,
      true_and] at he
    rcases he with rfl | ⟨i, hi⟩
    · exact he0Q
    · exact hPQ i hi
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnotmem, Finset.card_biUnion hdisjU] at hcard
  have hsum : k * (U.card - 1) ≤
      ∑ i : Fin k, ((A i).induce (U : Set V)).edgeFinset.card := by
    have hle := Finset.card_nsmul_le_sum (Finset.univ : Finset (Fin k))
      (fun i => ((A i).induce (U : Set V)).edgeFinset.card) (U.card - 1)
      (fun x _ => hPi x)
    rwa [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
  omega

/-- N14. The exchange step: a near-coloring with one uncovered edge extends
to a full coloring of one more edge. -/
private theorem nw_full_insert {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (Hyp : ∀ U : Finset V, U.Nonempty →
      (G.induce (U : Set V)).edgeFinset.card ≤ k * (U.card - 1))
    (S : Finset (Sym2 V)) (hSG : S ⊆ G.edgeFinset)
    (x0 : Sym2 V) (hx0mem : x0 ∈ G.edgeFinset) (hx0S : x0 ∉ S)
    (c0 : Sym2 V → Fin k)
    (hac0 : ∀ i : Fin k,
      (SimpleGraph.fromEdgeSet {e | e ∈ S ∧ c0 e = i}).IsAcyclic) :
    nwFull k (insert x0 S) := by
  by_contra hNo
  have hNear : nwNear (insert x0 S) c0 x0 := by
    refine ⟨Finset.mem_insert_self x0 S, fun i => ?_⟩
    have heq : nwForest (insert x0 S) Set.univ c0 x0 i =
        SimpleGraph.fromEdgeSet {e | e ∈ S ∧ c0 e = i} := by
      apply SimpleGraph.edgeSet_inj.mp
      ext e
      simp only [nwForest, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff,
        Set.mem_ofPred_eq]
      constructor
      · rintro ⟨⟨hS, _, hnex, hce⟩, hdiag⟩
        rw [Finset.mem_insert] at hS
        rcases hS with rfl | hS
        · exact absurd rfl hnex
        · exact ⟨⟨hS, hce⟩, hdiag⟩
      · rintro ⟨⟨hS, hce⟩, hdiag⟩
        refine ⟨⟨?_, Set.mem_univ e, ?_, hce⟩, hdiag⟩
        · rw [Finset.mem_insert]
          exact Or.inr hS
        · intro hcon
          subst hcon
          exact hx0S hS
    rw [heq]
    exact hac0 i
  obtain ⟨u0, v0, hxuv⟩ : ∃ u v : V, x0 = s(u, v) :=
    Sym2.ind (fun a b => ⟨a, b, rfl⟩) x0
  have hx0mem' : s(u0, v0) ∈ G.edgeFinset := hxuv ▸ hx0mem
  have hadj : G.Adj u0 v0 :=
    (SimpleGraph.mem_edgeSet G).mp (SimpleGraph.mem_edgeFinset.mp hx0mem')
  obtain ⟨U, hu0U, hv0U, hconn⟩ := nw_component_connected (insert x0 S) (x0, c0)
    hNear hNo hxuv hadj.ne
  have hAle : ∀ i : Fin k,
      nwForest (insert x0 S) (nwReached (insert x0 S) (x0, c0)) c0 x0 i ≤ G := by
    intro i
    apply nwForest_le_of_mem
    intro e he
    rw [Finset.mem_insert] at he
    rcases he with rfl | he
    · exact SimpleGraph.mem_edgeFinset.mp hx0mem
    · exact SimpleGraph.mem_edgeFinset.mp (hSG he)
  have hdisjA : ∀ i j : Fin k, i ≠ j → Disjoint
      (nwForest (insert x0 S) (nwReached (insert x0 S) (x0, c0)) c0 x0 i)
      (nwForest (insert x0 S) (nwReached (insert x0 S) (x0, c0)) c0 x0 j) := by
    intro i j hij
    rw [← SimpleGraph.disjoint_edgeSet, Set.disjoint_left]
    intro e hei hej
    simp only [nwForest, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff,
      Set.mem_ofPred_eq] at hei hej
    obtain ⟨⟨_, _, _, hci⟩, _⟩ := hei
    obtain ⟨⟨_, _, _, hcj⟩, _⟩ := hej
    exact hij (hci.symm.trans hcj)
  have hnoA : ∀ i : Fin k, ¬
      (nwForest (insert x0 S) (nwReached (insert x0 S) (x0, c0)) c0 x0 i).Adj
        u0 v0 := by
    intro i hadjA
    have hmem : s(u0, v0) ∈
        (nwForest (insert x0 S) (nwReached (insert x0 S) (x0, c0)) c0 x0 i).edgeSet :=
      (SimpleGraph.mem_edgeSet _).mpr hadjA
    simp only [nwForest, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff,
      Set.mem_ofPred_eq] at hmem
    obtain ⟨⟨_, _, hnex, _⟩, _⟩ := hmem
    exact hnex hxuv.symm
  have hconn' : ∀ i : Fin k, (((fun j => nwForest (insert x0 S)
      (nwReached (insert x0 S) (x0, c0)) c0 x0 j) i).induce
      (U : Set V)).Connected := hconn
  have hge := nw_card_induce_ge_of_connected G k U
    (fun j => nwForest (insert x0 S) (nwReached (insert x0 S) (x0, c0)) c0 x0 j)
    hu0U hv0U hAle hdisjA hnoA hadj hconn'
  have hle := Hyp U ⟨u0, hu0U⟩
  omega

/-- N15. The density condition yields an arboricity coloring. -/
private theorem nw_exists_isArboricityColoring {V : Type*} [Finite V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (Hyp : ∀ U : Finset V, U.Nonempty →
      (G.induce (U : Set V)).edgeFinset.card ≤ k * (U.card - 1)) :
    ∃ C : G.EdgeLabeling (Fin k), IsArboricityColoring C := by
  classical
  let := Fintype.ofFinite V
  by_cases hk : k = 0
  · subst hk
    have hnoadj : ∀ u v : V, ¬ G.Adj u v := by
      intro u v hadj
      have hU := Hyp {u, v} ⟨u, Finset.mem_insert_self u {v}⟩
      have hmem : s(⟨u, Finset.mem_coe.mpr (Finset.mem_insert_self u {v})⟩,
          ⟨v, Finset.mem_coe.mpr (Finset.mem_insert.mpr
            (Or.inr (Finset.mem_singleton_self v)))⟩) ∈
          (G.induce (↑({u, v} : Finset V) : Set V)).edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          SimpleGraph.induce_adj]
        exact hadj
      have hpos := Finset.card_pos.mpr ⟨_, hmem⟩
      omega
    have hempty : G.edgeFinset = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      rw [SimpleGraph.mem_edgeFinset] at he
      revert he
      induction e using Sym2.ind
      next x y =>
        intro he
        rw [SimpleGraph.mem_edgeSet] at he
        exact hnoadj x y he
    refine ⟨fun e => False.elim ?_, fun i => ?_⟩
    · have hmem : e.1 ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr e.2
      rw [hempty] at hmem
      exact Finset.notMem_empty e.1 hmem
    · exact Fin.elim0 i
  · have hfull : nwFull k G.edgeFinset := by
      refine Finset.induction_on' G.edgeFinset ?_ ?_
      · set z : Fin k := ⟨0, Nat.pos_of_ne_zero hk⟩ with hzdef
        refine ⟨fun _ => z, fun i => ?_⟩
        have hem : ({e : Sym2 V | e ∈ (∅ : Finset (Sym2 V)) ∧
            (fun _ => z) e = i} : Set (Sym2 V)) = ∅ := by
          ext e
          simp only [Set.mem_ofPred_eq, Finset.notMem_empty, false_and,
            Set.mem_empty_iff_false]
        rw [hem, SimpleGraph.fromEdgeSet_empty]
        exact SimpleGraph.isAcyclic_bot
      · intro a s has hss hnas ih
        obtain ⟨c, hc⟩ := ih
        exact nw_full_insert G k Hyp s hss a has hnas c hc
    obtain ⟨c, hc⟩ := hfull
    refine ⟨fun e => c e.1, fun i => ?_⟩
    have heq : SimpleGraph.EdgeLabeling.labelGraph
        (fun e : ↥G.edgeSet => c (e : Sym2 V)) i =
        SimpleGraph.fromEdgeSet {e | e ∈ G.edgeFinset ∧ c e = i} := by
      apply SimpleGraph.edgeSet_inj.mp
      ext e
      simp only [SimpleGraph.EdgeLabeling.labelGraph,
        SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨⟨h, hc⟩, hdiag⟩
        exact ⟨⟨SimpleGraph.mem_edgeFinset.mpr h, hc⟩, hdiag⟩
      · rintro ⟨⟨hmem, hce⟩, hdiag⟩
        exact ⟨⟨SimpleGraph.mem_edgeFinset.mp hmem, hce⟩, hdiag⟩
    rw [heq]
    exact hc i

/--
**Nash–Williams arboricity theorem.** Let $G$ be a simple graph on a finite vertex set $V$ and let
$k$ be a natural number. Then $G$ has an arboricity coloring with $k$ labels, that is, its edges
can be labeled with $k$ labels so that the edges of each label form a forest, if and only if for
every nonempty set $U \subseteq V$, the number of edges of $G$ with both endpoints in $U$ is at
most $k(|U| - 1)$.

Proves `Wanted` entry `nash_williams_arboricity`.

Source: C. St. J. A. Nash-Williams, J. London Math. Soc. 39 (1964), DOI 10.1112/jlms/s1-39.1.12.
-/
theorem nash_williams_arboricity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    (∃ C : G.EdgeLabeling (Fin k), IsArboricityColoring C) ↔
      ∀ (U : Finset V), U.Nonempty →
        (G.induce (U : Set V)).edgeFinset.card ≤ k * (U.card - 1) := by
  constructor
  · rintro ⟨C, hC⟩ U hU
    exact nw_card_induce_le_of_isArboricityColoring G k C hC U hU
  · intro Hyp
    exact nw_exists_isArboricityColoring G k Hyp

end MathlibExt.Combinatorics.SimpleGraph.NashWilliamsWanted
end
