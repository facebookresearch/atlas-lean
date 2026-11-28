/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.Combinatorics.SimpleGraph.CliqueWidth
public import MathlibExt.Combinatorics.SimpleGraph.RankWidth
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Tree.Basic
/-!
# Rank-width from a clique-width expression

A graph of clique-width at most `k` has rank-width at most `k`. The union tree of a
clique-width expression supplies a rank-decomposition; its cuts have at most `k` row classes.

## References

* S. Oum, *Rank-width and vertex-minors*, J. Combin. Theory Ser. B 95 (2005) 79–100
  (author's revised preprint of 18 April 2005).
* S. Oum and P. Seymour, *Approximating clique-width and branch-width*, J. Combin. Theory
  Ser. B 96 (2006) 514–528 (author's preprint of 20 October 2004).
* S. Oum, *Rank-width: algorithmic and structural results*, Discrete Appl. Math. 231 (2017)
  15–24, arXiv:1601.03800v2.
-/

@[expose] public section
namespace SimpleGraph.HasCliqueWidthAtMost

private theorem cutRank_le_labels {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S : Set V) {k : ℕ} (c : S → Fin k)
    (hc : ∀ x y : S, c x = c y → ∀ z : ↥Sᶜ, G.Adj x z ↔ G.Adj y z) :
    G.cutRank S ≤ k := by
  classical
  let M := (G.adjMatrix (ZMod 2)).submatrix (fun x : S => x.val) (fun z : ↥Sᶜ => z.val)
  let B : Matrix (Fin k) ↥Sᶜ (ZMod 2) := fun i =>
    if h : ∃ x, c x = i then M h.choose else 0
  have hM : M = B.submatrix c id := by
    ext x z
    have hx : ∃ y, c y = c x := ⟨x, rfl⟩
    change M x z = B (c x) z
    dsimp only [B]
    rw [dite_eq_left hx]
    change (if G.Adj x z then (1 : ZMod 2) else 0) =
      if G.Adj hx.choose z then 1 else 0
    rw [hc x hx.choose hx.choose_spec.symm z]
  change M.rank ≤ k
  rw [hM]
  exact (Matrix.rank_submatrix_le B c id).trans (by simpa using Matrix.rank_le_card_height B)

private def glue {A B : Type} (G : SimpleGraph A) (H : SimpleGraph B) (a : A) (b : B) :
    SimpleGraph (A ⊕ B) := (G ⊕g H) ⊔ edge (.inl a) (.inr b)

private theorem glue_isTree {A B : Type} [Finite A] [Finite B]
    {G : SimpleGraph A} {H : SimpleGraph B} (a : A) (b : B)
    (hG : G.IsTree) (hH : H.IsTree) : (glue G H a b).IsTree := by
  classical
  apply isTree_iff_connected_and_card.mpr
  refine ⟨hG.connected.sum_sup_edge hH.connected, ?_⟩
  have hcard : Nat.card (G ⊕g H).edgeSet = Nat.card G.edgeSet + Nat.card H.edgeSet := by
    rw [Nat.card_congr (edgeSetSumEquiv (G := G) (H := H)), Nat.card_sum]
  have he : (glue G H a b).edgeSet = insert s(.inl a, .inr b) (G ⊕g H).edgeSet := by
    rw [glue, edgeSet_sup, edgeSet_edge]
    have hd : ¬s(Sum.inl a, Sum.inr b).IsDiag := by simp
    have hs : ({s(Sum.inl a, Sum.inr b)} : Set (Sym2 (A ⊕ B))) \ Sym2.diagSet =
        {s(Sum.inl a, Sum.inr b)} := by
      ext e
      simp only [Set.mem_sdiff, Set.mem_singleton_iff]
      exact ⟨And.left, fun h => ⟨h, h ▸ hd⟩⟩
    rw [hs]
    exact Set.union_singleton
  have hn : s(.inl a, .inr b) ∉ (G ⊕g H).edgeSet := by simp
  rw [Nat.card_coe_set_eq, he, Set.ncard_insert_of_notMem hn,
    ← Nat.card_coe_set_eq]
  rw [hcard, Nat.card_sum]
  have h₁ := hG.ncard_edgeSet_add_one
  have h₂ := hH.ncard_edgeSet_add_one
  rw [← Nat.card_coe_set_eq] at h₁ h₂
  omega

open scoped Classical in
private theorem neighbor_glue_inl {A B : Type} (G : SimpleGraph A) (H : SimpleGraph B)
    (a x : A) (b : B) : (glue G H a b).neighborSet (.inl x) =
      Sum.inl '' G.neighborSet x ∪ if x = a then {Sum.inr b} else ∅ := by
  classical
  ext y
  cases y <;> simp [glue, neighborSet, edge_adj, eq_comm]

open scoped Classical in
private theorem neighbor_glue_inr {A B : Type} (G : SimpleGraph A) (H : SimpleGraph B)
    (a : A) (b y : B) : (glue G H a b).neighborSet (.inr y) =
      Sum.inr '' H.neighborSet y ∪ if y = b then {Sum.inl a} else ∅ := by
  classical
  ext x
  cases x <;> simp [glue, neighborSet, edge_adj, eq_comm]

open scoped Classical in
private theorem ncard_neighbor_glue_inl {A B : Type} [Finite A] [Finite B]
    (G : SimpleGraph A) (H : SimpleGraph B) (a x : A) (b : B) :
    ((glue G H a b).neighborSet (.inl x)).ncard =
      (G.neighborSet x).ncard + if x = a then 1 else 0 := by
  classical
  rw [neighbor_glue_inl]
  by_cases h : x = a
  · rw [ite_eq_left h, Set.ncard_union_eq (by simp),
      Set.ncard_image_of_injective _ Sum.inl_injective, Set.ncard_singleton, ite_eq_left h]
  · simp [h, Set.ncard_image_of_injective _ Sum.inl_injective]

open scoped Classical in
private theorem ncard_neighbor_glue_inr {A B : Type} [Finite A] [Finite B]
    (G : SimpleGraph A) (H : SimpleGraph B) (a : A) (b y : B) :
    ((glue G H a b).neighborSet (.inr y)).ncard =
      (H.neighborSet y).ncard + if y = b then 1 else 0 := by
  classical
  rw [neighbor_glue_inr]
  by_cases h : y = b
  · rw [ite_eq_left h, Set.ncard_union_eq (by simp),
      Set.ncard_image_of_injective _ Sum.inr_injective, Set.ncard_singleton, ite_eq_left h]
  · simp [h, Set.ncard_image_of_injective _ Sum.inr_injective]

private abbrev Shape := BinaryTree Unit

@[match_pattern] private abbrev Shape.tip : Shape := .nil
@[match_pattern] private abbrev Shape.fork (a b : Shape) : Shape := .node () a b
@[reducible] private def Nodes : Shape → Type
  | .tip => PUnit
  | .fork a b => (PUnit ⊕ Nodes a) ⊕ Nodes b

@[reducible] private def Leaves : Shape → Type
  | .tip => PUnit
  | .fork a b => Leaves a ⊕ Leaves b

@[instance_reducible] private noncomputable def nodesFintype (t : Shape) : Fintype (Nodes t) := by
  induction t using BinaryTree.unitRecOn with
  | base => exact inferInstanceAs (Fintype PUnit)
  | ind a b ia ib =>
    let _ := ia
    let _ := ib
    exact inferInstanceAs (Fintype ((PUnit ⊕ Nodes a) ⊕ Nodes b))

attribute [local instance] nodesFintype

private def root : (t : Shape) → Nodes t
  | .tip => PUnit.unit
  | .fork _ _ => .inl (.inl PUnit.unit)

private def leaf : (t : Shape) → Leaves t → Nodes t
  | .tip, x => x
  | .fork a _, .inl x => .inl (.inr (leaf a x))
  | .fork _ b, .inr x => .inr (leaf b x)

private def tree : (t : Shape) → SimpleGraph (Nodes t)
  | .tip => ⊥
  | .fork a b => glue (glue ⊥ (tree a) PUnit.unit (root a)) (tree b)
      (.inl PUnit.unit) (root b)

private theorem tree_isTree (t : Shape) : (tree t).IsTree := by
  induction t using BinaryTree.unitRecOn with
  | base => exact (IsTree.of_subsingleton : (⊥ : SimpleGraph PUnit).IsTree)
  | ind a b ia ib =>
    exact glue_isTree _ _ (glue_isTree _ _ IsTree.of_subsingleton ia) ib

private theorem leaf_injective (t : Shape) : Function.Injective (leaf t) := by
  induction t using BinaryTree.unitRecOn with
  | base => exact fun _ _ h => h
  | ind a b ia ib =>
    rintro (x | x) (y | y) h
    · exact congrArg Sum.inl (ia (Sum.inr.inj (Sum.inl.inj h)))
    · cases h
    · cases h
    · exact congrArg Sum.inr (ib (Sum.inr.inj h))

open scoped Classical in
private noncomputable def degree (t : Shape) (x : Nodes t) : ℕ :=
  ((tree t).neighborSet x).ncard + if x = root t then 1 else 0

private theorem degree_tip (x : Nodes .tip) : degree .tip x = 1 := by
  cases x
  simp [degree, tree, root]

private theorem degree_fork_root (a b : Shape) : degree (.fork a b) (root (.fork a b)) = 3 := by
  simp [degree, tree, root, ncard_neighbor_glue_inl]

private theorem degree_fork_left (a b : Shape) (x : Nodes a) :
    degree (.fork a b) (.inl (.inr x)) = degree a x := by
  simp [degree, tree, root, ncard_neighbor_glue_inl, ncard_neighbor_glue_inr]
  rfl

private theorem degree_fork_right (a b : Shape) (x : Nodes b) :
    degree (.fork a b) (.inr x) = degree b x := by
  simp [degree, tree, root, ncard_neighbor_glue_inr]
  rfl

private theorem degree_one_or_three (t : Shape) (x : Nodes t) :
    degree t x = 1 ∨ degree t x = 3 := by
  induction t using BinaryTree.unitRecOn with
  | base => exact Or.inl (degree_tip x)
  | ind a b ia ib =>
    rcases x with (u | x) | x
    · cases u
      exact Or.inr (degree_fork_root a b)
    · rw [degree_fork_left]
      exact ia x
    · rw [degree_fork_right]
      exact ib x

private theorem range_leaf (t : Shape) (x : Nodes t) :
    x ∈ Set.range (leaf t) ↔ degree t x = 1 := by
  induction t using BinaryTree.unitRecOn with
  | base => exact ⟨fun _ => degree_tip x, fun _ => ⟨x, rfl⟩⟩
  | ind a b ia ib =>
    rcases x with (u | x) | x
    · cases u
      change _ ↔ degree (.fork a b) (root (.fork a b)) = 1
      rw [degree_fork_root]
      constructor
      · rintro ⟨y, hy⟩
        cases y <;> cases hy
      · intro h
        omega
    · rw [degree_fork_left, ← ia]
      constructor
      · rintro ⟨y, hy⟩
        cases y with
        | inl y => exact ⟨y, Sum.inr.inj (Sum.inl.inj hy)⟩
        | inr y => cases hy
      · rintro ⟨y, rfl⟩
        exact ⟨.inl y, rfl⟩
    · rw [degree_fork_right, ← ib]
      constructor
      · rintro ⟨y, hy⟩
        cases y with
        | inl y => cases hy
        | inr y => exact ⟨y, Sum.inr.inj hy⟩
      · rintro ⟨y, rfl⟩
        exact ⟨.inr y, rfl⟩

private def Rows {V : Type*} (G : SimpleGraph V) {k : ℕ} (l : V → Fin k)
    (S : Set V) : Prop := ∃ c : V → Fin k, ∀ x ∈ S, ∀ y ∈ S,
      c x = c y → l x = l y ∧ ∀ z ∉ S, G.Adj x z ↔ G.Adj y z

private theorem rows_univ {V : Type*} (G : SimpleGraph V) {k : ℕ} (l : V → Fin k) :
    Rows G l Set.univ := ⟨l, fun _ _ _ _ h => ⟨h, fun _ hz => False.elim (hz trivial)⟩⟩

private theorem rows_sum_left {V W : Type*} {G : SimpleGraph V} (H : SimpleGraph W)
    {k : ℕ} {l : V → Fin k} (m : W → Fin k) {S : Set V} (h : Rows G l S) :
    Rows (G ⊕g H) (Sum.elim l m) (Sum.inl '' S) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨Sum.elim c m, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
  obtain ⟨hl, hr⟩ := hc x hx y hy hxy
  refine ⟨hl, ?_⟩
  rintro (z | z) hz
  · exact hr z (fun hs => hz ⟨z, hs, rfl⟩)
  · simp

private theorem rows_sum_right {V W : Type*} (G : SimpleGraph V) {H : SimpleGraph W}
    {k : ℕ} (l : V → Fin k) {m : W → Fin k} {S : Set W} (h : Rows H m S) :
    Rows (G ⊕g H) (Sum.elim l m) (Sum.inr '' S) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨Sum.elim l c, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
  obtain ⟨hl, hr⟩ := hc x hx y hy hxy
  refine ⟨hl, ?_⟩
  rintro (z | z) hz
  · simp
  · exact hr z (fun hs => hz ⟨z, hs, rfl⟩)

private theorem rows_join {V : Type*} {G : SimpleGraph V} {k : ℕ} {l : V → Fin k}
    {S : Set V} (h : Rows G l S) (i j : Fin k) :
    Rows (G ⊔ fromRel (fun x y => l x = i ∧ l y = j)) l S := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun x hx y hy hxy => ?_⟩
  obtain ⟨hl, hr⟩ := hc x hx y hy hxy
  refine ⟨hl, fun z hz => ?_⟩
  have hxz : x ≠ z := fun he => hz (he ▸ hx)
  have hyz : y ≠ z := fun he => hz (he ▸ hy)
  simp only [sup_adj, fromRel_adj, hl, hr z hz]
  tauto

private theorem rows_relabel {V : Type*} {G : SimpleGraph V} {k : ℕ} {l : V → Fin k}
    {S : Set V} (h : Rows G l S) (i j : Fin k) :
    Rows G (fun x => if l x = i then j else l x) S := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun x hx y hy hxy => ?_⟩
  obtain ⟨hl, hr⟩ := hc x hx y hy hxy
  exact ⟨congrArg (fun a => if a = i then j else a) hl, hr⟩

private def part : (t : Shape) → Nodes t → Set (Leaves t)
  | .tip, _ => Set.univ
  | .fork _ _, .inl (.inl _) => Set.univ
  | .fork a _, .inl (.inr x) => Sum.inl '' part a x
  | .fork _ b, .inr x => Sum.inr '' part b x

private def Good (t : Shape) (G : SimpleGraph (Leaves t)) {k : ℕ}
    (l : Leaves t → Fin k) : Prop := ∀ x, Rows G l (part t x)

private theorem good_fork {a b : Shape} {G : SimpleGraph (Leaves a)}
    {H : SimpleGraph (Leaves b)} {k : ℕ} {l : Leaves a → Fin k} {m : Leaves b → Fin k}
    (hG : Good a G l) (hH : Good b H m) : Good (.fork a b) (G ⊕g H) (Sum.elim l m) := by
  rintro ((u | x) | y)
  · exact rows_univ _ _
  · exact rows_sum_left H m (hG x)
  · exact rows_sum_right G l (hH y)

private theorem expression_shape {k : ℕ} {V : Type*} {G : SimpleGraph V} {l : V → Fin k}
    (h : CWExpressible k V G l) : ∃ t, ∃ e : Leaves t ≃ V, Good t (G.comap e) (l ∘ e) := by
  induction h with
  | vertex V i =>
    refine ⟨.tip, Equiv.ofUnique PUnit V, ?_⟩
    intro x
    exact rows_univ _ _
  | @union V W G H l m _ _ ia ib =>
    obtain ⟨a, e, ha⟩ := ia
    obtain ⟨b, f, hb⟩ := ib
    refine ⟨.fork a b, Equiv.sumCongr e f, ?_⟩
    convert good_fork ha hb using 1
    · ext x y
      cases x <;> cases y <;> rfl
    · funext x
      cases x <;> rfl
  | @join V G l i j hij _ ih =>
    obtain ⟨t, e, ht⟩ := ih
    refine ⟨t, e, ?_⟩
    intro x
    convert rows_join (ht x) i j using 1
    ext y z
    simp only [comap_adj, sup_adj, fromRel_adj, Function.comp_apply]
    rw [e.injective.ne_iff]
  | @relabel V G l i j _ ih =>
    obtain ⟨t, e, ht⟩ := ih
    refine ⟨t, e, ?_⟩
    intro x
    exact rows_relabel (ht x) i j
  | @iso V W G l e _ ih =>
    obtain ⟨t, f, ht⟩ := ih
    refine ⟨t, f.trans e, ?_⟩
    convert ht using 1
    · ext x y
      exact map_adj_apply
    · funext x
      simp

private def Boundary {A : Type*} (G : SimpleGraph A) (S : Set A) (i j : A) : Prop :=
  i ∈ S ∧ j ∉ S ∧ ∀ u v, G.Adj u v → s(u, v) ≠ s(i, j) → (u ∈ S ↔ v ∈ S)

private theorem boundary_mem_reachable {A : Type*} {G : SimpleGraph A} {S : Set A} {i j u v : A}
    (h : Boundary G S i j) (hp : (G.deleteEdges {s(i, j)}).Reachable u v) :
    u ∈ S ↔ v ∈ S := by
  obtain ⟨p⟩ := hp
  induction p with
  | nil => rfl
  | @cons u v w huv p ih =>
    obtain ⟨ha, he⟩ := deleteEdges_adj.mp huv
    exact (h.2.2 u v ha he).trans ih

private theorem reachable_delete_cover {A : Type*} {G : SimpleGraph A} (i j x : A)
    (h : G.Reachable i x) : (G.deleteEdges {s(i, j)}).Reachable i x ∨
      (G.deleteEdges {s(i, j)}).Reachable j x := by
  have aux {u v : A} (p : G.Walk u v)
      (hu : (G.deleteEdges {s(i, j)}).Reachable i u ∨
        (G.deleteEdges {s(i, j)}).Reachable j u) :
      (G.deleteEdges {s(i, j)}).Reachable i v ∨
        (G.deleteEdges {s(i, j)}).Reachable j v := by
    induction p with
    | nil => exact hu
    | @cons u v w huv p ih =>
      apply ih
      by_cases he : s(u, v) = s(i, j)
      · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr Reachable.rfl
        · exact Or.inl Reachable.rfl
      · have hv : (G.deleteEdges {s(i, j)}).Adj u v := deleteEdges_adj.mpr ⟨huv, he⟩
        exact hu.imp (fun h => h.trans hv.reachable) (fun h => h.trans hv.reachable)
  obtain ⟨p⟩ := h
  exact aux p (Or.inl Reachable.rfl)

private theorem boundary_side {A : Type*} {G : SimpleGraph A} (hG : G.Connected)
    {S : Set A} {i j : A} (h : Boundary G S i j) :
    {x | (G.deleteEdges {s(i, j)}).Reachable i x} = S := by
  ext x
  constructor
  · intro hx
    exact (boundary_mem_reachable h hx).mp h.1
  · intro hx
    rcases reachable_delete_cover i j x (hG i x) with hi | hj
    · exact hi
    · exact False.elim (h.2.1 ((boundary_mem_reachable h hj).mpr hx))

private theorem boundary_glue_left {A B : Type} {G : SimpleGraph A} (H : SimpleGraph B)
    {S : Set A} {u v : A} (h : Boundary G S u v) (a : A) (b : B) (ha : a ∉ S) :
    Boundary (glue G H a b) (Sum.inl '' S) (.inl u) (.inl v) := by
  refine ⟨⟨u, h.1, rfl⟩, by simpa using h.2.1, ?_⟩
  rintro (x | x) (y | y) hxy hne
  · have hadj : G.Adj x y := by simpa [glue, edge_adj] using hxy
    have he : s(x, y) ≠ s(u, v) := fun he => hne (congrArg (Sym2.map Sum.inl) he)
    simpa using h.2.2 x y hadj he
  · obtain ⟨rfl, rfl⟩ : x = a ∧ y = b := by simpa [glue, edge_adj] using hxy
    simp [ha]
  · obtain ⟨rfl, rfl⟩ : x = b ∧ y = a := by simpa [glue, edge_adj] using hxy
    simp [ha]
  · simp

private theorem boundary_glue_right {A B : Type} (G : SimpleGraph A) {H : SimpleGraph B}
    {S : Set B} {u v : B} (h : Boundary H S u v) (a : A) (b : B) (hb : b ∉ S) :
    Boundary (glue G H a b) (Sum.inr '' S) (.inr u) (.inr v) := by
  refine ⟨⟨u, h.1, rfl⟩, by simpa using h.2.1, ?_⟩
  rintro (x | x) (y | y) hxy hne
  · simp
  · obtain ⟨rfl, rfl⟩ : x = a ∧ y = b := by simpa [glue, edge_adj] using hxy
    simp [hb]
  · obtain ⟨rfl, rfl⟩ : x = b ∧ y = a := by simpa [glue, edge_adj] using hxy
    simp [hb]
  · have hadj : H.Adj x y := by simpa [glue, edge_adj] using hxy
    have he : s(x, y) ≠ s(u, v) := fun he => hne (congrArg (Sym2.map Sum.inr) he)
    simpa using h.2.2 x y hadj he

private theorem boundary_glue_root_left {A B : Type} (G : SimpleGraph A) (H : SimpleGraph B)
    (a : A) (b : B) : Boundary (glue G H a b) (Sum.inl '' Set.univ) (.inl a) (.inr b) := by
  refine ⟨by simp, by simp, ?_⟩
  rintro (x | x) (y | y) hxy hne
  · simp
  · obtain ⟨rfl, rfl⟩ : x = a ∧ y = b := by simpa [glue, edge_adj] using hxy
    exact False.elim (hne rfl)
  · obtain ⟨rfl, rfl⟩ : x = b ∧ y = a := by simpa [glue, edge_adj] using hxy
    exact False.elim (hne (Sym2.eq_swap))
  · simp

private theorem boundary_compl {A : Type*} {G : SimpleGraph A} {S : Set A} {i j : A}
    (h : Boundary G S i j) : Boundary G Sᶜ j i := by
  refine ⟨h.2.1, by simpa using h.1, ?_⟩
  intro u v huv hne
  exact not_congr (h.2.2 u v huv (by simpa [Sym2.eq_swap] using hne))

private theorem boundary_glue_root_right {A B : Type} (G : SimpleGraph A) (H : SimpleGraph B)
    (a : A) (b : B) : Boundary (glue G H a b) (Sum.inr '' Set.univ) (.inr b) (.inl a) := by
  convert boundary_compl (boundary_glue_root_left G H a b) using 1
  ext (x | x) <;> simp

private def region : (t : Shape) → Nodes t → Set (Nodes t)
  | .tip, _ => Set.univ
  | .fork _ _, .inl (.inl _) => Set.univ
  | .fork a _, .inl (.inr x) => (fun y => Sum.inl (Sum.inr y)) '' region a x
  | .fork _ b, .inr x => Sum.inr '' region b x

private theorem region_root (t : Shape) : region t (root t) = Set.univ := by
  cases t <;> rfl

private theorem root_not_region (t : Shape) (x : Nodes t) (hx : x ≠ root t) :
    root t ∉ region t x := by
  cases t with
  | nil => exact False.elim (hx (Subsingleton.elim _ _))
  | node _ a b =>
    rcases x with (u | x) | x
    · exact False.elim (hx (Subsingleton.elim u PUnit.unit ▸ rfl))
    · simp [root, region]
    · simp [root, region]

private theorem region_leaf (t : Shape) (x : Nodes t) (y : Leaves t) :
    leaf t y ∈ region t x ↔ y ∈ part t x := by
  induction t using BinaryTree.unitRecOn with
  | base => rfl
  | ind a b ia ib =>
    rcases x with (u | x) | x
    · rfl
    · cases y with
      | inl y => simpa [leaf, region, part] using ia x y
      | inr y => simp [leaf, region, part]
    · cases y with
      | inl y => simp [leaf, region, part]
      | inr y => simpa [leaf, region, part] using ib x y

private theorem boundary_root_ne {t : Shape} {i j : Nodes t}
    (h : Boundary (tree t) (region t i) i j) : i ≠ root t := by
  intro hi
  exact h.2.1 (by rw [hi, region_root]; trivial)

private theorem tree_boundary (t : Shape) {u v : Nodes t} (h : (tree t).Adj u v) :
    Boundary (tree t) (region t u) u v ∨ Boundary (tree t) (region t v) v u := by
  induction t using BinaryTree.unitRecOn with
  | base => exact False.elim h
  | ind a b ia ib =>
    rcases u with (u | u) | u <;> rcases v with (v | v) | v
    · cases u
      cases v
      simp [tree, glue] at h
    · cases u
      have hv : v = root a := by simpa [tree, glue, edge_adj] using h
      subst v
      right
      have hb := boundary_glue_root_right (⊥ : SimpleGraph PUnit) (tree a) PUnit.unit (root a)
      have hf := boundary_glue_left (tree b) hb (.inl PUnit.unit) (root b) (by simp)
      simpa [tree, region, region_root, Set.image_image, ← Set.range_comp,
        Function.comp_def] using hf
    · cases u
      have hv : v = root b := by simpa [tree, glue, edge_adj] using h
      subst v
      right
      simpa [tree, region, region_root] using
        boundary_glue_root_right (glue ⊥ (tree a) PUnit.unit (root a)) (tree b)
          (.inl PUnit.unit) (root b)
    · cases v
      have hu : u = root a := by simpa [tree, glue, edge_adj] using h
      subst u
      left
      have hb := boundary_glue_root_right (⊥ : SimpleGraph PUnit) (tree a) PUnit.unit (root a)
      have hf := boundary_glue_left (tree b) hb (.inl PUnit.unit) (root b) (by simp)
      simpa [tree, region, region_root, Set.image_image, ← Set.range_comp,
        Function.comp_def] using hf
    · have ha : (tree a).Adj u v := by simpa [tree, glue, edge_adj] using h
      rcases ia ha with hu | hv
      · left
        have hb := boundary_glue_right (⊥ : SimpleGraph PUnit) hu PUnit.unit (root a)
          (root_not_region a u (boundary_root_ne hu))
        have hf := boundary_glue_left (tree b) hb (.inl PUnit.unit) (root b) (by simp)
        simpa [tree, region, Set.image_image, ← Set.range_comp, Function.comp_def] using hf
      · right
        have hb := boundary_glue_right (⊥ : SimpleGraph PUnit) hv PUnit.unit (root a)
          (root_not_region a v (boundary_root_ne hv))
        have hf := boundary_glue_left (tree b) hb (.inl PUnit.unit) (root b) (by simp)
        simpa [tree, region, Set.image_image, ← Set.range_comp, Function.comp_def] using hf
    · simp [tree, glue, edge_adj] at h
    · cases v
      have hu : u = root b := by simpa [tree, glue, edge_adj] using h
      subst u
      left
      simpa [tree, region, region_root] using
        boundary_glue_root_right (glue ⊥ (tree a) PUnit.unit (root a)) (tree b)
          (.inl PUnit.unit) (root b)
    · simp [tree, glue, edge_adj] at h
    · have hb : (tree b).Adj u v := by simpa [tree, glue, edge_adj] using h
      rcases ib hb with hu | hv
      · left
        exact boundary_glue_right (glue ⊥ (tree a) PUnit.unit (root a)) hu
          (Sum.inl PUnit.unit) (root b)
          (root_not_region b u (boundary_root_ne hu))
      · right
        exact boundary_glue_right (glue ⊥ (tree a) PUnit.unit (root a)) hv
          (Sum.inl PUnit.unit) (root b)
          (root_not_region b v (boundary_root_ne hv))

private def finalTree (a b : Shape) : SimpleGraph (Nodes a ⊕ Nodes b) :=
  glue (tree a) (tree b) (root a) (root b)

private def finalLeaf (a b : Shape) : Leaves (.fork a b) → Nodes a ⊕ Nodes b :=
  Sum.map (leaf a) (leaf b)

private def finalRegion (a b : Shape) : Nodes a ⊕ Nodes b → Set (Nodes a ⊕ Nodes b)
  | .inl x => Sum.inl '' region a x
  | .inr x => Sum.inr '' region b x

private def finalPart (a b : Shape) : Nodes a ⊕ Nodes b → Set (Leaves (.fork a b))
  | .inl x => Sum.inl '' part a x
  | .inr x => Sum.inr '' part b x

private theorem final_leaf_region (a b : Shape) (x : Nodes a ⊕ Nodes b)
    (y : Leaves (.fork a b)) : finalLeaf a b y ∈ finalRegion a b x ↔ y ∈ finalPart a b x := by
  cases x <;> cases y <;> simp [finalLeaf, finalRegion, finalPart, region_leaf]

private theorem final_boundary (a b : Shape) {u v : Nodes a ⊕ Nodes b}
    (h : (finalTree a b).Adj u v) :
    Boundary (finalTree a b) (finalRegion a b u) u v ∨
      Boundary (finalTree a b) (finalRegion a b v) v u := by
  rcases u with u | u <;> rcases v with v | v
  · have ha : (tree a).Adj u v := by simpa [finalTree, glue, edge_adj] using h
    rcases tree_boundary a ha with hu | hv
    · exact Or.inl (boundary_glue_left _ hu (root a) (root b)
        (root_not_region a u (boundary_root_ne hu)))
    · exact Or.inr (boundary_glue_left _ hv (root a) (root b)
        (root_not_region a v (boundary_root_ne hv)))
  · obtain ⟨rfl, rfl⟩ : u = root a ∧ v = root b := by
      simpa [finalTree, glue, edge_adj] using h
    left
    simpa [finalTree, finalRegion, region_root] using
      boundary_glue_root_left (tree a) (tree b) (root a) (root b)
  · obtain ⟨rfl, rfl⟩ : u = root b ∧ v = root a := by
      simpa [finalTree, glue, edge_adj] using h
    left
    simpa [finalTree, finalRegion, region_root] using
      boundary_glue_root_right (tree a) (tree b) (root a) (root b)
  · have hb : (tree b).Adj u v := by simpa [finalTree, glue, edge_adj] using h
    rcases tree_boundary b hb with hu | hv
    · exact Or.inl (boundary_glue_right _ hu (root a) (root b)
        (root_not_region b u (boundary_root_ne hu)))
    · exact Or.inr (boundary_glue_right _ hv (root a) (root b)
        (root_not_region b v (boundary_root_ne hv)))

private theorem final_degree_left (a b : Shape) (x : Nodes a) :
    ((finalTree a b).neighborSet (.inl x)).ncard = degree a x :=
  ncard_neighbor_glue_inl (tree a) (tree b) (root a) x (root b)

private theorem final_degree_right (a b : Shape) (x : Nodes b) :
    ((finalTree a b).neighborSet (.inr x)).ncard = degree b x :=
  ncard_neighbor_glue_inr (tree a) (tree b) (root a) (root b) x

private theorem final_leaf_injective (a b : Shape) : Function.Injective (finalLeaf a b) := by
  rintro (x | x) (y | y) h
  · exact congrArg Sum.inl (leaf_injective a (Sum.inl.inj h))
  · cases h
  · cases h
  · exact congrArg Sum.inr (leaf_injective b (Sum.inr.inj h))

private theorem final_range_leaf (a b : Shape) (x : Nodes a ⊕ Nodes b) :
    x ∈ Set.range (finalLeaf a b) ↔ ((finalTree a b).neighborSet x).ncard = 1 := by
  cases x with
  | inl x =>
    rw [final_degree_left, ← range_leaf]
    constructor
    · rintro ⟨y, hy⟩
      cases y with
      | inl y => exact ⟨y, Sum.inl.inj hy⟩
      | inr y => cases hy
    · rintro ⟨y, rfl⟩
      exact ⟨.inl y, rfl⟩
  | inr x =>
    rw [final_degree_right, ← range_leaf]
    constructor
    · rintro ⟨y, hy⟩
      cases y with
      | inl y => cases hy
      | inr y => exact ⟨y, Sum.inr.inj hy⟩
    · rintro ⟨y, rfl⟩
      exact ⟨.inr y, rfl⟩

private noncomputable def decomposition {V : Type*} (a b : Shape)
    (e : Leaves (.fork a b) ≃ V) : RankDecomposition V where
  ι := Nodes a ⊕ Nodes b
  T := finalTree a b
  isTree := glue_isTree (root a) (root b) (tree_isTree a) (tree_isTree b)
  degree_one_or_three := fun x => by
    cases x with
    | inl x => rw [final_degree_left]; exact degree_one_or_three a x
    | inr x => rw [final_degree_right]; exact degree_one_or_three b x
  leaf := ⟨finalLeaf a b ∘ e.symm, (final_leaf_injective a b).comp e.symm.injective⟩
  range_leaf := by
    ext x
    change (∃ y : V, finalLeaf a b (e.symm y) = x) ↔
      ((finalTree a b).neighborSet x).ncard = 1
    rw [← final_range_leaf]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨e.symm y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨e y, by simp⟩

private theorem rows_equiv {V W : Type*} (e : W ≃ V) {G : SimpleGraph V} {k : ℕ}
    {l : V → Fin k} {S : Set W} (h : Rows (G.comap e) (l ∘ e) S) :
    Rows G l (e '' S) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c ∘ e.symm, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
  have hcxy : c x = c y := by simpa using hxy
  obtain ⟨hl, hr⟩ := hc x hx y hy hcxy
  refine ⟨hl, fun z hz => ?_⟩
  have hzs : e.symm z ∉ S := fun hs => hz ⟨e.symm z, hs, e.apply_symm_apply z⟩
  simpa using hr (e.symm z) hzs

private theorem decomposition_side {V : Type*} (a b : Shape) (e : Leaves (.fork a b) ≃ V)
    {i j : Nodes a ⊕ Nodes b} (h : Boundary (finalTree a b) (finalRegion a b i) i j) :
    (decomposition a b e).side i j = e '' finalPart a b i := by
  have hnodes := boundary_side (glue_isTree (root a) (root b) (tree_isTree a)
    (tree_isTree b)).connected h
  change {x | ((finalTree a b).deleteEdges {s(i, j)}).Reachable i x} =
    finalRegion a b i at hnodes
  ext x
  change (finalLeaf a b (e.symm x) ∈
    {z | ((finalTree a b).deleteEdges {s(i, j)}).Reachable i z}) ↔ _
  rw [hnodes, final_leaf_region]
  constructor
  · intro hx
    exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

private theorem decomposition_side_compl {V : Type*} (a b : Shape)
    (e : Leaves (.fork a b) ≃ V) {i j : Nodes a ⊕ Nodes b}
    (h : Boundary (finalTree a b) (finalRegion a b j) j i) :
    (decomposition a b e).side i j = ((decomposition a b e).side j i)ᶜ := by
  have ht : (finalTree a b).Connected :=
    (glue_isTree (root a) (root b) (tree_isTree a) (tree_isTree b)).connected
  have hi := boundary_side ht (boundary_compl h)
  have hj := boundary_side ht h
  ext x
  change (finalLeaf a b (e.symm x) ∈ {z | ((finalTree a b).deleteEdges {s(i, j)}).Reachable i z}) ↔
    finalLeaf a b (e.symm x) ∉ {z | ((finalTree a b).deleteEdges {s(j, i)}).Reachable j z}
  rw [hi, hj]
  rfl

private theorem rows_cutRank {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {l : V → Fin k} {S : Set V} (h : Rows G l S) : G.cutRank S ≤ k := by
  obtain ⟨c, hc⟩ := h
  exact cutRank_le_labels G S (fun x => c x)
    (fun x y hxy z => (hc x x.property y y.property hxy).2 z z.property)

private theorem decomposition_width {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {l : V → Fin k} (a b : Shape) (e : Leaves (.fork a b) ≃ V)
    (h : Good (.fork a b) (G.comap e) (l ∘ e)) :
    (decomposition a b e).HasWidthAtMost G k := by
  have hr (x : Nodes a ⊕ Nodes b) : Rows G l (e '' finalPart a b x) := by
    apply rows_equiv e
    cases x with
    | inl x => exact h (.inl (.inr x))
    | inr x => exact h (.inr x)
  intro i j hij
  change (finalTree a b).Adj i j at hij
  rcases final_boundary a b hij with hi | hj
  · rw [decomposition_side a b e hi]
    exact rows_cutRank (hr i)
  · rw [decomposition_side_compl a b e hj, cutRank_compl, decomposition_side a b e hj]
    exact rows_cutRank (hr j)

/-- **Rank-width is at most clique-width (Oum–Seymour).** If a finite graph has clique-width at
most `k`, it has rank-width at most `k`; this is the inequality `rw(G) ≤ cw(G)` of Oum and
Seymour, *Approximating clique-width and branch-width*, J. Combin. Theory Ser. B 96 (2006),
Proposition 6.3 (also Oum, arXiv:1601.03800v2, Theorem 2.1). -/
theorem hasRankWidthAtMost {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (h : G.HasCliqueWidthAtMost k) : G.HasRankWidthAtMost k := by
  rcases h with he | ⟨l, h⟩
  · let _ := he
    exact Or.inl (by simp)
  · obtain ⟨t, e, ht⟩ := expression_shape h
    cases t with
    | nil =>
      exact Or.inl (by simpa using (Fintype.card_congr e.symm).le)
    | node _ a b =>
      exact Or.inr ⟨decomposition a b e, decomposition_width a b e ht⟩

end SimpleGraph.HasCliqueWidthAtMost
