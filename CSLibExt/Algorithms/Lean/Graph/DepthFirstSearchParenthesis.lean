/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.DepthFirstSearchNumbering
import Mathlib.Data.List.Basic

/-!
# Ancestors in a depth-first forest: interval nesting and white paths

J. Erickson, *Algorithms* (1st ed., 2019), Chapter 6, Lemma 6.1: for any depth-first traversal
of a directed graph, `u` is an ancestor of `v` in the depth-first forest if and only if
(b) `u.pre ≤ v.pre < v.post ≤ u.post`, if and only if (d) just before `DFS(u)` is called there
is a path from `u` to `v` all of whose vertices are new.

* `treeAncestor_iff_whitePath`: (a) ⇔ (d) for every numbering with the depth-first numbering
  properties `IsDFSNumbering`, a vertex being new just before `DFS(u)` exactly when its number
  is at least that of `u`; `dfsAll_treeAncestor_iff_whitePath` for the repository's search.
* `dfsAll_treeAncestor_iff`: (a) ⇔ (b) for the repository's search, with the discovery order
  (`preorder`) and the finishing order (`postorder`) in place of Erickson's single clock:
  `u` is an ancestor of `v` exactly when `u` is discovered no later and finishes no earlier
  than `v`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.StronglyConnectedLowlink

open DepthFirstSearch DepthFirstSearch.Internal NumberingInternal

variable {V : Type u}

section WhitePath

variable {adj : DirectedAdjacency V} {parents : List (V × V)} {num : V → ℕ}

/-- **White-path theorem.** Under the numbering properties of depth-first search, `u` is an
ancestor of `v` in the depth-first forest if and only if `v` is reached from `u` by a path of
edges all of whose vertices have number at least that of `u`, that is, are still new when the
search reaches `u` (J. Erickson, *Algorithms* (2019), Lemma 6.1, (a) ⇔ (d)). -/
theorem treeAncestor_iff_whitePath (h : IsDFSNumbering adj parents num) (u v : V) :
    TreeAncestor parents u v ↔
      Relation.ReflTransGen (fun x y => adj.Edge x y ∧ num u ≤ num y) u v := by
  constructor
  · intro huv
    induction huv with
    | refl => exact .refl
    | @tail b c hub hbc ih =>
        refine ih.tail ⟨h.parent_edge c b hbc, ?_⟩
        exact h.num_le_of_treeAncestor u c (hub.tail hbc)
  · intro hpath
    induction hpath with
    | refl => exact .refl
    | @tail b c _ hbc ih =>
        obtain ⟨hedge, huc⟩ := hbc
        rcases h.edge_cases b c hedge with hbc' | hlt
        · exact ih.trans hbc'
        · exact h.treeAncestor_of_between u b c ih huc hlt.le

end WhitePath

namespace ParenInternal

variable [BEq V] [Hashable V] [LawfulBEq V]

/- The finishing number: the index in finishing order. -/
def postS (s : Machine V) (x : V) : ℕ := s.postorderRev.reverse.idxOf x

/- The invariant relating discovery and finishing. -/
structure Inv2 (s : Machine V) : Prop where
  postSub : ∀ x ∈ s.postorderRev, x ∈ s.preorderRev
  fin : ∀ x ∈ s.preorderRev, x ∈ actives s.work ∨ x ∈ s.postorderRev
  actNotPost : ∀ x ∈ actives s.work, x ∉ s.postorderRev
  actNodup : (actives s.work).Nodup
  paren : ∀ a b, a ∈ s.preorderRev → b ∈ s.preorderRev → numS s a < numS s b →
    ¬ TreeAncestor s.parentsRev a b → a ∈ s.postorderRev ∧
      (b ∈ s.postorderRev → postS s a < postS s b)

theorem inv2_initial (roots : List V) : Inv2 (initial roots) where
  postSub := by simp [initial]
  fin := by simp [initial]
  actNotPost := by simp [initial]
  actNodup := by
    have : actives (initial roots : Machine V).work = [] := actives_base (by
      intro f hf
      simp only [initial, enterFrames, List.mem_map] at hf
      obtain ⟨r, _, rfl⟩ := hf
      exact ⟨r, rfl⟩)
    rw [this]; exact List.nodup_nil
  paren := by simp [initial]

omit [LawfulBEq V] in
theorem inv2_skip (s : Machine V) (parent : Option V) (v : V) (work : List (Frame V))
    (hw : s.work = Frame.enter parent v :: work) (h : Inv2 s) : Inv2 { s with work := work } := by
  have hact : actives work = actives s.work := by rw [hw]; rfl
  exact ⟨h.postSub, fun x hx => hact ▸ h.fin x hx, fun x hx => h.actNotPost x (hact ▸ hx),
    hact ▸ h.actNodup, h.paren⟩

theorem inv2_exit (adj : DirectedAdjacency V) (s : Machine V) (v : V) (work : List (Frame V))
    (hw : s.work = Frame.exit v :: work) (hI : Inv adj s) (h : Inv2 s) :
    Inv2 { s with work := work, postorderRev := v :: s.postorderRev } := by
  have hact : actives s.work = v :: actives work := by rw [hw]; rfl
  have hvact : v ∈ actives s.work := by rw [hact]; exact List.mem_cons_self
  have hvpost : v ∉ s.postorderRev := h.actNotPost v hvact
  have hnd := h.actNodup
  rw [hact, List.nodup_cons] at hnd
  have hpostold : ∀ x ∈ s.postorderRev,
      (v :: s.postorderRev).reverse.idxOf x = s.postorderRev.reverse.idxOf x := by
    intro x hx
    rw [List.reverse_cons]
    exact idxOf_append_singleton_of_mem (by simpa using hx)
  have hpostnew : (v :: s.postorderRev).reverse.idxOf v = s.postorderRev.length := by
    rw [List.reverse_cons, idxOf_append_singleton_self (by simpa using hvpost)]
    simp
  refine ⟨?_, ?_, ?_, hnd.2, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hI.actDisc x hvact
    · exact h.postSub x hx
  · intro x hx
    rcases h.fin x hx with hxa | hxp
    · rw [hact] at hxa
      rcases List.mem_cons.mp hxa with rfl | hxa
      · exact Or.inr List.mem_cons_self
      · exact Or.inl hxa
    · exact Or.inr (List.mem_cons_of_mem _ hxp)
  · intro x hx hxp
    rcases List.mem_cons.mp hxp with rfl | hxp
    · exact hnd.1 hx
    · exact h.actNotPost x (by rw [hact]; exact List.mem_cons_of_mem _ hx) hxp
  · intro a b ha hb hab hnab
    obtain ⟨hapost, hbpost⟩ := h.paren a b ha hb hab hnab
    refine ⟨List.mem_cons_of_mem _ hapost, fun hb' => ?_⟩
    change (v :: s.postorderRev).reverse.idxOf a < (v :: s.postorderRev).reverse.idxOf b
    rw [hpostold a hapost]
    rcases List.mem_cons.mp hb' with rfl | hb'
    · rw [hpostnew]
      have : a ∈ s.postorderRev.reverse := by simpa using hapost
      simpa using List.idxOf_lt_length_of_mem this
    · rw [hpostold b hb']
      exact hbpost hb'

theorem inv2_discover (adj : DirectedAdjacency V) (s s' : Machine V) (parent : Option V)
    (v : V) (work : List (Frame V)) (hw : s.work = Frame.enter parent v :: work)
    (hv : v ∉ s.visited) (hI : Inv adj s) (h : Inv2 s)
    (hwork' : s'.work = enterFrames (some v) (adj.adjacency v) ++ Frame.exit v :: work)
    (hpre' : s'.preorderRev = v :: s.preorderRev)
    (hpost' : s'.postorderRev = s.postorderRev)
    (hpar' : s'.parentsRev = match parent with
      | none => s.parentsRev
      | some u => (v, u) :: s.parentsRev) : Inv2 s' := by
  obtain ⟨top, hs⟩ := hI.shape
  rw [hw] at hs
  have hvpre : v ∉ s.preorderRev := fun hm => hv ((hI.vis v).2 hm)
  have hact : actives work = actives s.work := by rw [hw]; rfl
  have hactW : actives s'.work = v :: actives work := by
    rw [hwork', actives_append, actives_of_enters (enterFrames_spec v _)]
    rfl
  have hold : ∀ x ∈ s.preorderRev, numS s' x = numS s x :=
    fun x hx => numS_discover_old s v x hx s' hpre'
  have hnew : numS s' v = s.preorderRev.length := numS_discover_new s v hvpre s' hpre'
  have hmem' : ∀ x, x ∈ s'.preorderRev ↔ x = v ∨ x ∈ s.preorderRev := by
    intro x; rw [hpre', List.mem_cons]
  have hiso : ∀ c' p', (c', p') ∈ s.parentsRev → c' ≠ v ∧ p' ≠ v := by
    intro c' p' hm
    obtain ⟨hc, hp⟩ := hI.parDisc c' p' hm
    exact ⟨fun e => hvpre (e ▸ hc), fun e => hvpre (e ▸ hp)⟩
  -- every old active vertex is an ancestor of the new vertex
  have hancv : ∀ a ∈ actives work, TreeAncestor s'.parentsRev a v := by
    intro a ha
    cases parent with
    | none =>
        have := (Shape.head_enter_none hs).2.2
        rw [actives_enter] at this
        simp [this] at ha
    | some q =>
        obtain ⟨_, hsw⟩ := Shape.head_enter_some hs
        rw [hpar']
        exact (treeAncestor_mono (Shape.anc_top hsw q rfl a ha)).tail List.mem_cons_self
  -- tree ancestry between old vertices is unchanged
  have hancold : ∀ a b, b ∈ s.preorderRev →
      (TreeAncestor s'.parentsRev a b ↔ TreeAncestor s.parentsRev a b) := by
    intro a b hb
    cases parent with
    | none => rw [hpar']
    | some q =>
        rw [hpar']
        exact ⟨fun hab => treeAncestor_of_add_arc hiso hab (fun e => hvpre (e ▸ hb)),
          treeAncestor_mono⟩
  have hpostS : ∀ x, postS s' x = postS s x := by intro x; simp [postS, hpost']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hpost'] at hx
    exact (hmem' x).2 (Or.inr (h.postSub x hx))
  · intro x hx
    rw [hactW, hpost']
    rcases (hmem' x).1 hx with rfl | hx
    · exact Or.inl List.mem_cons_self
    · rcases h.fin x hx with hxa | hxp
      · exact Or.inl (List.mem_cons_of_mem _ (hact ▸ hxa))
      · exact Or.inr hxp
  · intro x hx hxp
    rw [hactW] at hx
    rw [hpost'] at hxp
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hvpre (h.postSub x hxp)
    · exact h.actNotPost x (hact ▸ hx) hxp
  · rw [hactW, List.nodup_cons]
    refine ⟨fun hva => hvpre (hI.actDisc v (hact ▸ hva)), hact ▸ h.actNodup⟩
  · intro a b ha hb hab hnab
    rw [hpost']
    rcases (hmem' b).1 hb with rfl | hb
    · rcases (hmem' a).1 ha with rfl | ha
      · exact absurd hab (lt_irrefl _)
      · rcases h.fin a ha with haa | hap
        · exact absurd (hancv a (hact ▸ haa)) hnab
        · refine ⟨hap, fun hbp => absurd (h.postSub _ hbp) hvpre⟩
    · rcases (hmem' a).1 ha with rfl | ha
      · have := numS_lt hb
        rw [hnew, hold b hb] at hab
        omega
      · rw [hold a ha, hold b hb] at hab
        rw [hancold a b hb] at hnab
        obtain ⟨h1, h2⟩ := h.paren a b ha hb hab hnab
        exact ⟨h1, fun hbp => by rw [hpostS, hpostS]; exact h2 hbp⟩

theorem inv2_step (adj : DirectedAdjacency V) (roots : List V) {a b : Machine V}
    (hab : Step adj roots a b) (hI : Inv adj a) (h : Inv2 a) : Inv2 b := by
  cases hab with
  | skip parent v work hw hv => exact inv2_skip a parent v work hw h
  | discover parent v work hw hv =>
      exact inv2_discover adj a _ parent v work hw hv hI h rfl rfl rfl rfl
  | exit v work hw => exact inv2_exit adj a v work hw hI h

theorem inv2_steps (adj : DirectedAdjacency V) (roots : List V) {b : Machine V}
    (hsteps : Steps adj roots (initial roots) b) : Inv adj b ∧ Inv2 b := by
  induction hsteps with
  | refl => exact ⟨inv_initial adj roots, inv2_initial roots⟩
  | tail hprev hstep ih =>
      exact ⟨inv_step adj roots hstep ih.1, inv2_step adj roots hstep ih.1 ih.2⟩

end ParenInternal

open ParenInternal

variable [BEq V] [Hashable V] [LawfulBEq V]

/-- **Ancestors by interval nesting.** In the whole-graph traversal `dfsAll adj`, `u` is an
ancestor of `v` in the depth-first forest if and only if `u` is discovered no later than `v` and
finishes no earlier than `v`: `pre(u) ≤ pre(v)` and `post(v) ≤ post(u)` for the indices in
discovery order and in finishing order (J. Erickson, *Algorithms* (2019), Lemma 6.1, (a) ⇔ (b),
`u.pre ≤ v.pre < v.post ≤ u.post` for a single clock). -/
theorem dfsAll_treeAncestor_iff (adj : DirectedAdjacency V) (u v : V) :
    TreeAncestor (dfsAll adj).parents u v ↔
      (dfsAll adj).preorder.idxOf u ≤ (dfsAll adj).preorder.idxOf v ∧
        (dfsAll adj).postorder.idxOf v ≤ (dfsAll adj).postorder.idxOf u := by
  constructor
  · intro huv
    refine ⟨dfsAll_num_le_of_treeAncestor adj u v huv, ?_⟩
    induction huv with
    | refl => exact le_rfl
    | @tail b c _ hbc ih =>
        have hb := DepthFirstSearch.child_before_parent_postorder adj adj.vertices c b hbc
        exact (idxOf_lt_of_before hb
          (DepthFirstSearch.postorder_nodup adj adj.vertices)).le.trans ih
  · rintro ⟨hpre, hpost⟩
    obtain ⟨final, hsteps, hwork, hfin⟩ := dfs_is_left_first adj adj.vertices
    obtain ⟨hI, h2⟩ := inv2_steps adj adj.vertices hsteps
    have hmem : ∀ x, x ∈ final.preorderRev := by
      intro x
      have := mem_dfsAll_preorder adj x
      rw [dfsAll, ← hfin] at this
      simpa [finish] using this
    have hnoact : actives final.work = [] := by rw [hwork]; rfl
    have hpostmem : ∀ x, x ∈ final.postorderRev := by
      intro x
      rcases h2.fin x (hmem x) with hx | hx
      · simp [hnoact] at hx
      · exact hx
    rw [dfsAll, ← hfin] at hpre hpost ⊢
    simp only [finish, treeAncestor_reverse] at hpre hpost ⊢
    by_contra hnuv
    have hne : u ≠ v := fun e => hnuv (e ▸ .refl)
    have hlt : numS final u < numS final v := by
      refine lt_of_le_of_ne hpre (fun e => hne ?_)
      exact (List.idxOf_inj (by simpa [disc] using hmem u)).1 e
    have := (h2.paren u v (hmem u) (hmem v) hlt hnuv).2 (hpostmem v)
    change postS final v ≤ postS final u at hpost
    omega

/-- **White-path theorem for the repository's depth-first search.** In the whole-graph traversal
`dfsAll adj`, `u` is an ancestor of `v` if and only if `v` is reached from `u` by a path of edges
through vertices discovered no earlier than `u`, that is, new when `u` is discovered
(J. Erickson, *Algorithms* (2019), Lemma 6.1, (a) ⇔ (d)). -/
theorem dfsAll_treeAncestor_iff_whitePath (adj : DirectedAdjacency V) (u v : V) :
    TreeAncestor (dfsAll adj).parents u v ↔
      Relation.ReflTransGen (fun x y => adj.Edge x y ∧
        (dfsAll adj).preorder.idxOf u ≤ (dfsAll adj).preorder.idxOf y) u v :=
  treeAncestor_iff_whitePath (dfsAll_isDFSNumbering adj) u v

end Cslib.Algorithms.Lean.StronglyConnectedLowlink
