/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.StronglyConnectedLowlink
import Std.Data.HashSet.Lemmas
import Mathlib.Data.List.Basic

/-!
# Numbering properties of the repository's depth-first search

For the whole-graph traversal `dfsAll adj` of `CSLibExt.Algorithms.Lean.Graph.DepthFirstSearch`,
numbered by preorder index, this module proves the two remaining numbering properties used by
Tarjan's analysis of strongly connected components: descendants are numbered consecutively
(`dfsAll_treeAncestor_of_between`) and every edge leads to a descendant or to an earlier vertex
(`dfsAll_edge_cases`). Hence `dfsAll_isDFSNumbering`, and Tarjan's lowlink test holds for this
search (`dfsAll_isFirstInComponent_iff_lowlinkEqSelf`).

The proof is an invariant of the search machine: its work stack consists of blocks, one per
vertex on the stack, each block holding the pending adjacency entries of its vertex above that
vertex's exit frame, the vertices on the stack forming a path of tree arcs from a root
(R. E. Tarjan, *Depth-first search and linear graph algorithms*, SIAM J. Comput. 1(2) (1972),
§2 and §4).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.StronglyConnectedLowlink

open DepthFirstSearch DepthFirstSearch.Internal

namespace NumberingInternal

variable {V : Type u}

/- The vertices with an exit frame on a work stack, from the top. -/
def actives : List (Frame V) → List V
  | [] => []
  | Frame.enter _ _ :: w => actives w
  | Frame.exit v :: w => v :: actives w

theorem actives_append (a b : List (Frame V)) : actives (a ++ b) = actives a ++ actives b := by
  induction a with
  | nil => rfl
  | cons f a ih => cases f <;> simp [actives, ih]

theorem actives_of_enters {t : Option V} {B : List (Frame V)}
    (h : ∀ f ∈ B, ∃ y, f = Frame.enter t y) : actives B = [] := by
  induction B with
  | nil => rfl
  | cons f B ih =>
      obtain ⟨y, rfl⟩ := h f (by simp)
      exact ih (fun g hg => h g (by simp [hg]))

/- The block structure of a depth-first work stack, relative to tree arcs `parents`:
`Shape parents top w` says that `w` consists of blocks, the top one belonging to `top`, each
block holding enter frames of its vertex above that vertex's exit frame, the vertex below being
the parent; below the last block there are only root enter frames. -/
inductive Shape (parents : List (V × V)) : Option V → List (Frame V) → Prop
  | base (w : List (Frame V)) (h : ∀ f ∈ w, ∃ r, f = Frame.enter none r) : Shape parents none w
  | cons (t : V) (B rest : List (Frame V)) (below : Option V)
      (hB : ∀ f ∈ B, ∃ y, f = Frame.enter (some t) y)
      (hpar : ∀ p, ParentRel parents t p ↔ below = some p)
      (h : Shape parents below rest) :
      Shape parents (some t) (B ++ Frame.exit t :: rest)

theorem actives_base {w : List (Frame V)} (h : ∀ f ∈ w, ∃ r, f = Frame.enter none r) :
    actives w = [] :=
  actives_of_enters h

theorem actives_block {t : V} {B rest : List (Frame V)}
    (hB : ∀ f ∈ B, ∃ y, f = Frame.enter (some t) y) :
    actives (B ++ Frame.exit t :: rest) = t :: actives rest := by
  rw [actives_append, actives_of_enters hB]
  rfl

theorem Shape.anc_top {parents : List (V × V)} :
    ∀ {top : Option V} {w : List (Frame V)}, Shape parents top w →
      ∀ t, top = some t → ∀ a ∈ actives w, TreeAncestor parents a t := by
  intro top w h
  induction h with
  | base w hw =>
      intro t ht
      cases ht
  | cons t B rest below hB hpar h ih =>
      intro t' ht a ha
      cases ht
      rw [actives_block hB] at ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact .refl
      · cases below with
        | none =>
            cases h with
            | base w hw => simp [actives_base hw] at ha
        | some p =>
            exact (ih p rfl a ha).tail ((hpar p).2 rfl)

theorem Shape.active_of_anc {parents : List (V × V)} :
    ∀ {top : Option V} {w : List (Frame V)}, Shape parents top w →
      ∀ t, top = some t → ∀ a, TreeAncestor parents a t → a ∈ actives w := by
  intro top w h
  induction h with
  | base w hw =>
      intro t ht
      cases ht
  | cons t B rest below hB hpar h ih =>
      intro t' ht a ha
      cases ht
      rw [actives_block hB]
      rcases Relation.ReflTransGen.cases_tail ha with rfl | ⟨c, hac, htc⟩
      · simp
      · have hbelow := (hpar c).1 htc
        subst hbelow
        exact List.mem_cons_of_mem _ (ih c rfl a hac)

theorem Shape.head_enter_some {parents : List (V × V)} {top : Option V} {q v : V}
    {w : List (Frame V)} (h : Shape parents top (Frame.enter (some q) v :: w)) :
    top = some q ∧ Shape parents (some q) w := by
  generalize hW : Frame.enter (some q) v :: w = W at h
  cases h with
  | base _ hw =>
      obtain ⟨r, hr⟩ := hw _ (hW ▸ List.mem_cons_self)
      cases hr
  | cons t B rest below hB hpar hrest =>
      cases B with
      | nil => cases hW
      | cons b B =>
          simp only [List.cons_append, List.cons.injEq] at hW
          obtain ⟨rfl, rfl⟩ := hW
          obtain ⟨y, hy⟩ := hB _ List.mem_cons_self
          cases hy
          exact ⟨rfl, Shape.cons q B rest below (fun f hf => hB f (by simp [hf])) hpar hrest⟩

theorem Shape.head_enter_none {parents : List (V × V)} {top : Option V} {r : V}
    {w : List (Frame V)} (h : Shape parents top (Frame.enter none r :: w)) :
    top = none ∧ Shape parents none w ∧ actives (Frame.enter none r :: w) = [] := by
  generalize hW : Frame.enter none r :: w = W at h
  cases h with
  | base _ hw =>
      subst hW
      exact ⟨rfl, Shape.base w (fun f hf => hw f (by simp [hf])), actives_base hw⟩
  | cons t B rest below hB hpar hrest =>
      cases B with
      | nil => cases hW
      | cons b B =>
          simp only [List.cons_append, List.cons.injEq] at hW
          obtain ⟨rfl, rfl⟩ := hW
          obtain ⟨y, hy⟩ := hB _ List.mem_cons_self
          cases hy

theorem Shape.head_exit {parents : List (V × V)} {top : Option V} {v : V}
    {w : List (Frame V)} (h : Shape parents top (Frame.exit v :: w)) :
    ∃ below, Shape parents below w := by
  generalize hW : Frame.exit v :: w = W at h
  cases h with
  | base _ hw =>
      obtain ⟨r, hr⟩ := hw _ (hW ▸ List.mem_cons_self)
      cases hr
  | cons t B rest below hB hpar hrest =>
      cases B with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at hW
          obtain ⟨_, rfl⟩ := hW
          exact ⟨below, hrest⟩
      | cons b B =>
          simp only [List.cons_append, List.cons.injEq] at hW
          obtain ⟨rfl, _⟩ := hW
          obtain ⟨y, hy⟩ := hB _ List.mem_cons_self
          cases hy

/- Adding a tree arc to a new child keeps the shape of a stack whose vertices differ from it. -/
theorem Shape.add_arc {parents : List (V × V)} {c p : V} :
    ∀ {top : Option V} {w : List (Frame V)}, Shape parents top w →
      (∀ t ∈ actives w, t ≠ c) → Shape ((c, p) :: parents) top w := by
  intro top w h
  induction h with
  | base w hw => intro _; exact Shape.base w hw
  | cons t B rest below hB hpar h ih =>
      intro hne
      rw [actives_block hB] at hne
      have htc : t ≠ c := hne t List.mem_cons_self
      refine Shape.cons t B rest below hB (fun q => ?_) (ih fun s hs => hne s (by simp [hs]))
      rw [← hpar q]
      simp only [ParentRel, List.mem_cons, Prod.mk.injEq]
      constructor
      · rintro (⟨h1, _⟩ | h1)
        · exact absurd h1 htc
        · exact h1
      · exact Or.inr

/- Tree ancestry after adding the arc `p → c` to a new leaf `c`, for a descendant `d ≠ c`. -/
theorem treeAncestor_of_add_arc {parents : List (V × V)} {c p : V}
    (hpar : ∀ c' p', (c', p') ∈ parents → c' ≠ c ∧ p' ≠ c) {a d : V}
    (h : TreeAncestor ((c, p) :: parents) a d) (hd : d ≠ c) : TreeAncestor parents a d := by
  induction h with
  | refl => exact .refl
  | @tail b e _ hbe ih =>
      simp only [ParentRel, List.mem_cons, Prod.mk.injEq] at hbe
      rcases hbe with ⟨h1, _⟩ | hbe
      · exact absurd h1 hd
      · exact (ih (hpar e b hbe).2).tail hbe

theorem treeAncestor_mono {parents : List (V × V)} {e : V × V} {a d : V}
    (h : TreeAncestor parents a d) : TreeAncestor (e :: parents) a d := by
  induction h with
  | refl => exact .refl
  | tail _ hbe ih => exact ih.tail (List.mem_cons_of_mem _ hbe)

theorem treeAncestor_new_leaf {parents : List (V × V)} {c p : V}
    (hpar : ∀ c' p', (c', p') ∈ parents → c' ≠ c ∧ p' ≠ c) (hpc : p ≠ c) {a : V}
    (h : TreeAncestor ((c, p) :: parents) a c) : a = c ∨ TreeAncestor parents a p := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨b, hab, hcb⟩
  · exact Or.inl rfl
  · simp only [ParentRel, List.mem_cons, Prod.mk.injEq] at hcb
    rcases hcb with ⟨_, rfl⟩ | hcb
    · exact Or.inr (treeAncestor_of_add_arc hpar hab hpc)
    · exact absurd rfl (hpar c b hcb).1

theorem treeAncestor_from_new_leaf {parents : List (V × V)} {c p : V}
    (hpar : ∀ c' p', (c', p') ∈ parents → c' ≠ c ∧ p' ≠ c) (hpc : p ≠ c) {d : V}
    (h : TreeAncestor ((c, p) :: parents) c d) : d = c := by
  induction h with
  | refl => rfl
  | @tail b e _ hbe ih =>
      subst ih
      simp only [ParentRel, List.mem_cons, Prod.mk.injEq] at hbe
      rcases hbe with ⟨_, rfl⟩ | hbe
      · exact absurd rfl hpc
      · exact absurd rfl (hpar e b hbe).2

theorem idxOf_append_singleton_of_mem [BEq V] [LawfulBEq V] {l : List V} {x v : V}
    (hx : x ∈ l) : (l ++ [v]).idxOf x = l.idxOf x := by
  rw [List.idxOf_append, ite_eq_left hx]

theorem idxOf_append_singleton_self [BEq V] [LawfulBEq V] {l : List V} {v : V} (hv : v ∉ l) :
    (l ++ [v]).idxOf v = l.length := by
  rw [List.idxOf_append, ite_eq_right hv]
  simp

theorem treeAncestor_isolated {parents : List (V × V)} {v : V}
    (hpar : ∀ c' p', (c', p') ∈ parents → c' ≠ v ∧ p' ≠ v) :
    (∀ d, TreeAncestor parents v d → d = v) ∧ (∀ a, TreeAncestor parents a v → a = v) := by
  constructor
  · intro d h
    induction h with
    | refl => rfl
    | @tail b e _ hbe ih =>
        subst ih
        exact absurd rfl (hpar e b hbe).2
  · intro a h
    rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨b, _, hvb⟩
    · rfl
    · exact absurd rfl (hpar v b hvb).1

section Machine

variable [BEq V] [Hashable V] [LawfulBEq V]

/- The vertices discovered so far, in discovery order. -/
def disc (s : Machine V) : List V := s.preorderRev.reverse

/- The discovery number of a vertex: its index in discovery order. -/
def numS (s : Machine V) (x : V) : ℕ := (disc s).idxOf x

/- The invariant of the depth-first search machine used for the numbering properties. -/
structure Inv (adj : DirectedAdjacency V) (s : Machine V) : Prop where
  nodup : s.preorderRev.Nodup
  vis : ∀ v, v ∈ s.visited ↔ v ∈ s.preorderRev
  parDisc : ∀ c p, (c, p) ∈ s.parentsRev → c ∈ s.preorderRev ∧ p ∈ s.preorderRev
  shape : ∃ top, Shape s.parentsRev top s.work
  actDisc : ∀ t ∈ actives s.work, t ∈ s.preorderRev
  active : ∀ a ∈ actives s.work, ∀ x ∈ s.preorderRev, numS s a ≤ numS s x →
    TreeAncestor s.parentsRev a x
  contig : ∀ a x d, a ∈ s.preorderRev → x ∈ s.preorderRev → d ∈ s.preorderRev →
    TreeAncestor s.parentsRev a d → numS s a < numS s x → ¬ TreeAncestor s.parentsRev a x →
    numS s d < numS s x
  edge : ∀ x ∈ s.preorderRev, ∀ y ∈ adj.adjacency x,
    Frame.enter (some x) y ∈ s.work ∨
      (y ∈ s.preorderRev ∧ (TreeAncestor s.parentsRev x y ∨ numS s y < numS s x))

theorem numS_lt {s : Machine V} {x : V} (hx : x ∈ s.preorderRev) :
    numS s x < s.preorderRev.length := by
  have : x ∈ disc s := by simp [disc, hx]
  simpa [numS, disc] using List.idxOf_lt_length_of_mem this

theorem inv_initial (adj : DirectedAdjacency V) (roots : List V) : Inv adj (initial roots) where
  nodup := by simp [initial]
  vis := by simp [initial]
  parDisc := by simp [initial]
  shape := ⟨none, Shape.base _ (by
    intro f hf
    simp only [initial, enterFrames, List.mem_map] at hf
    obtain ⟨r, _, rfl⟩ := hf
    exact ⟨r, rfl⟩)⟩
  actDisc := by
    intro t ht
    have : actives (initial roots : Machine V).work = [] := actives_base (by
      intro f hf
      simp only [initial, enterFrames, List.mem_map] at hf
      obtain ⟨r, _, rfl⟩ := hf
      exact ⟨r, rfl⟩)
    simp [this] at ht
  active := by simp [initial]
  contig := by simp [initial]
  edge := by simp [initial]

omit [BEq V] [Hashable V] [LawfulBEq V] in
theorem actives_enter (par : Option V) (v : V) (w : List (Frame V)) :
    actives (Frame.enter par v :: w) = actives w := rfl

omit [BEq V] [Hashable V] [LawfulBEq V] in
theorem enterFrames_spec (v : V) (xs : List V) :
    ∀ f ∈ enterFrames (some v) xs, ∃ y, f = Frame.enter (some v) y := by
  intro f hf
  simp only [enterFrames, List.mem_map] at hf
  obtain ⟨y, _, rfl⟩ := hf
  exact ⟨y, rfl⟩

omit [LawfulBEq V] in
theorem inv_skip (adj : DirectedAdjacency V) (s : Machine V) (parent : Option V) (v : V)
    (work : List (Frame V)) (hw : s.work = Frame.enter parent v :: work) (hv : v ∈ s.visited)
    (h : Inv adj s) : Inv adj { s with work := work } := by
  obtain ⟨top, hs⟩ := h.shape
  rw [hw] at hs
  have hact : actives work = actives s.work := by rw [hw]; rfl
  have hvpre := (h.vis v).1 hv
  refine ⟨h.nodup, h.vis, h.parDisc, ?_, ?_, ?_, h.contig, ?_⟩
  · cases parent with
    | none => exact ⟨none, (Shape.head_enter_none hs).2.1⟩
    | some q => exact ⟨some q, (Shape.head_enter_some hs).2⟩
  · intro t ht
    exact h.actDisc t (hact ▸ ht)
  · intro a ha
    exact h.active a (hact ▸ ha)
  · intro x hx y hy
    rcases h.edge x hx y hy with hpend | hres
    · rw [hw] at hpend
      rcases List.mem_cons.mp hpend with heq | hmem
      · simp only [Frame.enter.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        right
        refine ⟨hvpre, ?_⟩
        have hxs := (Shape.head_enter_some hs).2
        have hxa : x ∈ actives work := Shape.active_of_anc hxs x rfl x .refl
        by_cases hlt : numS s y < numS s x
        · exact Or.inr hlt
        · exact Or.inl (h.active x (hact ▸ hxa) y hvpre (by omega))
      · exact Or.inl hmem
    · exact Or.inr hres

omit [LawfulBEq V] in
theorem inv_exit (adj : DirectedAdjacency V) (s : Machine V) (v : V)
    (work : List (Frame V)) (hw : s.work = Frame.exit v :: work)
    (h : Inv adj s) : Inv adj { s with work := work, postorderRev := v :: s.postorderRev } := by
  obtain ⟨top, hs⟩ := h.shape
  rw [hw] at hs
  have hact : ∀ t ∈ actives work, t ∈ actives s.work := by
    intro t ht
    rw [hw]
    exact List.mem_cons_of_mem _ ht
  refine ⟨h.nodup, h.vis, h.parDisc, Shape.head_exit hs, ?_, ?_, h.contig, ?_⟩
  · intro t ht
    exact h.actDisc t (hact t ht)
  · intro a ha
    exact h.active a (hact a ha)
  · intro x hx y hy
    rcases h.edge x hx y hy with hpend | hres
    · rw [hw] at hpend
      rcases List.mem_cons.mp hpend with heq | hmem
      · cases heq
      · exact Or.inl hmem
    · exact Or.inr hres

theorem numS_discover_old (s : Machine V) (v x : V) (hx : x ∈ s.preorderRev)
    (s' : Machine V) (hs' : s'.preorderRev = v :: s.preorderRev) : numS s' x = numS s x := by
  unfold numS disc
  rw [hs', List.reverse_cons]
  exact idxOf_append_singleton_of_mem (by simpa using hx)

theorem numS_discover_new (s : Machine V) (v : V) (hv : v ∉ s.preorderRev)
    (s' : Machine V) (hs' : s'.preorderRev = v :: s.preorderRev) :
    numS s' v = s.preorderRev.length := by
  unfold numS disc
  rw [hs', List.reverse_cons, idxOf_append_singleton_self (by simpa using hv)]
  simp

theorem inv_discover_core (adj : DirectedAdjacency V) (s s' : Machine V) (parent : Option V)
    (v : V) (work : List (Frame V)) (hw : s.work = Frame.enter parent v :: work)
    (hv : v ∉ s.visited) (h : Inv adj s)
    (hwork' : s'.work = enterFrames (some v) (adj.adjacency v) ++ Frame.exit v :: work)
    (hvis'' : s'.visited = s.visited.insert v)
    (hpre' : s'.preorderRev = v :: s.preorderRev)
    (hpar' : s'.parentsRev = match parent with
      | none => s.parentsRev
      | some u => (v, u) :: s.parentsRev) : Inv adj s' := by
  obtain ⟨top, hs⟩ := h.shape
  rw [hw] at hs
  have hvpre : v ∉ s.preorderRev := fun hm => hv ((h.vis v).2 hm)
  have hact : actives work = actives s.work := by rw [hw]; rfl
  have hiso : ∀ c' p', (c', p') ∈ s.parentsRev → c' ≠ v ∧ p' ≠ v := by
    intro c' p' hm
    obtain ⟨hc, hp⟩ := h.parDisc c' p' hm
    exact ⟨fun e => hvpre (e ▸ hc), fun e => hvpre (e ▸ hp)⟩
  have hactne : ∀ t ∈ actives work, t ≠ v := by
    intro t ht e
    exact hvpre (e ▸ h.actDisc t (hact ▸ ht))
  have hvis' : ∀ x, x ∈ s'.visited ↔ x ∈ s'.preorderRev := by
    intro x
    rw [hvis'', hpre']
    constructor
    · intro hx
      rcases Std.HashSet.mem_insert.mp hx with hx | hx
      · exact List.mem_cons.mpr (Or.inl (beq_iff_eq.mp hx).symm)
      · exact List.mem_cons.mpr (Or.inr ((h.vis x).mp hx))
    · intro hx
      rcases List.mem_cons.mp hx with hx | hx
      · exact Std.HashSet.mem_insert.mpr (Or.inl (beq_iff_eq.mpr hx.symm))
      · exact Std.HashSet.mem_insert.mpr (Or.inr ((h.vis x).mpr hx))
  have hnodup' : s'.preorderRev.Nodup := by
    rw [hpre']; exact List.nodup_cons.mpr ⟨hvpre, h.nodup⟩
  have hactW : actives s'.work = v :: actives work := by
    rw [hwork', actives_append, actives_of_enters (enterFrames_spec v _)]
    rfl
  have hmemW : ∀ y ∈ adj.adjacency v, Frame.enter (some v) y ∈ s'.work := by
    intro y hy
    rw [hwork']
    exact List.mem_append_left _ (List.mem_map.mpr ⟨y, hy, rfl⟩)
  have hmemW' : ∀ f ∈ work, f ∈ s'.work := by
    intro f hf
    rw [hwork']
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hf)
  have hold : ∀ x ∈ s.preorderRev, numS s' x = numS s x :=
    fun x hx => numS_discover_old s v x hx s' hpre'
  have hnew : numS s' v = s.preorderRev.length := numS_discover_new s v hvpre s' hpre'
  have hmem' : ∀ x, x ∈ s'.preorderRev ↔ x = v ∨ x ∈ s.preorderRev := by
    intro x; rw [hpre', List.mem_cons]
  cases parent with
  | none =>
      obtain ⟨_, hsw, hnil⟩ := Shape.head_enter_none hs
      have hwork_nil : actives work = [] := hnil
      simp only at hpar'
      have hisoV := treeAncestor_isolated hiso
      refine ⟨hnodup', hvis', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro c p hm
        rw [hpar'] at hm
        obtain ⟨hc, hp⟩ := h.parDisc c p hm
        exact ⟨(hmem' c).2 (Or.inr hc), (hmem' p).2 (Or.inr hp)⟩
      · refine ⟨some v, ?_⟩
        rw [hwork', hpar']
        refine Shape.cons v _ work none (enterFrames_spec v _) ?_ hsw
        intro p
        constructor
        · intro hp
          exact absurd rfl (hiso v p hp).1
        · intro hp
          cases hp
      · intro t ht
        rw [hactW, hwork_nil, List.mem_singleton] at ht
        exact (hmem' t).2 (Or.inl ht)
      · intro a ha x hx hax
        rw [hpar']
        rw [hactW, hwork_nil, List.mem_singleton] at ha
        subst a
        rcases (hmem' x).1 hx with hxv | hx
        · subst x; exact .refl
        · have := numS_lt hx
          rw [hold x hx, hnew] at hax
          omega
      · intro a x d ha hx hd had hax hnax
        rw [hpar'] at had hnax
        rcases (hmem' x).1 hx with hxv | hx
        · subst x
          rcases (hmem' d).1 hd with hdv | hd
          · subst d
            exact absurd had hnax
          · rw [hold d hd, hnew]; exact numS_lt hd
        · rcases (hmem' a).1 ha with hav | ha
          · subst a
            have := numS_lt hx
            rw [hnew, hold x hx] at hax
            omega
          · rcases (hmem' d).1 hd with hdv | hd
            · subst d
              exact absurd (hisoV.2 a had ▸ ha) hvpre
            · rw [hold a ha, hold x hx] at hax
              rw [hold d hd, hold x hx]
              exact h.contig a x d ha hx hd had hax hnax
      · intro x hx y hy
        rw [hpar']
        rcases (hmem' x).1 hx with hxv | hx
        · subst x; exact Or.inl (hmemW y hy)
        · rcases h.edge x hx y hy with hpend | ⟨hyp, hres⟩
          · rw [hw] at hpend
            rcases List.mem_cons.mp hpend with heq | hmem
            · cases heq
            · exact Or.inl (hmemW' _ hmem)
          · right
            refine ⟨(hmem' y).2 (Or.inr hyp), ?_⟩
            rw [hold y hyp, hold x hx]
            exact hres
  | some q =>
      obtain ⟨rfl, hsw⟩ := Shape.head_enter_some hs
      simp only at hpar'
      have hqa : q ∈ actives work := Shape.active_of_anc hsw q rfl q .refl
      have hqpre : q ∈ s.preorderRev := h.actDisc q (hact ▸ hqa)
      have hqv : q ≠ v := fun e => hvpre (e ▸ hqpre)
      have harc : ParentRel ((v, q) :: s.parentsRev) v q := List.mem_cons_self
      refine ⟨hnodup', hvis', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro c p hm
        rw [hpar'] at hm
        rcases List.mem_cons.mp hm with heq | hm
        · simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          exact ⟨(hmem' c).2 (Or.inl rfl), (hmem' p).2 (Or.inr hqpre)⟩
        · obtain ⟨hc, hp⟩ := h.parDisc c p hm
          exact ⟨(hmem' c).2 (Or.inr hc), (hmem' p).2 (Or.inr hp)⟩
      · refine ⟨some v, ?_⟩
        rw [hwork', hpar']
        refine Shape.cons v _ work (some q) (enterFrames_spec v _) ?_ (Shape.add_arc hsw hactne)
        intro p
        constructor
        · intro hp
          rcases List.mem_cons.mp hp with heq | hp
          · simp only [Prod.mk.injEq] at heq
            rw [heq.2]
          · exact absurd rfl (hiso v p hp).1
        · intro hp
          cases hp
          exact harc
      · intro t ht
        rw [hactW] at ht
        rcases List.mem_cons.mp ht with htv | ht
        · exact (hmem' t).2 (Or.inl htv)
        · exact (hmem' t).2 (Or.inr (h.actDisc t (hact ▸ ht)))
      · intro a ha x hx hax
        rw [hpar']
        rw [hactW] at ha
        rcases List.mem_cons.mp ha with hav | ha
        · subst a
          rcases (hmem' x).1 hx with hxv | hx
          · subst x; exact .refl
          · have := numS_lt hx
            rw [hold x hx, hnew] at hax
            omega
        · have hapre : a ∈ s.preorderRev := h.actDisc a (hact ▸ ha)
          rcases (hmem' x).1 hx with hxv | hx
          · subst x
            exact (treeAncestor_mono (Shape.anc_top hsw q rfl a ha)).tail harc
          · rw [hold a hapre, hold x hx] at hax
            exact treeAncestor_mono (h.active a (hact ▸ ha) x hx hax)
      · intro a x d ha hx hd had hax hnax
        rw [hpar'] at had hnax
        rcases (hmem' x).1 hx with hxv | hx
        · subst x
          rcases (hmem' d).1 hd with hdv | hd
          · subst d
            exact absurd had hnax
          · rw [hold d hd, hnew]; exact numS_lt hd
        · rcases (hmem' a).1 ha with hav | ha
          · subst a
            have := numS_lt hx
            rw [hnew, hold x hx] at hax
            omega
          · rcases (hmem' d).1 hd with hdv | hd
            · subst d
              rcases treeAncestor_new_leaf hiso hqv had with hav | haq
              · exact absurd (hav ▸ ha) hvpre
              · have haa : a ∈ actives work := Shape.active_of_anc hsw q rfl a haq
                rw [hold a ha, hold x hx] at hax
                exact absurd (treeAncestor_mono (h.active a (hact ▸ haa) x hx hax.le)) hnax
            · have had' : TreeAncestor s.parentsRev a d :=
                treeAncestor_of_add_arc hiso had (fun e => hvpre (e ▸ hd))
              have hnax' : ¬ TreeAncestor s.parentsRev a x :=
                fun h' => hnax (treeAncestor_mono h')
              rw [hold a ha, hold x hx] at hax
              rw [hold d hd, hold x hx]
              exact h.contig a x d ha hx hd had' hax hnax'
      · intro x hx y hy
        rw [hpar']
        rcases (hmem' x).1 hx with hxv | hx
        · subst x; exact Or.inl (hmemW y hy)
        · rcases h.edge x hx y hy with hpend | ⟨hyp, hres⟩
          · rw [hw] at hpend
            rcases List.mem_cons.mp hpend with heq | hmem
            · simp only [Frame.enter.injEq, Option.some.injEq] at heq
              obtain ⟨rfl, rfl⟩ := heq
              exact Or.inr ⟨(hmem' y).2 (Or.inl rfl), Or.inl (Relation.ReflTransGen.single harc)⟩
            · exact Or.inl (hmemW' _ hmem)
          · right
            refine ⟨(hmem' y).2 (Or.inr hyp), ?_⟩
            rw [hold y hyp, hold x hx]
            rcases hres with hres | hres
            · exact Or.inl (treeAncestor_mono hres)
            · exact Or.inr hres

theorem inv_step (adj : DirectedAdjacency V) (roots : List V) {a b : Machine V}
    (hab : Step adj roots a b) (h : Inv adj a) : Inv adj b := by
  cases hab with
  | skip parent v work hw hv => exact inv_skip adj a parent v work hw hv h
  | discover parent v work hw hv =>
      exact inv_discover_core adj a _ parent v work hw hv h rfl rfl rfl rfl
  | exit v work hw => exact inv_exit adj a v work hw h

theorem inv_steps (adj : DirectedAdjacency V) (roots : List V) {b : Machine V}
    (h : Steps adj roots (initial roots) b) : Inv adj b := by
  induction h with
  | refl => exact inv_initial adj roots
  | tail _ hstep ih => exact inv_step adj roots hstep ih

end Machine

end NumberingInternal

open NumberingInternal

variable {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]

omit [BEq V] [Hashable V] [LawfulBEq V] in
private theorem treeAncestor_reverse (l : List (V × V)) (a d : V) :
    TreeAncestor l.reverse a d ↔ TreeAncestor l a d := by
  simp [TreeAncestor, ParentRel]

private theorem dfs_final (adj : DirectedAdjacency V) (roots : List V) :
    ∃ final, Inv adj final ∧ final.work = [] ∧ finish final = dfs adj roots := by
  obtain ⟨final, hsteps, hwork, hfin⟩ := dfs_is_left_first adj roots
  exact ⟨final, inv_steps adj roots hsteps, hwork, hfin⟩

private theorem mem_final (adj : DirectedAdjacency V) (final : Machine V)
    (hfin : finish final = dfs adj adj.vertices) (x : V) : x ∈ final.preorderRev := by
  have := mem_dfsAll_preorder adj x
  rw [dfsAll, ← hfin] at this
  simpa [finish] using this

/-- **Edges of a depth-first search go to descendants or to earlier vertices.** In the
whole-graph traversal `dfsAll adj`, every edge `(x, y)` leads to a descendant of `x` in the
depth-first spanning forest or to a vertex discovered before `x` (R. E. Tarjan, *Depth-first
search and linear graph algorithms*, SIAM J. Comput. 1(2) (1972), §4: besides tree arcs, edges
run from ancestors to descendants, from descendants to ancestors (fronds), or between subtrees
(cross-links), and "a cross-link `(v, w)` always has `NUMBER(v) > NUMBER(w)`"). -/
theorem dfsAll_edge_cases (adj : DirectedAdjacency V) (x y : V) (hxy : adj.Edge x y) :
    TreeAncestor (dfsAll adj).parents x y ∨
      (dfsAll adj).preorder.idxOf y < (dfsAll adj).preorder.idxOf x := by
  obtain ⟨final, hinv, hwork, hfin⟩ := dfs_final adj adj.vertices
  rcases hinv.edge x (mem_final adj final hfin x) y hxy with hpend | ⟨_, hres⟩
  · rw [hwork] at hpend
    simp at hpend
  · rw [dfsAll, ← hfin]
    simpa [finish, treeAncestor_reverse, numS, disc] using hres

/-- **Descendants are numbered consecutively in depth-first search.** In the whole-graph
traversal `dfsAll adj`, if `a` is an ancestor of `d` in the depth-first spanning forest, every
vertex whose preorder index lies between those of `a` and `d` is a descendant of `a` (R. E.
Tarjan, *Depth-first search and linear graph algorithms*, SIAM J. Comput. 1(2) (1972), §2: all
vertices numbered during the call `DFS(w)` are descendants of `w`). -/
theorem dfsAll_treeAncestor_of_between (adj : DirectedAdjacency V) (a d x : V)
    (had : TreeAncestor (dfsAll adj).parents a d)
    (hax : (dfsAll adj).preorder.idxOf a ≤ (dfsAll adj).preorder.idxOf x)
    (hxd : (dfsAll adj).preorder.idxOf x ≤ (dfsAll adj).preorder.idxOf d) :
    TreeAncestor (dfsAll adj).parents a x := by
  obtain ⟨final, hinv, _, hfin⟩ := dfs_final adj adj.vertices
  rw [dfsAll, ← hfin] at had hax hxd ⊢
  simp only [finish, treeAncestor_reverse] at had hax hxd ⊢
  have hmem := mem_final adj final hfin
  by_contra hnax
  have hne : a ≠ x := fun e => hnax (e ▸ .refl)
  have hlt : numS final a < numS final x := by
    refine lt_of_le_of_ne hax (fun e => hne ?_)
    exact (List.idxOf_inj (by simpa [disc] using hmem a)).1 e
  have := hinv.contig a x d (hmem a) (hmem x) (hmem d) had hlt hnax
  change numS final x ≤ numS final d at hxd
  omega

/-- **The repository's depth-first search has the numbering properties of depth-first search.**
For the whole-graph traversal `dfsAll adj` numbered by preorder index, tree arcs are edges,
ancestors come first, descendants are numbered consecutively, and every edge leads to a
descendant or to an earlier vertex (R. E. Tarjan, *Depth-first search and linear graph
algorithms*, SIAM J. Comput. 1(2) (1972), §2–4). -/
theorem dfsAll_isDFSNumbering (adj : DirectedAdjacency V) :
    IsDFSNumbering adj (dfsAll adj).parents (fun v => (dfsAll adj).preorder.idxOf v) :=
  ⟨dfsAll_parent_edge adj, dfsAll_num_le_of_treeAncestor adj,
    dfsAll_treeAncestor_of_between adj, dfsAll_edge_cases adj⟩

/-- **Tarjan's lowlink test for the repository's depth-first search.** In the whole-graph
traversal `dfsAll adj`, a vertex is the first of its strongly connected component in preorder,
that is, the root of the subtree formed by the component, if and only if `LOWLINK(v) = v`
(R. E. Tarjan, *Depth-first search and linear graph algorithms*, SIAM J. Comput. 1(2) (1972),
§4, Lemma 12). -/
theorem dfsAll_isFirstInComponent_iff_lowlinkEqSelf (adj : DirectedAdjacency V) (v : V) :
    IsFirstInComponent adj (fun v => (dfsAll adj).preorder.idxOf v) v ↔
      LowlinkEqSelf adj (dfsAll adj).parents (fun v => (dfsAll adj).preorder.idxOf v) v :=
  isFirstInComponent_iff_lowlinkEqSelf (dfsAll_isDFSNumbering adj) v

/-- **Strongly connected vertices have a common ancestor in their component (depth-first
search).** In the whole-graph traversal `dfsAll adj`, two strongly connected vertices have a
common ancestor in the depth-first spanning forest that lies in their strongly connected
component (R. E. Tarjan, *Depth-first search and linear graph algorithms*, SIAM J. Comput. 1(2)
(1972), §4, Lemma 10). -/
theorem dfsAll_exists_commonAncestor_stronglyConnected (adj : DirectedAdjacency V) {v w : V}
    (hvw : StronglyConnectedComponents.StronglyConnected adj v w) :
    ∃ u, TreeAncestor (dfsAll adj).parents u v ∧ TreeAncestor (dfsAll adj).parents u w ∧
      StronglyConnectedComponents.StronglyConnected adj u v :=
  exists_commonAncestor_stronglyConnected (dfsAll_isDFSNumbering adj) hvw

end Cslib.Algorithms.Lean.StronglyConnectedLowlink
