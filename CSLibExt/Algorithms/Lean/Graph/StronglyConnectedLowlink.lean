/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.StronglyConnectedComponents

/-!
# Strongly connected components in a depth-first spanning forest

R. E. Tarjan, *Depth-first search and linear graph algorithms*, SIAM J. Comput. 1(2) (1972)
146–160, §4. Number the vertices of a directed graph in the order a depth-first search reaches
them and let `F` be the spanning forest of tree arcs. Tarjan's linear-time strong-components
algorithm rests on three facts, proved here from the numbering properties of depth-first search
that his argument uses (`IsDFSNumbering`):

* Lemma 10 (`exists_commonAncestor_stronglyConnected`,
  `stronglyConnected_of_highest_commonAncestor`): two vertices of the same strongly connected
  component have a common ancestor in `F`, and their highest-numbered common ancestor lies in
  the same component;
* Corollary 11 (`stronglyConnected_of_treeAncestor_between`): the vertices of a component form a
  subtree of `F` (they are closed under tree paths), whose root is the first vertex of the
  component reached by the search (`treeAncestor_of_first`);
* Lemma 12 (`isFirstInComponent_iff_lowlinkEqSelf`): a vertex `v` is the root of its component
  if and only if `LOWLINK(v) = v`, where `LOWLINK(v)` is the smallest-numbered vertex in the
  component of `v` reachable from `v` by zero or more tree arcs followed by at most one other
  edge.

**Numbering properties** (`IsDFSNumbering`). With `num` the discovery number and `Anc u v` the
relation "`u` is an ancestor of `v` in the forest" (reflexive): tree arcs are graph edges;
ancestors are numbered no later than their descendants; the descendants of `u` are numbered
consecutively from `u` on (if `Anc u x` and `num u ≤ num y ≤ num x` then `Anc u y`); and every
edge `(x, y)` goes to a descendant of `x` or to a vertex numbered before `x` (Tarjan §4: fronds
go to ancestors and "a cross-link `(v, w)` always has `NUMBER(v) > NUMBER(w)`"; the remaining
edges run from ancestors to descendants). The repository's depth-first search satisfies them:
two properties are proved below, the other two, by an invariant of the search machine, in
`CSLibExt.Algorithms.Lean.Graph.DepthFirstSearchNumbering`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.StronglyConnectedLowlink

open DepthFirstSearch StronglyConnectedComponents

variable {V : Type u}

/-- **Ancestor in a depth-first spanning forest.** `TreeAncestor parents a d` holds when `d` is
reached from `a` by zero or more tree arcs, the tree arcs being the `(child, parent)` pairs of
`parents` (Tarjan's relation `a →* d`). -/
def TreeAncestor (parents : List (V × V)) (a d : V) : Prop :=
  Relation.ReflTransGen (fun p c => ParentRel parents c p) a d

/-- **Numbering properties of depth-first search.** For a graph `adj`, tree arcs `parents` and a
numbering `num` of the vertices: tree arcs are graph edges; ancestors are numbered no later than
their descendants; the descendants of a vertex are numbered consecutively from it; and every edge
leads to a descendant of its tail or to a vertex numbered before its tail (Tarjan, *Depth-first
search and linear graph algorithms*, SIAM J. Comput. 1(2) (1972), §2 and §4). -/
structure IsDFSNumbering (adj : DirectedAdjacency V) (parents : List (V × V)) (num : V → ℕ) :
    Prop where
  parent_edge : ∀ c p, ParentRel parents c p → adj.Edge p c
  num_le_of_treeAncestor : ∀ a d, TreeAncestor parents a d → num a ≤ num d
  treeAncestor_of_between : ∀ a d x, TreeAncestor parents a d → num a ≤ num x →
    num x ≤ num d → TreeAncestor parents a x
  edge_cases : ∀ x y, adj.Edge x y → TreeAncestor parents x y ∨ num y < num x

/-- **First vertex of a strongly connected component.** `v` has the smallest number in its
strongly connected component; by Corollary 11 of Tarjan (1972) this is the root of the subtree
that the component forms in the depth-first spanning forest. -/
def IsFirstInComponent (adj : DirectedAdjacency V) (num : V → ℕ) (v : V) : Prop :=
  ∀ w, StronglyConnected adj v w → num v ≤ num w

/-- **`LOWLINK(v) = v`.** No vertex `w` in the strongly connected component of `v` that is
reached from `v` by zero or more tree arcs followed by one edge has a smaller number than `v`.
Since `v` itself is a candidate, this says that Tarjan's `LOWLINK(v)`, the smallest-numbered such
vertex, is `v` (Tarjan, *Depth-first search and linear graph algorithms*, SIAM J. Comput. 1(2)
(1972), §4; including tree arcs and ancestor-to-descendant edges among the final edges does not
change the minimum, as they lead to descendants of `v`). -/
def LowlinkEqSelf (adj : DirectedAdjacency V) (parents : List (V × V)) (num : V → ℕ) (v : V) :
    Prop :=
  ∀ d w, TreeAncestor parents v d → adj.Edge d w → StronglyConnected adj v w → num v ≤ num w

section

variable {adj : DirectedAdjacency V} {parents : List (V × V)} {num : V → ℕ}

theorem treeAncestor_edge_reachable (h : IsDFSNumbering adj parents num) {a d : V}
    (had : TreeAncestor parents a d) : adj.Reachable a d := by
  induction had with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail (h.parent_edge _ _ hbc)

/-- **Strongly connected components are closed under tree paths.** If `a` is an ancestor of
`b`, `b` an ancestor of `d`, and `a`, `d` lie in the same strongly connected component, then so
does `b`; hence the vertices of a component form a subtree of the depth-first spanning forest
(Tarjan, *Depth-first search and linear graph algorithms*, SIAM J. Comput. 1(2) (1972), §4,
Corollary 11). -/
theorem stronglyConnected_of_treeAncestor_between (h : IsDFSNumbering adj parents num)
    {a b d : V} (hab : TreeAncestor parents a b) (hbd : TreeAncestor parents b d)
    (had : StronglyConnected adj a d) : StronglyConnected adj b d :=
  ⟨treeAncestor_edge_reachable h hbd,
    had.2.trans (treeAncestor_edge_reachable h hab)⟩

/-- The first vertex of a component reaches every vertex reachable from it and reaching it by a
path of descendants. -/
private theorem treeAncestor_of_min (h : IsDFSNumbering adj parents num) {u : V}
    (hmin : ∀ x, StronglyConnected adj u x → num u ≤ num x) :
    ∀ y, adj.Reachable u y → adj.Reachable y u → TreeAncestor parents u y := by
  intro y huy
  induction huy with
  | refl => intro _; exact .refl
  | @tail b c hub hbc ih =>
      intro hcu
      have hbu : adj.Reachable b u := Relation.ReflTransGen.head hbc hcu
      have hanc := ih hbu
      rcases h.edge_cases b c hbc with hbc' | hlt
      · exact hanc.trans hbc'
      · have hsc : StronglyConnected adj u c := ⟨hub.tail hbc, hcu⟩
        exact h.treeAncestor_of_between u b c hanc (hmin c hsc)
          (le_of_lt hlt |>.trans (h.num_le_of_treeAncestor _ _ .refl))

/-- **The first vertex of a component is an ancestor of all of it.** If `u` has the smallest
number in its strongly connected component, every vertex of the component is a descendant of
`u` in the depth-first spanning forest: `u` is the root of the subtree formed by the component
(Tarjan, *Depth-first search and linear graph algorithms*, SIAM J. Comput. 1(2) (1972), §4,
Corollary 11). -/
theorem treeAncestor_of_first (h : IsDFSNumbering adj parents num) {u x : V}
    (hu : IsFirstInComponent adj num u) (hux : StronglyConnected adj u x) :
    TreeAncestor parents u x :=
  treeAncestor_of_min h hu x hux.1 hux.2

private theorem exists_first (v : V) :
    ∃ u, StronglyConnected adj v u ∧ IsFirstInComponent adj num u := by
  classical
  have hex : ∃ k, ∃ x, StronglyConnected adj v x ∧ num x = k := ⟨num v, v, ⟨.refl, .refl⟩, rfl⟩
  obtain ⟨u, hvu, hu⟩ := Nat.find_spec hex
  refine ⟨u, hvu, fun w huw => ?_⟩
  rw [hu]
  exact Nat.find_min' hex ⟨w, hvu.trans huw, rfl⟩

/-- **Common ancestor of strongly connected vertices.** Two vertices in the same strongly
connected component have a common ancestor in the depth-first spanning forest that lies in the
same component (Tarjan, *Depth-first search and linear graph algorithms*, SIAM J. Comput. 1(2)
(1972), §4, Lemma 10, first part). -/
theorem exists_commonAncestor_stronglyConnected (h : IsDFSNumbering adj parents num) {v w : V}
    (hvw : StronglyConnected adj v w) :
    ∃ u, TreeAncestor parents u v ∧ TreeAncestor parents u w ∧ StronglyConnected adj u v := by
  obtain ⟨u, hvu, hu⟩ := exists_first (adj := adj) (num := num) v
  exact ⟨u, treeAncestor_of_first h hu hvu.symm, treeAncestor_of_first h hu (hvu.symm.trans hvw),
    hvu.symm⟩

/-- **The highest-numbered common ancestor lies in the component.** If `v` and `w` are in the
same strongly connected component and `u` is a common ancestor of `v` and `w` in the depth-first
spanning forest whose number is at least that of every common ancestor, then `u` is in the
component of `v` and `w` (Tarjan, *Depth-first search and linear graph algorithms*, SIAM J.
Comput. 1(2) (1972), §4, Lemma 10). -/
theorem stronglyConnected_of_highest_commonAncestor (h : IsDFSNumbering adj parents num)
    {u v w : V} (hvw : StronglyConnected adj v w) (huv : TreeAncestor parents u v)
    (_huw : TreeAncestor parents u w)
    (hmax : ∀ u', TreeAncestor parents u' v → TreeAncestor parents u' w → num u' ≤ num u) :
    StronglyConnected adj u v := by
  obtain ⟨u₀, hu₀v, hu₀w, hsc⟩ := exists_commonAncestor_stronglyConnected h hvw
  have hle := hmax u₀ hu₀v hu₀w
  have hanc : TreeAncestor parents u₀ u :=
    h.treeAncestor_of_between u₀ v u hu₀v hle (h.num_le_of_treeAncestor u v huv)
  exact stronglyConnected_of_treeAncestor_between h hanc huv hsc

/-- Following a path from `v` to `u` either stays among the descendants of `v` or takes an edge
from a descendant of `v` to a vertex numbered before `v` from which `u` is still reachable. -/
private theorem descendant_or_exit (h : IsDFSNumbering adj parents num) {v u : V} :
    ∀ y, adj.Reachable v y → adj.Reachable y u →
      TreeAncestor parents v y ∨
        ∃ d w, TreeAncestor parents v d ∧ adj.Edge d w ∧ num w < num v ∧
          adj.Reachable v w ∧ adj.Reachable w u := by
  intro y hvy
  induction hvy with
  | refl => intro _; exact Or.inl .refl
  | @tail b c hvb hbc ih =>
      intro hcu
      rcases ih (Relation.ReflTransGen.head hbc hcu) with hanc | hexit
      · rcases h.edge_cases b c hbc with hbc' | hlt
        · exact Or.inl (hanc.trans hbc')
        · by_cases hvc : num v ≤ num c
          · exact Or.inl (h.treeAncestor_of_between v b c hanc hvc hlt.le)
          · exact Or.inr ⟨b, c, hanc, hbc, by omega, hvb.tail hbc, hcu⟩
      · exact Or.inr hexit

/-- **Tarjan's lowlink test for component roots.** A vertex `v` has the smallest number in its
strongly connected component, that is, `v` is the root of the subtree formed by its component in
the depth-first spanning forest, if and only if `LOWLINK(v) = v` (Tarjan, *Depth-first search and
linear graph algorithms*, SIAM J. Comput. 1(2) (1972), §4, Lemma 12). -/
theorem isFirstInComponent_iff_lowlinkEqSelf (h : IsDFSNumbering adj parents num) (v : V) :
    IsFirstInComponent adj num v ↔ LowlinkEqSelf adj parents num v := by
  constructor
  · intro hv d w _ _ hvw
    exact hv w hvw
  · intro hlow x hvx
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨u, hvu, hu⟩ := exists_first (adj := adj) (num := num) v
    have hux : num u ≤ num x := hu x (hvu.symm.trans hvx)
    have huv : num u < num v := by omega
    rcases descendant_or_exit h u hvu.1 .refl with hanc | ⟨d, w, hvd, hdw, hwv, hvw, hwu⟩
    · have := h.num_le_of_treeAncestor v u hanc
      omega
    · have hsc : StronglyConnected adj v w := ⟨hvw, hwu.trans hvu.2⟩
      have := hlow d w hvd hdw hsc
      omega

end

section DepthFirstSearch

variable [BEq V] [Hashable V] [LawfulBEq V]

omit [Hashable V] in
theorem idxOf_lt_of_before {x y : V} {xs : List V} (h : Before x y xs) (hnd : xs.Nodup) :
    xs.idxOf x < xs.idxOf y := by
  obtain ⟨a, b, c, rfl⟩ := h
  have hnd' : (a ++ x :: (b ++ y :: c)).Nodup := by simpa using hnd
  rw [List.nodup_append] at hnd'
  obtain ⟨_, hxbc, hdisj⟩ := hnd'
  have hxa : x ∉ a := fun hx => hdisj x hx x (by simp) rfl
  have hya : y ∉ a := fun hy => hdisj y hy y (by simp) rfl
  rw [List.nodup_cons] at hxbc
  have hyx : y ≠ x := fun hyx => hxbc.1 (by simp [hyx])
  have hrw : a ++ x :: b ++ y :: c = a ++ (x :: (b ++ y :: c)) := by simp
  rw [hrw, List.idxOf_append, List.idxOf_append, ite_eq_right hxa, ite_eq_right hya,
    List.idxOf_cons_self, List.idxOf_cons_ne _ (Ne.symm hyx)]
  omega

/-- **Tree arcs of the repository's depth-first search are graph edges.** In the whole-graph
traversal `dfsAll adj`, every recorded `(child, parent)` pair is an edge from parent to child. -/
theorem dfsAll_parent_edge (adj : DirectedAdjacency V) (c p : V)
    (h : ParentRel (dfsAll adj).parents c p) : adj.Edge p c :=
  DepthFirstSearch.parent_edge adj adj.vertices c p h

/-- **Ancestors are discovered first in the repository's depth-first search.** In the
whole-graph traversal `dfsAll adj`, an ancestor's preorder index is at most its descendant's
(Tarjan, *Depth-first search and linear graph algorithms*, SIAM J. Comput. 1(2) (1972), §3:
"If `u` is an ancestor of `v` in the spanning tree `T` of `P`, then `u < v`", vertices being
identified with their numbers). -/
theorem dfsAll_num_le_of_treeAncestor (adj : DirectedAdjacency V) (a d : V)
    (h : TreeAncestor (dfsAll adj).parents a d) :
    (dfsAll adj).preorder.idxOf a ≤ (dfsAll adj).preorder.idxOf d := by
  induction h with
  | refl => exact le_rfl
  | @tail b c _ hbc ih =>
      have hb := DepthFirstSearch.parent_before_child adj adj.vertices c b hbc
      exact ih.trans (idxOf_lt_of_before hb (DepthFirstSearch.preorder_nodup adj adj.vertices)).le

end DepthFirstSearch

end Cslib.Algorithms.Lean.StronglyConnectedLowlink
