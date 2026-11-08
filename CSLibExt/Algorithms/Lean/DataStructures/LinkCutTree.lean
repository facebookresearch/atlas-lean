/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Nodup
public import CSLibExt.Algorithms.Lean.DataStructures.EulerTourTree

/-!
# Link-cut trees (functional, specification-level model)

A link-cut tree (Sleator-Tarjan) maintains a forest of rooted trees (the
represented forest) as a disjoint union of preferred paths, each stored in
an auxiliary splay tree keyed by depth in the imperative structure. This
module does not model the auxiliary splay trees. It models only the
represented forest and its preferred-path decomposition, functionally and
at the level of specifications:

* the represented forest is a list of `EulerTourTree.Tree`s;
* the preferred-path decomposition is a list of paths `paths s`, computed
  from the state: the state stores the preferred (solid) edges `s.preferred`,
  each directed from a node to its preferred child (`ParentChild`), and
  `paths s` is the maximal solid chains in each represented tree
  (`treePaths`, built from `decomp`), with vertices incident to no solid edge
  forming singleton paths. This is the usual Sleator-Tarjan preferred-path
  decomposition: `mem_paths_flatMap` and `nodup_paths_flatMap` record that
  it partitions the vertex set of the forest, `pairwise_disjoint_paths` that
  distinct paths are vertex-disjoint, and `isChain_of_mem_paths` that
  consecutive vertices of every path are joined by a represented edge;
* `access x` makes the path from the represented root to `x` (`rootPath`)
  solid: its edges become preferred, the previously preferred edge of each
  vertex on the path is dropped, and every preferred edge whose parent
  endpoint lies off the path is retained (`mem_preferred_access`). Off-path
  preferred paths therefore persist across accesses: in the tree with root
  `1`, children `2 → 4` and `3 → 5`, `access 5` after `access 4` keeps the
  preferred path `[2, 4]` (only the edge `1`-`2` is dropped, replaced by
  `1`-`3`), a regression test in `LinkCutTreeTests`. After `access x`, the
  root-to-`x` path is one of the paths of the decomposition and `x` is its
  last (deepest) vertex, recorded by `access_last`;
* the structural operations preserve represented adjacency: `link x y`
  reroots the tree of `x` at `x` and grafts it as a new child subtree of
  `y` (`rerootAt` then `graftAt`, adding exactly the endpoint edge
  `x`-`y`; a no-op when already connected), `makeRoot x` reroots the tree
  containing `x` at `x` by reversing the edges on the old root-to-`x`
  path (`rerootAt`, every undirected edge kept), `cut x` detaches the
  subtree rooted at `x` and prunes it from the remainder (`pruneAt`,
  every remaining edge kept), and `cutEdge x y` removes the undirected
  edge `x`-`y` by the textbook composite `cut y` after `makeRoot x`,
  guarded by a computable adjacency test (`adjacentB`): on a
  non-adjacent pair it leaves the forest unchanged
  (`cutEdge_eq_of_not_adjacent`). Structural operations reset
  `preferred` to `[]` (all edges dashed).

The abstractions proved here are forest connectivity and the undirected
edge relation: `Connected s x y` is reachability in one represented tree,
equivalently co-occurrence in one Euler tour (`connected_iff_tour`), and
`Adjacent a b t` is parent-child adjacency in a represented tree, with
`adjacent_graftAt` (grafting adds exactly one edge),
`adjacent_rerootAt` (rerooting a duplicate-free tree keeps every edge),
and `adjacent_pruneAt_of_mem_mem` (pruning keeps every edge whose
endpoints survive) specifying the surgeries at the level of edges. The
main theorems are
`connected_link` (a link connects its endpoints), `not_connected_cut` (a cut
separates the detached subtree from the rest of its tree),
`not_connected_cutEdge` and `adjacent_cutEdge` (an edge cut on an
adjacent pair in a valid state separates exactly that pair and retains
every other edge), `access_last`
(`access x` makes `x` the last, deepest vertex of its preferred path),
`makeRoot_root` (`makeRoot x` installs a tree rooted at `x`),
`access_forest`/`connected_access_iff` (`access` changes only preferred
paths), and the invariant-preservation theorems `Valid.access`,
`Valid.makeRoot`, `Valid.link`, `Valid.cut`, and `Valid.cutEdge`.

## What is not modeled

This is not the imperative link-cut tree. Concretely, out of scope here:

* the auxiliary splay trees themselves: no splay-tree shape, root, or
  splaying operation is modeled here. The textbook `expose` operation
  (`access` plus a splay of the auxiliary tree) is therefore not
  modeled either; this module provides `access` (the preferred-path
  update) only. A preferred path is represented solely as its vertex
  list ordered from shallowest to deepest, with no auxiliary-tree
  correctness claim;
* path aggregates and subtree queries;
* a full edge-level specification of `pruneAt`/`cut` as an adjacency
  equivalence: grafting and rerooting are specified at edge level for
  arbitrary vertex pairs (`adjacent_graftAt`, `adjacent_rerootAt`), and
  pruning is specified by edge retention on the surviving vertices
  (`adjacent_pruneAt_of_mem_mem`, with the vertex-set characterizations
  `mem_vertices_pruneAt`, `mem_vertices_pruneAt_of_mem_not_mem`,
  `perm_vertices_pruneAt`); that every edge of the pruned remainder was
  already an edge of the original tree, and a state-level adjacency
  equivalence for the rooted `cut` (as opposed to `cutEdge`, covered by
  `adjacent_cutEdge`), are not proved. The separation/connectivity
  theorems apply as before, together with exact-forest
  composition tests on branched trees in `LinkCutTreeTests` (for example
  linking `1` with children `2`, `3` under an isolated `4` and then
  cutting `2` leaves `{4, 1, 3}` and `{2}` with the original branch
  intact, and `cutEdge 1 2` on the branched tree leaves `{1, 3}` and
  `{2}`);
* all amortized bounds, including the `O(log n)` access lemma.

## Dependency

The represented forest is built from the `EulerTourTree.Tree` API in
`EulerTourTree.lean` (landed separately); this module only consumes
`Tree.vertices`, `Tree.tour`, and the tree structure from it.
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean

namespace LinkCutTree

open EulerTourTree

variable {V : Type u} [DecidableEq V]

omit [DecidableEq V] in
private theorem getLast?_cons_of_getLast?_eq_some {r x : V} {p : List V}
    (h : p.getLast? = some x) : (r :: p).getLast? = some x := by
  cases p with
  | nil => simp at h
  | cons a p => exact h

omit [DecidableEq V] in
private theorem root_mem_vertices (t : Tree V) : t.root ∈ Tree.vertices t := by
  cases t with
  | node r cs => simp [Tree.vertices_node]

omit [DecidableEq V] in
private theorem mem_vertices_node {v r : V} {cs : List (Tree V)} :
    v ∈ Tree.vertices (.node r cs) ↔ v = r ∨ ∃ c ∈ cs, v ∈ Tree.vertices c := by
  simp [Tree.vertices_node, List.mem_flatMap]

omit [DecidableEq V] in
private theorem disjoint_vertices_of_nodup_flatMap :
    ∀ {f : List (Tree V)}, (f.flatMap Tree.vertices).Nodup →
      ∀ {a b : Tree V}, a ∈ f → b ∈ f → a ≠ b →
        List.Disjoint (Tree.vertices a) (Tree.vertices b) := by
  intro f hnodup a b ha hb hab
  obtain ⟨-, hpair⟩ := List.nodup_flatMap.mp hnodup
  have haux : ∀ (ds : List (Tree V)),
      List.Pairwise (Function.onFun List.Disjoint Tree.vertices) ds →
      ∀ {a b : Tree V}, a ∈ ds → b ∈ ds → a ≠ b →
        List.Disjoint (Tree.vertices a) (Tree.vertices b) := by
    intro ds
    induction ds with
    | nil =>
        intro _ a b ha _ _
        exact absurd ha (by simp)
    | cons d ds ihd =>
        intro hpair' a b ha hb hab
        obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair'
        rw [List.mem_cons] at ha hb
        rcases ha with rfl | ha
        · rcases hb with rfl | hb
          · exact absurd rfl hab
          · exact hhead b hb
        · rcases hb with rfl | hb
          · intro y hya hyb
            exact hhead a ha hyb hya
          · exact ihd htail ha hb hab
  exact haux f hpair ha hb hab

omit [DecidableEq V] in
private theorem eq_of_mem_vertices_of_nodup_flatMap :
    ∀ {f : List (Tree V)}, (f.flatMap Tree.vertices).Nodup →
      ∀ {a b : Tree V} {v : V}, a ∈ f → b ∈ f → v ∈ Tree.vertices a →
        v ∈ Tree.vertices b → a = b := by
  intro f hnodup a b v ha hb hva hvb
  by_contra hab
  exact disjoint_vertices_of_nodup_flatMap hnodup ha hb hab hva hvb

omit [DecidableEq V] in
private theorem root_not_mem_flatMap_children {r : V} {cs : List (Tree V)}
    (hnodup : (Tree.vertices (.node r cs)).Nodup) :
    r ∉ cs.flatMap Tree.vertices := by
  rw [Tree.vertices_node, List.nodup_cons] at hnodup
  exact hnodup.1

omit [DecidableEq V] in
private theorem vertices_ne_nil (t : Tree V) : Tree.vertices t ≠ [] := by
  intro h
  have hmem := root_mem_vertices t
  rw [h] at hmem
  exact (List.not_mem_nil hmem).elim

/-- The chain `r → c₁ → c₂ → ⋯` as a rooted tree: each vertex has the next as
its only child. A convenience constructor for building represented trees
from vertex lists; the structural operations do not use it (they perform
adjacency-preserving surgery instead). -/
public def spine : V → List V → Tree V
  | r, [] => .node r []
  | r, c :: cs => .node r [spine c cs]

omit [DecidableEq V] in
public theorem vertices_spine : ∀ (r : V) (xs : List V),
    Tree.vertices (spine r xs) = r :: xs := by
  intro r xs
  induction xs generalizing r with
  | nil => simp [spine, Tree.vertices_node]
  | cons c cs ih => simp [spine, Tree.vertices_node, ih]

omit [DecidableEq V] in
public theorem root_spine (r : V) (xs : List V) : (spine r xs).root = r := by
  cases xs with
  | nil => rfl
  | cons c cs => rfl

/-- The spine over a vertex list, as a one-element forest, or the empty forest
for the empty list. -/
public def ofVertexList : List V → List (Tree V)
  | [] => []
  | r :: rs => [spine r rs]

omit [DecidableEq V] in
public theorem vertices_of_mem_ofVertexList {t : Tree V} {l : List V}
    (h : t ∈ ofVertexList l) : Tree.vertices t = l := by
  cases l with
  | nil => exact absurd h (by simp [ofVertexList])
  | cons r rs =>
      have hmem : t ∈ [spine r rs] := h
      rw [List.mem_singleton] at hmem
      rw [hmem, vertices_spine]

omit [DecidableEq V] in
public theorem exists_mem_ofVertexList {l : List V} (hl : l ≠ []) :
    ∃ t ∈ ofVertexList l, Tree.vertices t = l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons r rs => exact ⟨spine r rs, by simp [ofVertexList], vertices_spine r rs⟩

/-- The first tree of a forest whose vertices contain `x`, if any. -/
public def findTree (x : V) : List (Tree V) → Option (Tree V)
  | [] => none
  | t :: ts => if x ∈ Tree.vertices t then some t else findTree x ts

public theorem findTree_eq_some_spec {x : V} :
    ∀ {f : List (Tree V)} {t : Tree V}, findTree x f = some t →
      t ∈ f ∧ x ∈ Tree.vertices t := by
  intro f
  induction f with
  | nil => intro t h; simp [findTree] at h
  | cons s ts ih =>
      intro t h
      by_cases hs : x ∈ Tree.vertices s
      · have heq : findTree x (s :: ts) = some s := by simp [findTree, hs]
        rw [heq] at h
        have hst : s = t := Option.some.inj h
        subst hst
        exact ⟨by simp, hs⟩
      · have heq : findTree x (s :: ts) = findTree x ts := by simp [findTree, hs]
        rw [heq] at h
        obtain ⟨hmem, hx⟩ := ih h
        exact ⟨List.mem_cons_of_mem s hmem, hx⟩

public theorem findTree_eq_some_of_exists {x : V} :
    ∀ {f : List (Tree V)}, (∃ t ∈ f, x ∈ Tree.vertices t) →
      ∃ t, findTree x f = some t ∧ t ∈ f ∧ x ∈ Tree.vertices t := by
  intro f
  induction f with
  | nil =>
      intro h
      obtain ⟨t, hmem, -⟩ := h
      exact absurd hmem (by simp)
  | cons s ts ih =>
      intro h
      by_cases hs : x ∈ Tree.vertices s
      · exact ⟨s, by simp [findTree, hs], by simp, hs⟩
      · obtain ⟨t, hmem, hx⟩ := h
        have htail : ∃ t ∈ ts, x ∈ Tree.vertices t := by
          rw [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact absurd hx hs
          · exact ⟨t, hmem, hx⟩
        obtain ⟨t', hfind, hmem', hx'⟩ := ih htail
        exact ⟨t', by simp [findTree, hs, hfind], List.mem_cons_of_mem s hmem', hx'⟩

/-- The forest obtained by removing every tree whose vertices contain `x`. -/
public def removeTree (x : V) : List (Tree V) → List (Tree V)
  | [] => []
  | t :: ts => if x ∈ Tree.vertices t then removeTree x ts else t :: removeTree x ts

public theorem mem_removeTree {x : V} :
    ∀ {f : List (Tree V)} {t : Tree V},
      t ∈ removeTree x f ↔ t ∈ f ∧ x ∉ Tree.vertices t := by
  intro f
  induction f with
  | nil => intro t; simp [removeTree]
  | cons s ts ih =>
      intro t
      by_cases hs : x ∈ Tree.vertices s
      · have heq : removeTree x (s :: ts) = removeTree x ts := by simp [removeTree, hs]
        rw [heq, ih]
        constructor
        · intro h
          exact ⟨List.mem_cons_of_mem s h.1, h.2⟩
        · intro h
          obtain ⟨hmem, hx⟩ := h
          rw [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact absurd hs hx
          · exact ⟨hmem, hx⟩
      · have heq : removeTree x (s :: ts) = s :: removeTree x ts := by simp [removeTree, hs]
        rw [heq, List.mem_cons, ih, List.mem_cons]
        constructor
        · rintro (rfl | ⟨hmem, hx⟩)
          · exact ⟨Or.inl rfl, hs⟩
          · exact ⟨Or.inr hmem, hx⟩
        · rintro ⟨rfl | hmem, hx⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hmem, hx⟩

public theorem removeTree_eq_self_of_forall_not_mem {x : V} :
    ∀ {f : List (Tree V)}, (∀ t ∈ f, x ∉ Tree.vertices t) →
      removeTree x f = f := by
  intro f
  induction f with
  | nil => intro _; rfl
  | cons t f ih =>
      intro h
      have ht : x ∉ Tree.vertices t := h t List.mem_cons_self
      have hrest : removeTree x f = f :=
        ih (fun s hs => h s (List.mem_cons_of_mem t hs))
      simp [removeTree, ht, hrest]

/-- Removing the (unique, by duplicate-freeness) tree containing `x` from a
forest splits its flat vertex list into the remainder plus that tree, up
to permutation. -/
public theorem perm_flatMap_removeTree {x : V} :
    ∀ {f : List (Tree V)} {t : Tree V},
      (f.flatMap Tree.vertices).Nodup → findTree x f = some t →
      ((removeTree x f).flatMap Tree.vertices ++ Tree.vertices t).Perm
        (f.flatMap Tree.vertices) := by
  intro f
  induction f with
  | nil =>
      intro t _ h
      simp [findTree] at h
  | cons a f ih =>
      intro t hnodup h
      by_cases ha : x ∈ Tree.vertices a
      · have hfindA : findTree x (a :: f) = some a := by simp [findTree, ha]
        rw [hfindA] at h
        have hst : a = t := Option.some.inj h
        subst hst
        have hnotF : ∀ s ∈ f, x ∉ Tree.vertices s := by
          intro s hs hxs
          have hflat : ((a :: f).flatMap Tree.vertices) =
              Tree.vertices a ++ f.flatMap Tree.vertices :=
            List.flatMap_cons ..
          rw [hflat] at hnodup
          obtain ⟨-, -, hcross⟩ := List.pairwise_append.mp hnodup
          exact hcross x ha x (List.mem_flatMap.mpr ⟨s, hs, hxs⟩) rfl
        have hrem : removeTree x (a :: f) = f := by
          have h1 : removeTree x (a :: f) = removeTree x f := by
            simp [removeTree, ha]
          rw [h1, removeTree_eq_self_of_forall_not_mem hnotF]
        rw [hrem]
        simp only [List.flatMap_cons]
        exact List.perm_append_comm
      · have hfindEq : findTree x (a :: f) = findTree x f := by
          simp [findTree, ha]
        rw [hfindEq] at h
        have hremEq : removeTree x (a :: f) = a :: removeTree x f := by
          simp [removeTree, ha]
        have hnodupF : (f.flatMap Tree.vertices).Nodup := by
          have hflat : ((a :: f).flatMap Tree.vertices) =
              Tree.vertices a ++ f.flatMap Tree.vertices :=
            List.flatMap_cons ..
          rw [hflat] at hnodup
          exact (List.pairwise_append.mp hnodup).2.1
        have hrest := ih hnodupF h
        rw [hremEq]
        simp only [List.flatMap_cons]
        exact (List.Perm.of_eq (List.append_assoc _ _ _)).trans
          (hrest.append_left _)


/-- The subtree rooted at `x`, if `x` occurs in the tree: the first such
subtree in preorder. -/
public def findSubtree (x : V) : Tree V → Option (Tree V)
  | .node r cs => if r = x then some (.node r cs) else findSubtreeList x cs
where
  findSubtreeList (x : V) : List (Tree V) → Option (Tree V)
    | [] => none
    | c :: cs =>
        match findSubtree x c with
        | some s => some s
        | none => findSubtreeList x cs

private theorem findSubtreeList_eq_some_spec {x : V} :
    ∀ {cs : List (Tree V)} {s : Tree V},
      findSubtree.findSubtreeList x cs = some s →
      ∃ c ∈ cs, findSubtree x c = some s := by
  intro cs
  induction cs with
  | nil => intro s h; simp [findSubtree.findSubtreeList] at h
  | cons c cs ih =>
      intro s h
      cases hc : findSubtree x c with
      | some s' =>
          have heq : findSubtree.findSubtreeList x (c :: cs) = some s' := by
            simp [findSubtree.findSubtreeList, hc]
          rw [heq] at h
          have hss : s' = s := Option.some.inj h
          exact ⟨c, by simp, by rw [hc, hss]⟩
      | none =>
          have heq : findSubtree.findSubtreeList x (c :: cs) =
              findSubtree.findSubtreeList x cs := by
            simp [findSubtree.findSubtreeList, hc]
          rw [heq] at h
          obtain ⟨c', hc', hfind⟩ := ih h
          exact ⟨c', List.mem_cons_of_mem c hc', hfind⟩

private theorem findSubtreeList_eq_some_of_exists {x : V} :
    ∀ {cs : List (Tree V)} {s : Tree V},
      (∃ c ∈ cs, findSubtree x c = some s) →
      findSubtree.findSubtreeList x cs = some s ∨
        ∃ s', findSubtree.findSubtreeList x cs = some s' := by
  intro cs
  induction cs with
  | nil =>
      intro s h
      obtain ⟨c, hmem, -⟩ := h
      exact absurd hmem (by simp)
  | cons c cs ih =>
      intro s h
      cases hc : findSubtree x c with
      | some s' =>
          exact Or.inr ⟨s', by simp [findSubtree.findSubtreeList, hc]⟩
      | none =>
          obtain ⟨c', hmem, hfind⟩ := h
          have htail : ∃ c ∈ cs, findSubtree x c = some s := by
            rw [List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · rw [hc] at hfind
              cases hfind
            · exact ⟨c', hmem, hfind⟩
          have heq : findSubtree.findSubtreeList x (c :: cs) =
              findSubtree.findSubtreeList x cs := by
            simp [findSubtree.findSubtreeList, hc]
          rw [heq]
          exact ih htail

public theorem root_findSubtree {x : V} {t s : Tree V} (h : findSubtree x t = some s) :
    s.root = x := by
  revert h
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro h
      by_cases hr : r = x
      · have heq : findSubtree x (.node r cs) = some (.node r cs) := by
          simp [findSubtree, hr]
        rw [heq] at h
        have hst : (Tree.node r cs : Tree V) = s := Option.some.inj h
        rw [← hst]
        simp [hr]
      · have heq : findSubtree x (.node r cs) = findSubtree.findSubtreeList x cs := by
          simp [findSubtree, hr]
        rw [heq] at h
        obtain ⟨c, hc, hfind⟩ := findSubtreeList_eq_some_spec h
        exact ih c hc hfind

public theorem mem_vertices_findSubtree {x v : V} {t s : Tree V}
    (h : findSubtree x t = some s) (hv : v ∈ Tree.vertices s) : v ∈ Tree.vertices t := by
  revert h hv
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro h hv
      by_cases hr : r = x
      · have heq : findSubtree x (.node r cs) = some (.node r cs) := by
          simp [findSubtree, hr]
        rw [heq] at h
        have hst : (Tree.node r cs : Tree V) = s := Option.some.inj h
        rw [← hst] at hv
        exact hv
      · have heq : findSubtree x (.node r cs) = findSubtree.findSubtreeList x cs := by
          simp [findSubtree, hr]
        rw [heq] at h
        obtain ⟨c, hc, hfind⟩ := findSubtreeList_eq_some_spec h
        have hvc := ih c hc hfind hv
        exact mem_vertices_node.mpr (Or.inr ⟨c, hc, hvc⟩)

public theorem findSubtree_eq_some_of_mem {x : V} {t : Tree V}
    (hx : x ∈ Tree.vertices t) : ∃ s, findSubtree x t = some s := by
  revert hx
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro hx
      by_cases hr : r = x
      · exact ⟨.node r cs, by simp [findSubtree, hr]⟩
      · have hchild : ∃ c ∈ cs, ∃ s, findSubtree x c = some s := by
          rw [mem_vertices_node] at hx
          rcases hx with hx | ⟨c, hc, hxc⟩
          · exact absurd hx.symm hr
          · obtain ⟨s, hs⟩ := ih c hc hxc
            exact ⟨c, hc, s, hs⟩
        obtain ⟨s, hs⟩ : ∃ s, findSubtree.findSubtreeList x cs = some s := by
          obtain ⟨c, hc, s, hs⟩ := hchild
          rcases findSubtreeList_eq_some_of_exists ⟨c, hc, hs⟩ with h | ⟨s', h'⟩
          · exact ⟨s, h⟩
          · exact ⟨s', h'⟩
        exact ⟨s, by simp [findSubtree, hr, hs]⟩

public theorem findSubtree_eq_none_of_not_mem {x : V} {t : Tree V}
    (hx : x ∉ Tree.vertices t) : findSubtree x t = none := by
  cases h : findSubtree x t with
  | none => rfl
  | some s =>
      exfalso
      have hroot : s.root = x := root_findSubtree h
      have hxmem : x ∈ Tree.vertices s := by
        rw [← hroot]
        exact root_mem_vertices s
      exact hx (mem_vertices_findSubtree h hxmem)

private theorem root_not_mem_vertices_findSubtree {y : V} {t sub : Tree V}
    (hnodup : (Tree.vertices t).Nodup) (h : findSubtree y t = some sub)
    (hy : y ≠ t.root) : t.root ∉ Tree.vertices sub := by
  cases t with
  | node r cs =>
      have hr : r ≠ y := fun hreq => hy hreq.symm
      have heq : findSubtree y (.node r cs) =
          findSubtree.findSubtreeList y cs := by simp [findSubtree, hr]
      rw [heq] at h
      obtain ⟨c, hc, hfind⟩ := findSubtreeList_eq_some_spec h
      intro hmem
      have hrc : r ∈ Tree.vertices c := mem_vertices_findSubtree hfind hmem
      have hflat : r ∈ cs.flatMap Tree.vertices :=
        List.mem_flatMap.mpr ⟨c, hc, hrc⟩
      exact root_not_mem_flatMap_children hnodup hflat

private theorem findSubtreeList_eq_some_of_unique {y : V} {c₀ s : Tree V} :
    ∀ {ds : List (Tree V)}, c₀ ∈ ds → findSubtree y c₀ = some s →
      (∀ c ∈ ds, c ≠ c₀ → findSubtree y c = none) →
      findSubtree.findSubtreeList y ds = some s := by
  intro ds
  induction ds with
  | nil =>
      intro hmem _ _
      exact absurd hmem (by simp)
  | cons d ds ih =>
      intro hmem hfind hnone
      rw [List.mem_cons] at hmem
      by_cases hd : d = c₀
      · subst hd
        simp [findSubtree.findSubtreeList, hfind]
      · have hdn : findSubtree y d = none :=
          hnone d List.mem_cons_self hd
        have hc₀ : c₀ ∈ ds := by
          rcases hmem with h | h
          · exact absurd h.symm hd
          · exact h
        have hrest : findSubtree.findSubtreeList y ds = some s :=
          ih hc₀ hfind (fun c hc => hnone c (List.mem_cons_of_mem d hc))
        simp [findSubtree.findSubtreeList, hdn, hrest]

private theorem findSubtree_eq_child_of_root_eq {y r : V}
    {cs : List (Tree V)} {c₀ : Tree V}
    (hnodup : (Tree.vertices (.node r cs)).Nodup) (hc₀ : c₀ ∈ cs)
    (hroot : c₀.root = y) (hr : r ≠ y) :
    findSubtree y (.node r cs) = some c₀ := by
  have hfind₀ : findSubtree y c₀ = some c₀ := by
    cases c₀ with
    | node r₀ cs₀ =>
        have hr₀ : r₀ = y := hroot
        simp [findSubtree, hr₀]
  have hflat : (cs.flatMap Tree.vertices).Nodup := by
    rw [Tree.vertices_node, List.nodup_cons] at hnodup
    exact hnodup.2
  have hy₀ : y ∈ Tree.vertices c₀ := by
    rw [← hroot]
    exact root_mem_vertices c₀
  have hnone : ∀ c ∈ cs, c ≠ c₀ → findSubtree y c = none := by
    intro c hc hne
    apply findSubtree_eq_none_of_not_mem
    intro hyc
    exact hne (eq_of_mem_vertices_of_nodup_flatMap hflat hc hc₀ hyc hy₀)
  have heq : findSubtree y (.node r cs) =
      findSubtree.findSubtreeList y cs := by simp [findSubtree, hr]
  rw [heq]
  exact findSubtreeList_eq_some_of_unique hc₀ hfind₀ hnone

/-- Undirected adjacency in a represented tree: `a` and `b` are joined by a
parent-child edge (in either direction) somewhere in the tree. This is the
edge relation the structural operations preserve (`adjacent_graftAt`,
`adjacent_rerootAt`). -/
public def Adjacent (a b : V) : Tree V → Prop
  | .node r cs =>
      (r = a ∧ ∃ c ∈ cs, c.root = b) ∨ (r = b ∧ ∃ c ∈ cs, c.root = a) ∨
        AdjacentList a b cs
where
  /-- Adjacency inside one of a list of subtrees. -/
  AdjacentList (a b : V) : List (Tree V) → Prop
    | [] => False
    | c :: cs => Adjacent a b c ∨ AdjacentList a b cs

omit [DecidableEq V] in
public theorem adjacent_node {a b r : V} {cs : List (Tree V)} :
    Adjacent a b (.node r cs) ↔
      (r = a ∧ ∃ c ∈ cs, c.root = b) ∨ (r = b ∧ ∃ c ∈ cs, c.root = a) ∨
        Adjacent.AdjacentList a b cs :=
  Iff.rfl

omit [DecidableEq V] in
public theorem adjacentList_iff {a b : V} :
    ∀ {cs : List (Tree V)},
      Adjacent.AdjacentList a b cs ↔ ∃ c ∈ cs, Adjacent a b c := by
  intro cs
  induction cs with
  | nil => simp [Adjacent.AdjacentList]
  | cons c cs ih =>
      have hcons : Adjacent.AdjacentList a b (c :: cs) ↔
          Adjacent a b c ∨ Adjacent.AdjacentList a b cs := Iff.rfl
      rw [hcons, ih]
      constructor
      · rintro (h | ⟨d, hd, hadj⟩)
        · exact ⟨c, List.mem_cons_self, h⟩
        · exact ⟨d, List.mem_cons_of_mem c hd, hadj⟩
      · rintro ⟨d, hd, hadj⟩
        rw [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact Or.inl hadj
        · exact Or.inr ⟨d, hd, hadj⟩

omit [DecidableEq V] in
/-- The endpoints of an edge of a tree are vertices of the tree. -/
public theorem Adjacent.mem_left {a b : V} :
    ∀ {t : Tree V}, Adjacent a b t → a ∈ Tree.vertices t := by
  intro t
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro h
      rw [adjacent_node] at h
      rcases h with ⟨hr, -⟩ | ⟨hr, c, hc, hroot⟩ | h
      · exact mem_vertices_node.mpr (Or.inl hr.symm)
      · have ha : a ∈ Tree.vertices c := by
          rw [← hroot]
          exact root_mem_vertices c
        exact mem_vertices_node.mpr (Or.inr ⟨c, hc, ha⟩)
      · rw [adjacentList_iff] at h
        obtain ⟨c, hc, hadj⟩ := h
        exact mem_vertices_node.mpr (Or.inr ⟨c, hc, ih c hc hadj⟩)

omit [DecidableEq V] in
/-- Adjacency is symmetric. -/
public theorem Adjacent.symm {a b : V} :
    ∀ {t : Tree V}, Adjacent a b t → Adjacent b a t := by
  intro t
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro h
      rw [adjacent_node] at h ⊢
      rcases h with ⟨hr, hc⟩ | ⟨hr, hc⟩ | h
      · exact Or.inr (Or.inl ⟨hr, hc⟩)
      · exact Or.inl ⟨hr, hc⟩
      · rw [adjacentList_iff] at h ⊢
        obtain ⟨c, hc, hadj⟩ := h
        exact Or.inr (Or.inr ⟨c, hc, ih c hc hadj⟩)

omit [DecidableEq V] in
/-- The right endpoint of an edge is a vertex of the tree. -/
public theorem Adjacent.mem_right {a b : V} {t : Tree V}
    (h : Adjacent a b t) : b ∈ Tree.vertices t :=
  h.symm.mem_left

omit [DecidableEq V] in
private theorem not_adjacent_self_of_nodup {a : V} :
    ∀ {t : Tree V}, (Tree.vertices t).Nodup → ¬ Adjacent a a t := by
  intro t
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro hnodup h
      have hflat : (cs.flatMap Tree.vertices).Nodup := by
        rw [Tree.vertices_node, List.nodup_cons] at hnodup
        exact hnodup.2
      obtain ⟨hnodupC, -⟩ := List.nodup_flatMap.mp hflat
      rw [adjacent_node] at h
      rcases h with ⟨hr, c, hc, hroot⟩ | ⟨hr, c, hc, hroot⟩ | h
      · have ha : a ∈ Tree.vertices c := by
          rw [← hroot]
          exact root_mem_vertices c
        have hmem : r ∈ cs.flatMap Tree.vertices := by
          rw [hr]
          exact List.mem_flatMap.mpr ⟨c, hc, ha⟩
        exact root_not_mem_flatMap_children
          hnodup hmem
      · have ha : a ∈ Tree.vertices c := by
          rw [← hroot]
          exact root_mem_vertices c
        have hmem : r ∈ cs.flatMap Tree.vertices := by
          rw [hr]
          exact List.mem_flatMap.mpr ⟨c, hc, ha⟩
        exact root_not_mem_flatMap_children
          hnodup hmem
      · rw [adjacentList_iff] at h
        obtain ⟨c, hc, hadj⟩ := h
        exact ih c hc (hnodupC c hc) hadj

/-- Computable adjacency test: `adjacentB a b t = true` exactly when
`Adjacent a b t` (`adjacentB_eq_true_iff`). This is the guard evaluated by
`State.cutEdge` before it cuts. -/
public def adjacentB (a b : V) : Tree V → Bool
  | .node r cs =>
      (decide (r = a) && cs.any (fun c => decide (c.root = b))) ||
        (decide (r = b) && cs.any (fun c => decide (c.root = a))) ||
        adjacentBList a b cs
where
  /-- Adjacency test over a list of subtrees. -/
  adjacentBList (a b : V) : List (Tree V) → Bool
    | [] => false
    | c :: cs => adjacentB a b c || adjacentBList a b cs

private theorem adjacentBList_eq_true_iff {a b : V} :
    ∀ {cs : List (Tree V)},
      adjacentB.adjacentBList a b cs = true ↔
        ∃ c ∈ cs, adjacentB a b c = true := by
  intro cs
  induction cs with
  | nil => simp [adjacentB.adjacentBList]
  | cons c cs ih =>
      have hcons : adjacentB.adjacentBList a b (c :: cs) =
          (adjacentB a b c || adjacentB.adjacentBList a b cs) := rfl
      rw [hcons, Bool.or_eq_true, ih]
      constructor
      · rintro (h | ⟨d, hd, hadj⟩)
        · exact ⟨c, List.mem_cons_self, h⟩
        · exact ⟨d, List.mem_cons_of_mem c hd, hadj⟩
      · rintro ⟨d, hd, hadj⟩
        rw [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact Or.inl hadj
        · exact Or.inr ⟨d, hd, hadj⟩

public theorem adjacentB_eq_true_iff {a b : V} :
    ∀ {t : Tree V}, adjacentB a b t = true ↔ Adjacent a b t := by
  intro t
  induction t using Tree.children_ind with
  | node r cs ih =>
      have hnode : adjacentB a b (.node r cs) =
          ((decide (r = a) && cs.any (fun c => decide (c.root = b))) ||
            (decide (r = b) && cs.any (fun c => decide (c.root = a))) ||
            adjacentB.adjacentBList a b cs) := rfl
      rw [hnode, adjacent_node, adjacentList_iff]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        List.any_eq_true, adjacentBList_eq_true_iff]
      constructor
      · rintro ((⟨hr, c, hc, hroot⟩ | ⟨hr, c, hc, hroot⟩) | ⟨c, hc, hadj⟩)
        · exact Or.inl ⟨hr, c, hc, hroot⟩
        · exact Or.inr (Or.inl ⟨hr, c, hc, hroot⟩)
        · exact Or.inr (Or.inr ⟨c, hc, (ih c hc).mp hadj⟩)
      · rintro (⟨hr, c, hc, hroot⟩ | ⟨hr, c, hc, hroot⟩ | ⟨c, hc, hadj⟩)
        · exact Or.inl (Or.inl ⟨hr, c, hc, hroot⟩)
        · exact Or.inl (Or.inr ⟨hr, c, hc, hroot⟩)
        · exact Or.inr ⟨c, hc, (ih c hc).mpr hadj⟩

private theorem adjacent_findSubtree_of_mem_mem {a b y : V} :
    ∀ {t sub : Tree V}, (Tree.vertices t).Nodup →
      findSubtree y t = some sub → Adjacent a b t →
      a ∈ Tree.vertices sub → b ∈ Tree.vertices sub →
      Adjacent a b sub := by
  intro t
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro sub hnodup hsub hadj ha hb
      by_cases hr : r = y
      · have heq : findSubtree y (.node r cs) = some (.node r cs) := by
          simp [findSubtree, hr]
        rw [heq] at hsub
        have hst : (Tree.node r cs : Tree V) = sub := Option.some.inj hsub
        subst hst
        exact hadj
      · have heq : findSubtree y (.node r cs) =
            findSubtree.findSubtreeList y cs := by simp [findSubtree, hr]
        rw [heq] at hsub
        obtain ⟨c₀, hc₀, hsub₀⟩ := findSubtreeList_eq_some_spec hsub
        have hflat : (cs.flatMap Tree.vertices).Nodup := by
          rw [Tree.vertices_node, List.nodup_cons] at hnodup
          exact hnodup.2
        obtain ⟨hnodupC, -⟩ := List.nodup_flatMap.mp hflat
        have hac₀ : a ∈ Tree.vertices c₀ := mem_vertices_findSubtree hsub₀ ha
        have hbc₀ : b ∈ Tree.vertices c₀ := mem_vertices_findSubtree hsub₀ hb
        rw [adjacent_node] at hadj
        rcases hadj with ⟨hr2, -, -, -⟩ | ⟨hr2, -, -, -⟩ | hadj
        · exfalso
          rw [← hr2] at hac₀
          exact root_not_mem_flatMap_children
            hnodup
            (List.mem_flatMap.mpr ⟨c₀, hc₀, hac₀⟩)
        · exfalso
          rw [← hr2] at hbc₀
          exact root_not_mem_flatMap_children
            hnodup
            (List.mem_flatMap.mpr ⟨c₀, hc₀, hbc₀⟩)
        · rw [adjacentList_iff] at hadj
          obtain ⟨c, hc, hadj⟩ := hadj
          have hcc₀ : c = c₀ :=
            eq_of_mem_vertices_of_nodup_flatMap hflat hc hc₀
              hadj.mem_left hac₀
          subst hcc₀
          exact ih c hc (hnodupC c hc) hsub₀ hadj ha hb

omit [DecidableEq V] in
private theorem adjacent_node_crossing {a b r : V} {cs : List (Tree V)}
    {c₀ : Tree V} (hnodup : (Tree.vertices (.node r cs)).Nodup)
    (hc₀ : c₀ ∈ cs) (hadj : Adjacent a b (.node r cs))
    (ha : a ∈ Tree.vertices c₀) (hb : b ∉ Tree.vertices c₀) :
    b = r ∧ a = c₀.root := by
  have hflat : (cs.flatMap Tree.vertices).Nodup := by
    rw [Tree.vertices_node, List.nodup_cons] at hnodup
    exact hnodup.2
  rw [adjacent_node] at hadj
  rcases hadj with ⟨hr, -, -, -⟩ | ⟨hr, c, hc, hroot⟩ | hadj
  · exfalso
    rw [← hr] at ha
    exact root_not_mem_flatMap_children
      hnodup
      (List.mem_flatMap.mpr ⟨c₀, hc₀, ha⟩)
  · have hac : a ∈ Tree.vertices c := by
      rw [← hroot]
      exact root_mem_vertices c
    have hcc₀ : c = c₀ :=
      eq_of_mem_vertices_of_nodup_flatMap hflat hc hc₀ hac ha
    subst hcc₀
    exact ⟨hr.symm, hroot.symm⟩
  · rw [adjacentList_iff] at hadj
    obtain ⟨c, hc, hadj⟩ := hadj
    exfalso
    have hcc₀ : c = c₀ :=
      eq_of_mem_vertices_of_nodup_flatMap hflat hc hc₀ hadj.mem_left ha
    subst hcc₀
    exact hb hadj.mem_right

/-- Attach `newChild` as a new last child of the node labelled `y`, keeping
every existing node and edge. Returns `none` when `y` does not occur. This
is the tree surgery behind `State.link`: it adds exactly the edge from `y`
to the root of `newChild`. -/
public def graftAt (y : V) (newChild : Tree V) : Tree V → Option (Tree V)
  | .node r cs =>
      if r = y then some (.node r (cs ++ [newChild]))
      else (graftAtList y newChild cs).map (.node r)
where
  graftAtList (y : V) (newChild : Tree V) :
      List (Tree V) → Option (List (Tree V))
    | [] => none
    | c :: cs =>
        match graftAt y newChild c with
        | some c' => some (c' :: cs)
        | none => (graftAtList y newChild cs).map (c :: ·)

private theorem graftAtList_eq_some_of_exists {y : V} {newChild : Tree V} :
    ∀ {cs : List (Tree V)}, (∃ c ∈ cs, ∃ c', graftAt y newChild c = some c') →
      ∃ cs', graftAt.graftAtList y newChild cs = some cs' := by
  intro cs
  induction cs with
  | nil =>
      intro h
      obtain ⟨c, hmem, -⟩ := h
      exact absurd hmem (by simp)
  | cons c cs ih =>
      intro h
      cases hc : graftAt y newChild c with
      | some c' => exact ⟨c' :: cs, by simp [graftAt.graftAtList, hc]⟩
      | none =>
          obtain ⟨d, hmem, d', hd⟩ := h
          have htail : ∃ d ∈ cs, ∃ d', graftAt y newChild d = some d' := by
            rw [List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · rw [hc] at hd
              exact absurd hd (by simp)
            · exact ⟨d, hmem, d', hd⟩
          obtain ⟨cs', hcs'⟩ := ih htail
          exact ⟨c :: cs', by simp [graftAt.graftAtList, hc, hcs']⟩

public theorem graftAt_eq_some_of_mem {y : V} {newChild t : Tree V}
    (hy : y ∈ Tree.vertices t) : ∃ t', graftAt y newChild t = some t' := by
  revert hy
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro hy
      by_cases hr : r = y
      · exact ⟨.node r (cs ++ [newChild]), by simp [graftAt, hr]⟩
      · have hchild : ∃ c ∈ cs, ∃ c', graftAt y newChild c = some c' := by
          rw [mem_vertices_node] at hy
          rcases hy with hy | ⟨c, hc, hyc⟩
          · exact absurd hy.symm hr
          · obtain ⟨c', hc'⟩ := ih c hc hyc
            exact ⟨c, hc, c', hc'⟩
        obtain ⟨cs', hcs'⟩ := graftAtList_eq_some_of_exists hchild
        exact ⟨.node r cs', by simp [graftAt, hr, hcs']⟩





private theorem mem_flatMap_graftAtList {y v : V} {newChild : Tree V} :
    ∀ (ds : List (Tree V)),
      (∀ c ∈ ds, ∀ t', graftAt y newChild c = some t' →
        (v ∈ Tree.vertices t' ↔
          v ∈ Tree.vertices c ∨ v ∈ Tree.vertices newChild)) →
      ∀ (ds' : List (Tree V)),
      graftAt.graftAtList y newChild ds = some ds' →
      (v ∈ ds'.flatMap Tree.vertices ↔
        v ∈ ds.flatMap Tree.vertices ∨ v ∈ Tree.vertices newChild) := by
  intro ds hih ds' h
  induction ds generalizing ds' with
  | nil =>
      have hnil : graftAt.graftAtList y newChild [] = none := rfl
      rw [hnil] at h
      cases h
  | cons c ds ihl =>
      cases hc : graftAt y newChild c with
      | some c' =>
          have heq : graftAt.graftAtList y newChild (c :: ds) =
              some (c' :: ds) := by simp [graftAt.graftAtList, hc]
          rw [heq] at h
          have hcs : (c' :: ds : List (Tree V)) = ds' := Option.some.inj h
          rw [← hcs]
          simp only [List.flatMap_cons, List.mem_append]
          have hic := hih c (by simp) c' hc
          constructor
          · rintro (hv | hv)
            · exact (hic.mp hv).elim (fun hv => Or.inl (Or.inl hv)) Or.inr
            · exact Or.inl (Or.inr hv)
          · rintro ((hv | hv) | hv)
            · exact Or.inl (hic.mpr (Or.inl hv))
            · exact Or.inr hv
            · exact Or.inl (hic.mpr (Or.inr hv))
      | none =>
          have heq : graftAt.graftAtList y newChild (c :: ds) =
              (graftAt.graftAtList y newChild ds).map (c :: ·) := by
            simp [graftAt.graftAtList, hc]
          rw [heq] at h
          obtain ⟨ds₀, hds₀, hds⟩ := Option.map_eq_some_iff.mp h
          rw [← hds]
          have hrest := ihl (fun d hd => hih d (List.mem_cons_of_mem c hd)) ds₀ hds₀
          simp only [List.flatMap_cons, List.mem_append]
          constructor
          · rintro (hv | hv)
            · exact Or.inl (Or.inl hv)
            · exact (hrest.mp hv).elim (fun hv => Or.inl (Or.inr hv)) Or.inr
          · rintro ((hv | hv) | hv)
            · exact Or.inl hv
            · exact Or.inr (hrest.mpr (Or.inl hv))
            · exact Or.inr (hrest.mpr (Or.inr hv))

/-- Grafting keeps every old vertex and adds exactly the vertices of the
new child. -/
public theorem mem_vertices_graftAt {y v : V} {newChild : Tree V} :
    ∀ {t t' : Tree V}, graftAt y newChild t = some t' →
      (v ∈ Tree.vertices t' ↔ v ∈ Tree.vertices t ∨ v ∈ Tree.vertices newChild) := by
  intro t
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro t' h
      by_cases hr : r = y
      · have heq : graftAt y newChild (.node r cs) =
            some (.node r (cs ++ [newChild])) := by simp [graftAt, hr]
        rw [heq] at h
        have hst : (Tree.node r (cs ++ [newChild]) : Tree V) = t' :=
          Option.some.inj h
        rw [← hst]
        simp only [Tree.vertices_node, List.flatMap_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append]
        constructor
        · rintro (hv | hv | hv)
          · exact Or.inl (Or.inl hv)
          · exact Or.inl (Or.inr hv)
          · exact Or.inr hv
        · rintro ((hv | hv) | hv)
          · exact Or.inl hv
          · exact Or.inr (Or.inl hv)
          · exact Or.inr (Or.inr hv)
      · have heq : graftAt y newChild (.node r cs) =
            (graftAt.graftAtList y newChild cs).map (.node r) := by
          simp [graftAt, hr]
        rw [heq] at h
        obtain ⟨cs', hcs', hcs⟩ := Option.map_eq_some_iff.mp h
        rw [← hcs]
        have hflat := mem_flatMap_graftAtList cs ih cs' hcs'
        simp only [Tree.vertices_node, List.mem_cons]
        constructor
        · rintro (hv | hv)
          · exact Or.inl (Or.inl hv)
          · exact (hflat.mp hv).elim (fun hv => Or.inl (Or.inr hv)) Or.inr
        · rintro ((hv | hv) | hv)
          · exact Or.inl hv
          · exact Or.inr (hflat.mpr (Or.inl hv))
          · exact Or.inr (hflat.mpr (Or.inr hv))

/-- Grafting does not change the root. -/
public theorem root_graftAt {y : V} {newChild : Tree V} :
    ∀ {t t' : Tree V}, graftAt y newChild t = some t' → t'.root = t.root := by
  intro t
  induction t using Tree.children_ind with
  | node r cs _ =>
      intro t' h
      by_cases hr : r = y
      · have heq : graftAt y newChild (.node r cs) =
            some (.node r (cs ++ [newChild])) := by simp [graftAt, hr]
        rw [heq] at h
        have hst : (Tree.node r (cs ++ [newChild]) : Tree V) = t' :=
          Option.some.inj h
        subst hst
        rfl
      · have heq : graftAt y newChild (.node r cs) =
            (graftAt.graftAtList y newChild cs).map (.node r) := by
          simp [graftAt, hr]
        rw [heq] at h
        obtain ⟨cs', -, hcs⟩ := Option.map_eq_some_iff.mp h
        rw [← hcs]
        rfl

private theorem adjacentList_graftAtList {y a b : V} {newChild : Tree V} :
    ∀ (ds : List (Tree V)),
      (∀ c ∈ ds, ∀ t', graftAt y newChild c = some t' →
        (Adjacent a b t' ↔ Adjacent a b c ∨ Adjacent a b newChild ∨
          (a = y ∧ b = newChild.root) ∨ (a = newChild.root ∧ b = y))) →
      ∀ (ds' : List (Tree V)),
      graftAt.graftAtList y newChild ds = some ds' →
      (Adjacent.AdjacentList a b ds' ↔ Adjacent.AdjacentList a b ds ∨
        Adjacent a b newChild ∨ (a = y ∧ b = newChild.root) ∨
          (a = newChild.root ∧ b = y)) := by
  intro ds hih ds' h
  induction ds generalizing ds' with
  | nil =>
      have hnil : graftAt.graftAtList y newChild ([] : List (Tree V)) = none :=
        rfl
      rw [hnil] at h
      cases h
  | cons c ds ihl =>
      cases hc : graftAt y newChild c with
      | some c' =>
          have heq : graftAt.graftAtList y newChild (c :: ds) =
              some (c' :: ds) := by simp [graftAt.graftAtList, hc]
          rw [heq] at h
          have hcs : (c' :: ds : List (Tree V)) = ds' := Option.some.inj h
          rw [← hcs]
          have hcons' : Adjacent.AdjacentList a b (c' :: ds) ↔
              Adjacent a b c' ∨ Adjacent.AdjacentList a b ds := Iff.rfl
          have hcons : Adjacent.AdjacentList a b (c :: ds) ↔
              Adjacent a b c ∨ Adjacent.AdjacentList a b ds := Iff.rfl
          rw [hcons', hcons]
          have hic := hih c (by simp) c' hc
          rw [hic]
          constructor
          · rintro ((h | h | h | h) | h)
            · exact Or.inl (Or.inl h)
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr h))
            · exact Or.inl (Or.inr h)
          · rintro ((h | h) | h | h | h)
            · exact Or.inl (Or.inl h)
            · exact Or.inr h
            · exact Or.inl (Or.inr (Or.inl h))
            · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
            · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
      | none =>
          have heq : graftAt.graftAtList y newChild (c :: ds) =
              (graftAt.graftAtList y newChild ds).map (c :: ·) := by
            simp [graftAt.graftAtList, hc]
          rw [heq] at h
          obtain ⟨ds₀, hds₀, hds⟩ := Option.map_eq_some_iff.mp h
          rw [← hds]
          have hrest := ihl (fun d hd => hih d (List.mem_cons_of_mem c hd))
            ds₀ hds₀
          have hcons' : Adjacent.AdjacentList a b (c :: ds₀) ↔
              Adjacent a b c ∨ Adjacent.AdjacentList a b ds₀ := Iff.rfl
          have hcons : Adjacent.AdjacentList a b (c :: ds) ↔
              Adjacent a b c ∨ Adjacent.AdjacentList a b ds := Iff.rfl
          rw [hcons', hcons, hrest]
          constructor
          · rintro (h | h | h | h | h)
            · exact Or.inl (Or.inl h)
            · exact Or.inl (Or.inr h)
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr h))
          · rintro ((h | h) | h | h | h)
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

private theorem exists_root_graftAtList {y b : V} {newChild : Tree V} :
    ∀ (ds : List (Tree V)),
      (∀ c ∈ ds, ∀ t', graftAt y newChild c = some t' → t'.root = c.root) →
      ∀ (ds' : List (Tree V)),
      graftAt.graftAtList y newChild ds = some ds' →
      ((∃ c ∈ ds', c.root = b) ↔ ∃ c ∈ ds, c.root = b) := by
  intro ds hih ds' h
  induction ds generalizing ds' with
  | nil =>
      have hnil : graftAt.graftAtList y newChild ([] : List (Tree V)) = none :=
        rfl
      rw [hnil] at h
      cases h
  | cons c ds ihl =>
      cases hc : graftAt y newChild c with
      | some c' =>
          have heq : graftAt.graftAtList y newChild (c :: ds) =
              some (c' :: ds) := by simp [graftAt.graftAtList, hc]
          rw [heq] at h
          have hcs : (c' :: ds : List (Tree V)) = ds' := Option.some.inj h
          rw [← hcs]
          have hroot : c'.root = c.root := hih c (by simp) c' hc
          constructor
          · rintro ⟨d, hd, hdroot⟩
            rw [List.mem_cons] at hd
            rcases hd with rfl | hd
            · exact ⟨c, List.mem_cons_self, hroot.symm.trans hdroot⟩
            · exact ⟨d, List.mem_cons_of_mem c hd, hdroot⟩
          · rintro ⟨d, hd, hdroot⟩
            rw [List.mem_cons] at hd
            rcases hd with rfl | hd
            · exact ⟨c', List.mem_cons_self, hroot.trans hdroot⟩
            · exact ⟨d, List.mem_cons_of_mem c' hd, hdroot⟩
      | none =>
          have heq : graftAt.graftAtList y newChild (c :: ds) =
              (graftAt.graftAtList y newChild ds).map (c :: ·) := by
            simp [graftAt.graftAtList, hc]
          rw [heq] at h
          obtain ⟨ds₀, hds₀, hds⟩ := Option.map_eq_some_iff.mp h
          rw [← hds]
          have hrest := ihl (fun d hd => hih d (List.mem_cons_of_mem c hd))
            ds₀ hds₀
          constructor
          · rintro ⟨d, hd, hdroot⟩
            rw [List.mem_cons] at hd
            rcases hd with rfl | hd
            · exact ⟨d, List.mem_cons_self, hdroot⟩
            · obtain ⟨e, he, heroot⟩ := hrest.mp ⟨d, hd, hdroot⟩
              exact ⟨e, List.mem_cons_of_mem c he, heroot⟩
          · rintro ⟨d, hd, hdroot⟩
            rw [List.mem_cons] at hd
            rcases hd with rfl | hd
            · exact ⟨d, List.mem_cons_self, hdroot⟩
            · obtain ⟨e, he, heroot⟩ := hrest.mpr ⟨d, hd, hdroot⟩
              exact ⟨e, List.mem_cons_of_mem c he, heroot⟩

/-- Grafting keeps every old edge and every edge of the new child, and adds
exactly the edge from `y` to the root of `newChild`. -/
public theorem adjacent_graftAt {y a b : V} {newChild : Tree V} :
    ∀ {t t' : Tree V}, graftAt y newChild t = some t' →
      (Adjacent a b t' ↔ Adjacent a b t ∨ Adjacent a b newChild ∨
        (a = y ∧ b = newChild.root) ∨ (a = newChild.root ∧ b = y)) := by
  intro t
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro t' h
      by_cases hr : r = y
      · have heq : graftAt y newChild (.node r cs) =
            some (.node r (cs ++ [newChild])) := by simp [graftAt, hr]
        rw [heq] at h
        have hst : (Tree.node r (cs ++ [newChild]) : Tree V) = t' :=
          Option.some.inj h
        rw [← hst]
        have hmemB : (∃ c ∈ cs ++ [newChild], c.root = b) ↔
            (∃ c ∈ cs, c.root = b) ∨ newChild.root = b := by
          constructor
          · rintro ⟨c, hc, hroot⟩
            rw [List.mem_append] at hc
            rcases hc with hc | hc
            · exact Or.inl ⟨c, hc, hroot⟩
            · rw [List.mem_singleton] at hc
              exact Or.inr (hc ▸ hroot)
          · rintro (⟨c, hc, hroot⟩ | hroot)
            · exact ⟨c, List.mem_append_left _ hc, hroot⟩
            · exact ⟨newChild, by simp, hroot⟩
        have hmemA : (∃ c ∈ cs ++ [newChild], c.root = a) ↔
            (∃ c ∈ cs, c.root = a) ∨ newChild.root = a := by
          constructor
          · rintro ⟨c, hc, hroot⟩
            rw [List.mem_append] at hc
            rcases hc with hc | hc
            · exact Or.inl ⟨c, hc, hroot⟩
            · rw [List.mem_singleton] at hc
              exact Or.inr (hc ▸ hroot)
          · rintro (⟨c, hc, hroot⟩ | hroot)
            · exact ⟨c, List.mem_append_left _ hc, hroot⟩
            · exact ⟨newChild, by simp, hroot⟩
        have hlistApp : Adjacent.AdjacentList a b (cs ++ [newChild]) ↔
            Adjacent.AdjacentList a b cs ∨ Adjacent a b newChild := by
          rw [adjacentList_iff, adjacentList_iff]
          constructor
          · rintro ⟨c, hc, hadj⟩
            rw [List.mem_append] at hc
            rcases hc with hc | hc
            · exact Or.inl ⟨c, hc, hadj⟩
            · rw [List.mem_singleton] at hc
              exact Or.inr (hc ▸ hadj)
          · rintro (⟨c, hc, hadj⟩ | hadj)
            · exact ⟨c, List.mem_append_left _ hc, hadj⟩
            · exact ⟨newChild, by simp, hadj⟩
        simp only [adjacent_node, hmemB, hmemA, hlistApp]
        constructor
        · rintro (⟨hra, (hex | hroot)⟩ | ⟨hrb, (hex | hroot)⟩ | h | h)
          · exact Or.inl (Or.inl ⟨hra, hex⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨hra.symm.trans hr, hroot.symm⟩))
          · exact Or.inl (Or.inr (Or.inl ⟨hrb, hex⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨hroot.symm, hrb.symm.trans hr⟩))
          · exact Or.inl (Or.inr (Or.inr h))
          · exact Or.inr (Or.inl h)
        · rintro ((⟨hra, hex⟩ | ⟨hrb, hex⟩ | h) | h | ⟨hay, hb⟩ | ⟨ha, hby⟩)
          · exact Or.inl ⟨hra, Or.inl hex⟩
          · exact Or.inr (Or.inl ⟨hrb, Or.inl hex⟩)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
          · exact Or.inl ⟨hr.trans hay.symm, Or.inr hb.symm⟩
          · exact Or.inr (Or.inl ⟨hr.trans hby.symm, Or.inr ha.symm⟩)
      · have heq : graftAt y newChild (.node r cs) =
            (graftAt.graftAtList y newChild cs).map (.node r) := by
          simp [graftAt, hr]
        rw [heq] at h
        obtain ⟨cs', hcs', hcs⟩ := Option.map_eq_some_iff.mp h
        rw [← hcs]
        have hflat := adjacentList_graftAtList cs ih cs' hcs'
        have hexB := exists_root_graftAtList cs
          (fun c _ t' ht' => root_graftAt ht') cs' hcs' (b := b)
        have hexA := exists_root_graftAtList cs
          (fun c _ t' ht' => root_graftAt ht') cs' hcs' (b := a)
        simp only [adjacent_node, hexB, hexA, hflat]
        constructor
        · rintro (⟨hra, hex⟩ | ⟨hrb, hex⟩ | h | h | h | h)
          · exact Or.inl (Or.inl ⟨hra, hex⟩)
          · exact Or.inl (Or.inr (Or.inl ⟨hrb, hex⟩))
          · exact Or.inl (Or.inr (Or.inr h))
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
        · rintro ((⟨hra, hex⟩ | ⟨hrb, hex⟩ | h) | h | h | h)
          · exact Or.inl ⟨hra, hex⟩
          · exact Or.inr (Or.inl ⟨hrb, hex⟩)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))


private theorem perm_rotate3 (a b c : List V) :
    ((a ++ b) ++ c).Perm ((a ++ c) ++ b) := by
  rw [List.append_assoc, List.append_assoc]
  exact List.Perm.append_left a List.perm_append_comm

private theorem perm_flatMap_graftAtList {y : V} {newChild : Tree V} :
    ∀ (ds : List (Tree V)),
      (∀ c ∈ ds, ∀ t', graftAt y newChild c = some t' →
        (Tree.vertices t').Perm (Tree.vertices c ++ Tree.vertices newChild)) →
      ∀ (ds' : List (Tree V)),
      graftAt.graftAtList y newChild ds = some ds' →
      (ds'.flatMap Tree.vertices).Perm
        (ds.flatMap Tree.vertices ++ Tree.vertices newChild) := by
  intro ds hih ds' h
  induction ds generalizing ds' with
  | nil =>
      have hnil : graftAt.graftAtList y newChild ([] : List (Tree V)) = none :=
        rfl
      rw [hnil] at h
      cases h
  | cons c ds ihl =>
      cases hc : graftAt y newChild c with
      | some c' =>
          have heq : graftAt.graftAtList y newChild (c :: ds) =
              some (c' :: ds) := by simp [graftAt.graftAtList, hc]
          rw [heq] at h
          have hcs : (c' :: ds : List (Tree V)) = ds' := Option.some.inj h
          rw [← hcs]
          have hic := hih c (by simp) c' hc
          simp only [List.flatMap_cons]
          exact (hic.append_right (ds.flatMap Tree.vertices)).trans
            (perm_rotate3 _ _ _)
      | none =>
          have heq : graftAt.graftAtList y newChild (c :: ds) =
              (graftAt.graftAtList y newChild ds).map (c :: ·) := by
            simp [graftAt.graftAtList, hc]
          rw [heq] at h
          obtain ⟨ds₀, hds₀, hds⟩ := Option.map_eq_some_iff.mp h
          rw [← hds]
          have hrest := ihl (fun d hd => hih d (List.mem_cons_of_mem c hd))
            ds₀ hds₀
          simp only [List.flatMap_cons]
          exact (hrest.append_left (Tree.vertices c)).trans
            (List.Perm.of_eq (List.append_assoc _ _ _).symm)

/-- The vertex list of a grafted tree is the old vertex list followed by
the new child's, up to permutation. -/
public theorem perm_vertices_graftAt {y : V} {newChild : Tree V} :
    ∀ {t t' : Tree V}, graftAt y newChild t = some t' →
      (Tree.vertices t').Perm (Tree.vertices t ++ Tree.vertices newChild) := by
  intro t
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro t' h
      by_cases hr : r = y
      · have heq : graftAt y newChild (.node r cs) =
            some (.node r (cs ++ [newChild])) := by simp [graftAt, hr]
        rw [heq] at h
        have hst : (Tree.node r (cs ++ [newChild]) : Tree V) = t' :=
          Option.some.inj h
        rw [← hst]
        apply List.Perm.of_eq
        simp [Tree.vertices_node, List.flatMap_append]
      · have heq : graftAt y newChild (.node r cs) =
            (graftAt.graftAtList y newChild cs).map (.node r) := by
          simp [graftAt, hr]
        rw [heq] at h
        obtain ⟨cs', hcs', hcs⟩ := Option.map_eq_some_iff.mp h
        rw [← hcs]
        have hflat := perm_flatMap_graftAtList cs ih cs' hcs'
        have hnode : ∀ ds : List (Tree V), Tree.vertices (.node r ds) =
            r :: ds.flatMap Tree.vertices := by
          intro ds
          simp [Tree.vertices_node]
        rw [hnode cs', hnode cs]
        exact (hflat.cons r).trans
          (List.Perm.of_eq List.cons_append.symm)


/-- Reroot a tree at `x`, reversing the edges on the path from the old root
to `x` and keeping every other edge: the undirected tree is unchanged, only
the choice of root changes. Returns `none` when `x` does not occur. This is
the tree surgery behind `State.makeRoot`.

The recursion reroots the child subtree `c` on the root-to-`x` path first,
then grafts the remainder of the current node (the old root `r` together
with the sibling subtrees off the path) back under the root of `c`, which
is the next vertex on the reversed path. Attaching the remainder under
that path vertex, rather than directly under `x`, is what keeps every
path edge intact at depth greater than one. -/
public def rerootAt (x : V) : Tree V → Option (Tree V)
  | .node r cs =>
      if r = x then some (.node r cs)
      else
        match rerootAtList x cs with
        | some (c', rest, p) => graftAt p (.node r rest) c'
        | none => none
where
  /-- Reroot the first child subtree containing `x`; returns the rerooted
  child, the remaining sibling subtrees in order, and the root of the
  original child (the next vertex on the root-to-`x` path, under which the
  caller reattaches the remainder). -/
  rerootAtList (x : V) : List (Tree V) → Option (Tree V × List (Tree V) × V)
    | [] => none
    | c :: cs =>
        match rerootAt x c with
        | some c' => some (c', cs, c.root)
        | none =>
            (rerootAtList x cs).map (fun (c', rest, p) => (c', c :: rest, p))

private theorem rerootAtList_eq_some_of_exists {x : V} :
    ∀ {cs : List (Tree V)}, (∃ c ∈ cs, ∃ c', rerootAt x c = some c') →
      ∃ c' rest p, rerootAt.rerootAtList x cs = some (c', rest, p) := by
  intro cs
  induction cs with
  | nil =>
      intro h
      obtain ⟨c, hmem, -⟩ := h
      exact absurd hmem (by simp)
  | cons c cs ih =>
      intro h
      cases hc : rerootAt x c with
      | some c' =>
          exact ⟨c', cs, c.root, by simp [rerootAt.rerootAtList, hc]⟩
      | none =>
          obtain ⟨d, hmem, d', hd⟩ := h
          have htail : ∃ d ∈ cs, ∃ d', rerootAt x d = some d' := by
            rw [List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · rw [hc] at hd
              exact absurd hd (by simp)
            · exact ⟨d, hmem, d', hd⟩
          obtain ⟨c', rest, p, hrest⟩ := ih htail
          exact ⟨c', c :: rest, p, by simp [rerootAt.rerootAtList, hc, hrest]⟩

private theorem rerootAtList_eq_some_spec {x : V} :
    ∀ {cs : List (Tree V)} {c' : Tree V} {rest : List (Tree V)} {p : V},
      rerootAt.rerootAtList x cs = some (c', rest, p) →
      ∃ c ∈ cs, rerootAt x c = some c' ∧ p = c.root ∧
        ∀ d : Tree V, d ∈ cs ↔ d = c ∨ d ∈ rest := by
  intro cs
  induction cs with
  | nil =>
      intro c' rest p h
      simp [rerootAt.rerootAtList] at h
  | cons c cs ih =>
      intro c' rest p h
      cases hc : rerootAt x c with
      | some c₀ =>
          have heq : rerootAt.rerootAtList x (c :: cs) =
              some (c₀, cs, c.root) := by
            simp [rerootAt.rerootAtList, hc]
          rw [heq] at h
          have hpair : (c₀, cs, c.root) = (c', rest, p) := Option.some.inj h
          obtain ⟨rfl, rfl, rfl⟩ : c' = c₀ ∧ rest = cs ∧ p = c.root := by
            simp only [Prod.mk.injEq] at hpair
            exact ⟨hpair.1.symm, hpair.2.1.symm, hpair.2.2.symm⟩
          refine ⟨c, by simp, hc, rfl, fun d => ?_⟩
          rw [List.mem_cons]
      | none =>
          have heq : rerootAt.rerootAtList x (c :: cs) =
              (rerootAt.rerootAtList x cs).map
                (fun (c', rest, p) => (c', c :: rest, p)) := by
            simp [rerootAt.rerootAtList, hc]
          rw [heq] at h
          obtain ⟨⟨c₀, rest₀, p₀⟩, hrest₀, hpair⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨rfl, rfl, rfl⟩ : c' = c₀ ∧ rest = c :: rest₀ ∧ p = p₀ := by
            simp only [Prod.mk.injEq] at hpair
            exact ⟨hpair.1.symm, hpair.2.1.symm, hpair.2.2.symm⟩
          obtain ⟨d, hd, hd', hdp, hmem⟩ := ih hrest₀
          refine ⟨d, List.mem_cons_of_mem c hd, hd', hdp, fun e => ?_⟩
          rw [List.mem_cons, hmem e, List.mem_cons]
          constructor
          · rintro (h | h | h)
            · exact Or.inr (Or.inl h)
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
          · rintro (h | h | h)
            · exact Or.inr (Or.inl h)
            · exact Or.inl h
            · exact Or.inr (Or.inr h)

/-- Rerooting at a vertex that does not occur fails. -/
public theorem rerootAt_eq_none_of_not_mem {x : V} :
    ∀ {t : Tree V}, x ∉ Tree.vertices t → rerootAt x t = none := by
  intro t
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro hx
      have hr : r ≠ x :=
        fun hreq => hx (mem_vertices_node.mpr (Or.inl hreq.symm))
      have hlist : ∀ (ds : List (Tree V)),
          (∀ c ∈ ds, rerootAt x c = none) →
          rerootAt.rerootAtList x ds = none := by
        intro ds
        induction ds with
        | nil => intro _; rfl
        | cons c ds ihl =>
            intro hall
            have hc : rerootAt x c = none := hall c List.mem_cons_self
            have hrest : rerootAt.rerootAtList x ds = none :=
              ihl (fun d hd => hall d (List.mem_cons_of_mem c hd))
            simp [rerootAt.rerootAtList, hc, hrest]
      have hcs : rerootAt.rerootAtList x cs = none :=
        hlist cs (fun c hc => ih c hc (fun hxc => hx
          (mem_vertices_node.mpr (Or.inr ⟨c, hc, hxc⟩))))
      simp [rerootAt, hr, hcs]

private theorem mem_rerootAtList {x v : V} :
    ∀ (ds : List (Tree V)),
      (∀ c ∈ ds, ∀ t', rerootAt x c = some t' →
        (v ∈ Tree.vertices t' ↔ v ∈ Tree.vertices c)) →
      ∀ (c' : Tree V) (rest : List (Tree V)) (p : V),
      rerootAt.rerootAtList x ds = some (c', rest, p) →
      (v ∈ Tree.vertices c' ∨ v ∈ rest.flatMap Tree.vertices ↔
        v ∈ ds.flatMap Tree.vertices) := by
  intro ds hih c' rest p h
  induction ds generalizing c' rest p with
  | nil =>
      simp [rerootAt.rerootAtList] at h
  | cons c ds ihl =>
      cases hc : rerootAt x c with
      | some c₀ =>
          have heq : rerootAt.rerootAtList x (c :: ds) =
              some (c₀, ds, c.root) := by
            simp [rerootAt.rerootAtList, hc]
          rw [heq] at h
          have hpair : (c₀, ds, c.root) = (c', rest, p) := Option.some.inj h
          obtain ⟨rfl, rfl, -⟩ : c' = c₀ ∧ rest = ds ∧ p = c.root := by
            simp only [Prod.mk.injEq] at hpair
            exact ⟨hpair.1.symm, hpair.2.1.symm, hpair.2.2.symm⟩
          simp only [List.flatMap_cons, List.mem_append]
          have hic := hih c (by simp) c' hc
          constructor
          · rintro (hv | hv)
            · exact Or.inl (hic.mp hv)
            · exact Or.inr hv
          · rintro (hv | hv)
            · exact Or.inl (hic.mpr hv)
            · exact Or.inr hv
      | none =>
          have heq : rerootAt.rerootAtList x (c :: ds) =
              (rerootAt.rerootAtList x ds).map
                (fun (c', rest, p) => (c', c :: rest, p)) := by
            simp [rerootAt.rerootAtList, hc]
          rw [heq] at h
          obtain ⟨⟨c₀, rest₀, p₀⟩, hrest₀, hpair⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨rfl, rfl, -⟩ : c' = c₀ ∧ rest = c :: rest₀ ∧ p = p₀ := by
            simp only [Prod.mk.injEq] at hpair
            exact ⟨hpair.1.symm, hpair.2.1.symm, hpair.2.2.symm⟩
          have hrestIff := ihl (fun d hd => hih d (List.mem_cons_of_mem c hd))
            c' rest₀ p₀ hrest₀
          simp only [List.flatMap_cons, List.mem_append]
          constructor
          · rintro (hv | hv | hv)
            · exact Or.inr (hrestIff.mp (Or.inl hv))
            · exact Or.inl hv
            · exact Or.inr (hrestIff.mp (Or.inr hv))
          · rintro (hv | hv)
            · exact Or.inr (Or.inl hv)
            · exact (hrestIff.mpr hv).elim Or.inl (fun hv => Or.inr (Or.inr hv))

private theorem rerootAt_spec_of_mem {x : V} :
    ∀ {t : Tree V}, x ∈ Tree.vertices t →
      ∃ t', rerootAt x t = some t' ∧ t'.root = x ∧
        ∀ v : V, v ∈ Tree.vertices t' ↔ v ∈ Tree.vertices t := by
  intro t
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro hx
      by_cases hr : r = x
      · exact ⟨.node r cs, by simp [rerootAt, hr], by simp [hr],
          fun _ => Iff.rfl⟩
      · have hmemChild : ∀ c ∈ cs, ∀ t', rerootAt x c = some t' →
            ∀ v : V, v ∈ Tree.vertices t' ↔ v ∈ Tree.vertices c := by
          intro c hc t' ht' v
          have hxc : x ∈ Tree.vertices c := by
            by_contra hnot
            rw [rerootAt_eq_none_of_not_mem hnot] at ht'
            cases ht'
          obtain ⟨t'', ht''eq, -, ht''mem⟩ := ih c hc hxc
          have hst : t' = t'' := Option.some.inj (ht'.symm.trans ht''eq)
          rw [hst]
          exact ht''mem v
        have hchild : ∃ c ∈ cs, ∃ c', rerootAt x c = some c' := by
          rw [mem_vertices_node] at hx
          rcases hx with hx | ⟨c, hc, hxc⟩
          · exact absurd hx.symm hr
          · obtain ⟨c', hc', -, -⟩ := ih c hc hxc
            exact ⟨c, hc, c', hc'⟩
        obtain ⟨c', rest, p, hlist⟩ := rerootAtList_eq_some_of_exists hchild
        obtain ⟨c₀, hc₀, hc₀eq, hp, -⟩ := rerootAtList_eq_some_spec hlist
        have hxc₀ : x ∈ Tree.vertices c₀ := by
          by_contra hnot
          rw [rerootAt_eq_none_of_not_mem hnot] at hc₀eq
          cases hc₀eq
        obtain ⟨c₁, hc₁eq, hc₁root, hc₁mem⟩ := ih c₀ hc₀ hxc₀
        have hc'eq : c' = c₁ := Option.some.inj (hc₀eq.symm.trans hc₁eq)
        rw [hc'eq] at hlist
        have hpMem : p ∈ Tree.vertices c₁ := (hc₁mem p).mpr (by
          rw [hp]
          exact root_mem_vertices c₀)
        obtain ⟨t', ht'graft⟩ :=
          graftAt_eq_some_of_mem hpMem (newChild := .node r rest)
        have hnode : ∀ (v : V) (ds : List (Tree V)),
            v ∈ Tree.vertices (.node r ds) ↔
              v = r ∨ v ∈ ds.flatMap Tree.vertices := by
          intro v ds
          simp [Tree.vertices_node]
        refine ⟨t', by simp [rerootAt, hr, hlist, ht'graft],
          by rw [root_graftAt ht'graft]; exact hc₁root, ?_⟩
        intro v
        have hflat := mem_rerootAtList cs
          (fun c hc t' ht' => hmemChild c hc t' ht' v) c₁ rest p hlist
        have hgraft : v ∈ Tree.vertices t' ↔
            v ∈ Tree.vertices c₁ ∨ v ∈ Tree.vertices (.node r rest) :=
          mem_vertices_graftAt ht'graft
        rw [hgraft, hnode v rest, hnode v cs]
        constructor
        · rintro (hv | hv | hv)
          · exact Or.inr (hflat.mp (Or.inl hv))
          · exact Or.inl hv
          · exact Or.inr (hflat.mp (Or.inr hv))
        · rintro (hv | hv)
          · exact Or.inr (Or.inl hv)
          · exact (hflat.mpr hv).elim Or.inl (fun hv => Or.inr (Or.inr hv))

public theorem rerootAt_eq_some_of_mem {x : V} {t : Tree V}
    (hx : x ∈ Tree.vertices t) : ∃ t', rerootAt x t = some t' ∧ t'.root = x := by
  obtain ⟨t', ht'eq, ht'root, -⟩ := rerootAt_spec_of_mem hx
  exact ⟨t', ht'eq, ht'root⟩

public theorem root_rerootAt {x : V} :
    ∀ {t t' : Tree V}, rerootAt x t = some t' → t'.root = x := by
  intro t t' h
  have hx : x ∈ Tree.vertices t := by
    by_contra hnot
    rw [rerootAt_eq_none_of_not_mem hnot] at h
    cases h
  obtain ⟨t'', ht''eq, ht''root, -⟩ := rerootAt_spec_of_mem hx
  rw [ht''eq] at h
  have hst : t'' = t' := Option.some.inj h
  rw [← hst]
  exact ht''root

/-- Rerooting keeps exactly the same vertex set. -/
public theorem mem_vertices_rerootAt {x v : V} :
    ∀ {t t' : Tree V}, rerootAt x t = some t' →
      (v ∈ Tree.vertices t' ↔ v ∈ Tree.vertices t) := by
  intro t t' h
  have hx : x ∈ Tree.vertices t := by
    by_contra hnot
    rw [rerootAt_eq_none_of_not_mem hnot] at h
    cases h
  obtain ⟨t'', ht''eq, -, ht''mem⟩ := rerootAt_spec_of_mem hx
  rw [ht''eq] at h
  have hst : t'' = t' := Option.some.inj h
  rw [← hst]
  exact ht''mem v

/-- Rerooting a duplicate-free tree keeps every undirected edge: the
rerooted tree has exactly the same adjacency relation as the original. -/
public theorem adjacent_rerootAt {x a b : V} :
    ∀ {t t' : Tree V}, (Tree.vertices t).Nodup → rerootAt x t = some t' →
      (Adjacent a b t' ↔ Adjacent a b t) := by
  intro t
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro t' hnodup h
      by_cases hr : r = x
      · have heq : rerootAt x (.node r cs) = some (.node r cs) := by
          simp [rerootAt, hr]
        rw [heq] at h
        have hst : (Tree.node r cs : Tree V) = t' := Option.some.inj h
        subst hst
        exact Iff.rfl
      · have heq : rerootAt x (.node r cs) =
            match rerootAt.rerootAtList x cs with
            | some (c', rest, p) => graftAt p (.node r rest) c'
            | none => none := by
          simp [rerootAt, hr]
        rw [heq] at h
        cases hlist : rerootAt.rerootAtList x cs with
        | none => simp [hlist] at h
        | some q =>
            obtain ⟨c', rest, p⟩ := q
            rw [hlist] at h
            obtain ⟨c₀, hc₀, hc₀eq, hp, hmem⟩ :=
              rerootAtList_eq_some_spec hlist
            have hnodup' : (cs.flatMap Tree.vertices).Nodup := by
              have hh := hnodup
              rw [Tree.vertices_node, List.nodup_cons] at hh
              exact hh.2
            obtain ⟨hnodupC, -⟩ := List.nodup_flatMap.mp hnodup'
            have hih : Adjacent a b c' ↔ Adjacent a b c₀ :=
              ih c₀ hc₀ (hnodupC c₀ hc₀) hc₀eq
            have hgraft : Adjacent a b t' ↔ Adjacent a b c' ∨
                Adjacent a b (.node r rest) ∨
                (a = p ∧ b = (Tree.node r rest).root) ∨
                (a = (Tree.node r rest).root ∧ b = p) :=
              adjacent_graftAt h
            simp only [Tree.root_node] at hgraft
            rw [hp] at hgraft
            have hexB : (∃ c ∈ cs, c.root = b) ↔
                c₀.root = b ∨ ∃ c ∈ rest, c.root = b := by
              constructor
              · rintro ⟨c, hc, hroot⟩
                rw [hmem c] at hc
                rcases hc with rfl | hc
                · exact Or.inl hroot
                · exact Or.inr ⟨c, hc, hroot⟩
              · rintro (hroot | ⟨c, hc, hroot⟩)
                · exact ⟨c₀, hc₀, hroot⟩
                · exact ⟨c, (hmem c).mpr (Or.inr hc), hroot⟩
            have hexA : (∃ c ∈ cs, c.root = a) ↔
                c₀.root = a ∨ ∃ c ∈ rest, c.root = a := by
              constructor
              · rintro ⟨c, hc, hroot⟩
                rw [hmem c] at hc
                rcases hc with rfl | hc
                · exact Or.inl hroot
                · exact Or.inr ⟨c, hc, hroot⟩
              · rintro (hroot | ⟨c, hc, hroot⟩)
                · exact ⟨c₀, hc₀, hroot⟩
                · exact ⟨c, (hmem c).mpr (Or.inr hc), hroot⟩
            have hlistAdj : Adjacent.AdjacentList a b cs ↔
                Adjacent a b c₀ ∨ Adjacent.AdjacentList a b rest := by
              rw [adjacentList_iff, adjacentList_iff]
              constructor
              · rintro ⟨c, hc, hadj⟩
                rw [hmem c] at hc
                rcases hc with rfl | hc
                · exact Or.inl hadj
                · exact Or.inr ⟨c, hc, hadj⟩
              · rintro (hadj | ⟨c, hc, hadj⟩)
                · exact ⟨c₀, hc₀, hadj⟩
                · exact ⟨c, (hmem c).mpr (Or.inr hc), hadj⟩
            rw [hgraft]
            simp only [adjacent_node, hexB, hexA, hlistAdj, hih]
            constructor
            · rintro (h | (⟨hra, hex⟩ | ⟨hrb, hex⟩ | h) | ⟨haq, hbr⟩ |
                ⟨har, hbq⟩)
              · exact Or.inr (Or.inr (Or.inl h))
              · exact Or.inl ⟨hra, Or.inr hex⟩
              · exact Or.inr (Or.inl ⟨hrb, Or.inr hex⟩)
              · exact Or.inr (Or.inr (Or.inr h))
              · exact Or.inr (Or.inl ⟨hbr.symm, Or.inl haq.symm⟩)
              · exact Or.inl ⟨har.symm, Or.inl hbq.symm⟩
            · rintro (⟨hra, (hqb | hex)⟩ | ⟨hrb, (hqa | hex)⟩ | h | h)
              · exact Or.inr (Or.inr (Or.inr ⟨hra.symm, hqb.symm⟩))
              · exact Or.inr (Or.inl (Or.inl ⟨hra, hex⟩))
              · exact Or.inr (Or.inr (Or.inl ⟨hqa.symm, hrb.symm⟩))
              · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨hrb, hex⟩)))
              · exact Or.inl h
              · exact Or.inr (Or.inl (Or.inr (Or.inr h)))


private theorem perm_rerootAtList {x : V} :
    ∀ (ds : List (Tree V)),
      (∀ c ∈ ds, ∀ t', rerootAt x c = some t' →
        (Tree.vertices t').Perm (Tree.vertices c)) →
      ∀ (c' : Tree V) (rest : List (Tree V)) (p : V),
      rerootAt.rerootAtList x ds = some (c', rest, p) →
      (Tree.vertices c' ++ rest.flatMap Tree.vertices).Perm
        (ds.flatMap Tree.vertices) := by
  intro ds hih c' rest p h
  induction ds generalizing c' rest p with
  | nil =>
      simp [rerootAt.rerootAtList] at h
  | cons c ds ihl =>
      cases hc : rerootAt x c with
      | some c₀ =>
          have heq : rerootAt.rerootAtList x (c :: ds) =
              some (c₀, ds, c.root) := by
            simp [rerootAt.rerootAtList, hc]
          rw [heq] at h
          have hpair : (c₀, ds, c.root) = (c', rest, p) := Option.some.inj h
          obtain ⟨rfl, rfl, -⟩ : c' = c₀ ∧ rest = ds ∧ p = c.root := by
            simp only [Prod.mk.injEq] at hpair
            exact ⟨hpair.1.symm, hpair.2.1.symm, hpair.2.2.symm⟩
          have hic := hih c (by simp) c' hc
          simp only [List.flatMap_cons]
          exact hic.append_right _
      | none =>
          have heq : rerootAt.rerootAtList x (c :: ds) =
              (rerootAt.rerootAtList x ds).map
                (fun (c', rest, p) => (c', c :: rest, p)) := by
            simp [rerootAt.rerootAtList, hc]
          rw [heq] at h
          obtain ⟨⟨c₀, rest₀, p₀⟩, hrest₀, hpair⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨rfl, rfl, -⟩ : c' = c₀ ∧ rest = c :: rest₀ ∧ p = p₀ := by
            simp only [Prod.mk.injEq] at hpair
            exact ⟨hpair.1.symm, hpair.2.1.symm, hpair.2.2.symm⟩
          have hrest := ihl (fun d hd => hih d (List.mem_cons_of_mem c hd))
            c' rest₀ p₀ hrest₀
          simp only [List.flatMap_cons]
          exact ((List.Perm.of_eq (List.append_assoc _ _ _).symm).trans
            ((List.perm_append_comm.append_right _).trans
              (List.Perm.of_eq (List.append_assoc _ _ _)))).trans
            (hrest.append_left _)

/-- Rerooting permutes the vertex list: same vertices, new preorder. -/
public theorem perm_vertices_rerootAt {x : V} :
    ∀ {t t' : Tree V}, rerootAt x t = some t' →
      (Tree.vertices t').Perm (Tree.vertices t) := by
  intro t
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro t' h
      by_cases hr : r = x
      · have heq : rerootAt x (.node r cs) = some (.node r cs) := by
          simp [rerootAt, hr]
        rw [heq] at h
        have hst : (Tree.node r cs : Tree V) = t' := Option.some.inj h
        subst hst
        exact List.Perm.refl _
      · have heq : rerootAt x (.node r cs) =
            match rerootAt.rerootAtList x cs with
            | some (c', rest, p) => graftAt p (.node r rest) c'
            | none => none := by
          simp [rerootAt, hr]
        rw [heq] at h
        cases hlist : rerootAt.rerootAtList x cs with
        | none => simp [hlist] at h
        | some q =>
            obtain ⟨c', rest, p⟩ := q
            rw [hlist] at h
            have hgraft : (Tree.vertices t').Perm
                (Tree.vertices c' ++ Tree.vertices (.node r rest)) :=
              perm_vertices_graftAt h
            have hflat := perm_rerootAtList cs ih c' rest p hlist
            have hnode : ∀ ds : List (Tree V), Tree.vertices (.node r ds) =
                r :: ds.flatMap Tree.vertices := by
              intro ds
              simp [Tree.vertices_node]
            rw [hnode cs]
            rw [hnode rest] at hgraft
            exact hgraft.trans (List.perm_middle.trans (hflat.cons r))


/-- Remove every subtree rooted at `x`, keeping every other node and edge:
the original tree with the `x` subtrees pruned off. Returns `none` exactly
when the root itself is `x` (nothing remains). This is the tree surgery
behind the remainder side of `State.cut`. -/
public def pruneAt (x : V) : Tree V → Option (Tree V)
  | .node r cs => if r = x then none else some (.node r (pruneList x cs))
where
  pruneList (x : V) : List (Tree V) → List (Tree V)
    | [] => []
    | c :: cs =>
        match pruneAt x c with
        | some c' => c' :: pruneList x cs
        | none => pruneList x cs

/-- Pruning at a vertex that does not occur is the identity. -/
public theorem pruneAt_eq_self_of_not_mem {x : V} :
    ∀ {t : Tree V}, x ∉ Tree.vertices t → pruneAt x t = some t := by
  intro t
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro hx
      have hr : r ≠ x := by
        intro hreq
        apply hx
        rw [mem_vertices_node]
        exact Or.inl hreq.symm
      have hlist : ∀ (ds : List (Tree V)),
          (∀ c ∈ ds, pruneAt x c = some c) →
          pruneAt.pruneList x ds = ds := by
        intro ds
        induction ds with
        | nil => intro _; rfl
        | cons c ds ihl =>
            intro hih
            have hc : pruneAt x c = some c := hih c List.mem_cons_self
            have hrest : pruneAt.pruneList x ds = ds :=
              ihl (fun d hd => hih d (List.mem_cons_of_mem c hd))
            simp [pruneAt.pruneList, hc, hrest]
      have hcs : pruneAt.pruneList x cs = cs :=
        hlist cs (fun c hc => ih c hc (fun hxc => hx
          (mem_vertices_node.mpr (Or.inr ⟨c, hc, hxc⟩))))
      simp [pruneAt, hr, hcs]

private theorem mem_flatMap_pruneList {x v : V} :
    ∀ (ds : List (Tree V)),
      (∀ c ∈ ds, ∀ t', pruneAt x c = some t' →
        v ∈ Tree.vertices t' → v ∈ Tree.vertices c ∧ v ≠ x) →
      v ∈ (pruneAt.pruneList x ds).flatMap Tree.vertices →
      v ∈ ds.flatMap Tree.vertices ∧ v ≠ x := by
  intro ds
  induction ds with
  | nil =>
      intro _ hv
      simp [pruneAt.pruneList] at hv
  | cons c ds ihl =>
      intro hih hv
      cases hc : pruneAt x c with
      | some c' =>
          have heq : pruneAt.pruneList x (c :: ds) =
              c' :: pruneAt.pruneList x ds := by
            simp [pruneAt.pruneList, hc]
          rw [heq] at hv
          simp only [List.flatMap_cons, List.mem_append] at hv
          rcases hv with hv | hv
          · have hic := hih c List.mem_cons_self c' hc hv
            refine ⟨?_, hic.2⟩
            rw [List.flatMap_cons, List.mem_append]
            exact Or.inl hic.1
          · have hrest := ihl (fun d hd => hih d (List.mem_cons_of_mem c hd)) hv
            refine ⟨?_, hrest.2⟩
            rw [List.flatMap_cons, List.mem_append]
            exact Or.inr hrest.1
      | none =>
          have heq : pruneAt.pruneList x (c :: ds) =
              pruneAt.pruneList x ds := by
            simp [pruneAt.pruneList, hc]
          rw [heq] at hv
          have hrest := ihl (fun d hd => hih d (List.mem_cons_of_mem c hd)) hv
          refine ⟨?_, hrest.2⟩
          rw [List.flatMap_cons, List.mem_append]
          exact Or.inr hrest.1

/-- Every vertex of the pruned tree was already a vertex of the original
tree, and `x` itself is gone. -/
public theorem mem_vertices_pruneAt {x v : V} :
    ∀ {t t' : Tree V}, pruneAt x t = some t' → v ∈ Tree.vertices t' →
      v ∈ Tree.vertices t ∧ v ≠ x := by
  intro t
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro t' h hv
      by_cases hr : r = x
      · have heq : pruneAt x (.node r cs) = none := by simp [pruneAt, hr]
        rw [heq] at h
        cases h
      · have heq : pruneAt x (.node r cs) =
            some (.node r (pruneAt.pruneList x cs)) := by simp [pruneAt, hr]
        rw [heq] at h
        have hst : (Tree.node r (pruneAt.pruneList x cs) : Tree V) = t' :=
          Option.some.inj h
        subst hst
        rw [mem_vertices_node] at hv
        rcases hv with hv | ⟨c', hc', hv⟩
        · exact ⟨mem_vertices_node.mpr (Or.inl hv), fun hvx => hr (hv ▸ hvx)⟩
        · have hvflat : v ∈ (pruneAt.pruneList x cs).flatMap Tree.vertices :=
            List.mem_flatMap.mpr ⟨c', hc', hv⟩
          have hres := mem_flatMap_pruneList cs ih hvflat
          exact ⟨mem_vertices_node.mpr (Or.inr (by
            rw [List.mem_flatMap] at hres
            exact hres.1)), hres.2⟩

private theorem mem_pruneList_of_pruneAt_some {x : V} :
    ∀ {ds : List (Tree V)} {c c' : Tree V},
      pruneAt x c = some c' → c ∈ ds → c' ∈ pruneAt.pruneList x ds := by
  intro ds
  induction ds with
  | nil =>
      intro c c' _ hmem
      exact absurd hmem (by simp)
  | cons d ds ih =>
      intro c c' hc hmem
      cases hd : pruneAt x d with
      | some d' =>
          have heq : pruneAt.pruneList x (d :: ds) =
              d' :: pruneAt.pruneList x ds := by
            simp [pruneAt.pruneList, hd]
          rw [heq, List.mem_cons]
          rw [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · have hdc : c' = d' := Option.some.inj (hc.symm.trans hd)
            exact Or.inl hdc
          · exact Or.inr (ih hc hmem)
      | none =>
          have heq : pruneAt.pruneList x (d :: ds) =
              pruneAt.pruneList x ds := by
            simp [pruneAt.pruneList, hd]
          rw [heq]
          rw [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · rw [hd] at hc
            cases hc
          · exact ih hc hmem

/-- The vertices on the other side of a prune survive: in a duplicate-free
(valid) tree, every vertex outside the detached subtree at `x` is a vertex
of the pruned remainder. Together with `mem_vertices_pruneAt` this says
pruning partitions the vertex set of a valid tree into the detached
subtree and the remainder, keeping all remaining edges. -/
public theorem mem_vertices_pruneAt_of_mem_not_mem {x v : V} :
    ∀ {t sub t' : Tree V}, (Tree.vertices t).Nodup →
      findSubtree x t = some sub → pruneAt x t = some t' →
      v ∈ Tree.vertices t → v ∉ Tree.vertices sub →
      v ∈ Tree.vertices t' := by
  intro t
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro sub t' hnodup hsub hprune hv hvsub
      have hr : r ≠ x := by
        intro hreq
        have heq : pruneAt x (.node r cs) = none := by simp [pruneAt, hreq]
        rw [heq] at hprune
        cases hprune
      have heq : pruneAt x (.node r cs) =
          some (.node r (pruneAt.pruneList x cs)) := by simp [pruneAt, hr]
      rw [heq] at hprune
      have hst : (Tree.node r (pruneAt.pruneList x cs) : Tree V) = t' :=
        Option.some.inj hprune
      subst hst
      have hsubeq : findSubtree x (.node r cs) =
          findSubtree.findSubtreeList x cs := by simp [findSubtree, hr]
      rw [hsubeq] at hsub
      obtain ⟨c₀, hc₀, hsub₀⟩ := findSubtreeList_eq_some_spec hsub
      have hnodup' : (cs.flatMap Tree.vertices).Nodup := by
        have h := hnodup
        rw [Tree.vertices_node, List.nodup_cons] at h
        exact h.2
      obtain ⟨hnodupC, hpair⟩ := Iff.mp List.nodup_flatMap hnodup'
      have hxc₀ : x ∈ Tree.vertices c₀ := by
        have hxsub : x ∈ Tree.vertices sub := by
          have hroot : sub.root = x := root_findSubtree hsub₀
          rw [← hroot]
          exact root_mem_vertices sub
        exact mem_vertices_findSubtree hsub₀ hxsub
      rw [mem_vertices_node] at hv
      rcases hv with hv | ⟨c, hc, hv⟩
      · exact mem_vertices_node.mpr (Or.inl hv)
      · by_cases hcc₀ : c = c₀
        · subst hcc₀
          cases hc₀p : pruneAt x c with
          | none =>
              cases c with
              | node r₀ cs₀ =>
                  have hr₀ : r₀ = x := by
                    by_contra hr₀
                    have hsome : pruneAt x (.node r₀ cs₀) =
                        some (.node r₀ (pruneAt.pruneList x cs₀)) := by
                      simp [pruneAt, hr₀]
                    rw [hsome] at hc₀p
                    cases hc₀p
                  have hsubt : findSubtree x (.node r₀ cs₀) =
                      some (.node r₀ cs₀) := by simp [findSubtree, hr₀]
                  rw [hsubt] at hsub₀
                  have hst2 : (Tree.node r₀ cs₀ : Tree V) = sub :=
                    Option.some.inj hsub₀
                  subst hst2
                  exact absurd hv hvsub
          | some c' =>
              have hv' := ih c hc (hnodupC c hc) hsub₀ hc₀p hv hvsub
              have hc'mem : c' ∈ pruneAt.pruneList x cs :=
                mem_pruneList_of_pruneAt_some hc₀p hc
              exact mem_vertices_node.mpr (Or.inr ⟨c', hc'mem, hv'⟩)
        · have hdisj : List.Disjoint (Tree.vertices c) (Tree.vertices c₀) := by
            have haux : ∀ (ds : List (Tree V)),
                List.Pairwise (Function.onFun List.Disjoint Tree.vertices) ds →
                ∀ {a b : Tree V}, a ∈ ds → b ∈ ds → a ≠ b →
                List.Disjoint (Tree.vertices a) (Tree.vertices b) := by
              intro ds
              induction ds with
              | nil =>
                  intro _ a b ha _ _
                  exact absurd ha (by simp)
              | cons d ds ihd =>
                  intro hpair' a b ha hb hab
                  obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair'
                  rw [List.mem_cons] at ha hb
                  rcases ha with rfl | ha
                  · rcases hb with rfl | hb
                    · exact absurd rfl hab
                    · exact hhead b hb
                  · rcases hb with rfl | hb
                    · intro y hya hyb
                      exact hhead a ha hyb hya
                    · exact ihd htail ha hb hab
            exact haux cs hpair hc hc₀ hcc₀
          have hxc : x ∉ Tree.vertices c := fun hxc => hdisj hxc hxc₀
          have hself : pruneAt x c = some c :=
            pruneAt_eq_self_of_not_mem hxc
          have hcmem : c ∈ pruneAt.pruneList x cs :=
            mem_pruneList_of_pruneAt_some hself hc
          exact mem_vertices_node.mpr (Or.inr ⟨c, hcmem, hv⟩)

private theorem pruneList_eq_self_of_forall_not_mem {x : V} :
    ∀ {ds : List (Tree V)}, (∀ c ∈ ds, x ∉ Tree.vertices c) →
      pruneAt.pruneList x ds = ds := by
  intro ds
  induction ds with
  | nil => intro _; rfl
  | cons c ds ih =>
      intro h
      have hc : pruneAt x c = some c :=
        pruneAt_eq_self_of_not_mem (h c List.mem_cons_self)
      have hrest : pruneAt.pruneList x ds = ds :=
        ih (fun d hd => h d (List.mem_cons_of_mem c hd))
      simp [pruneAt.pruneList, hc, hrest]

private theorem perm_flatMap_pruneList {x : V} :
    ∀ (ds : List (Tree V)), (ds.flatMap Tree.vertices).Nodup →
      (∀ c ∈ ds, ∀ (sub c' : Tree V), (Tree.vertices c).Nodup →
        findSubtree x c = some sub → pruneAt x c = some c' →
        (Tree.vertices c).Perm (Tree.vertices c' ++ Tree.vertices sub)) →
      ∀ (sub : Tree V), findSubtree.findSubtreeList x ds = some sub →
      (ds.flatMap Tree.vertices).Perm
        ((pruneAt.pruneList x ds).flatMap Tree.vertices ++
          Tree.vertices sub) := by
  intro ds
  induction ds with
  | nil =>
      intro _ _ sub h
      simp [findSubtree.findSubtreeList] at h
  | cons c ds ih =>
      intro hnodup hih sub h
      have hnodupFlat : ((c :: ds).flatMap Tree.vertices).Nodup := hnodup
      rw [List.flatMap_cons] at hnodupFlat
      obtain ⟨hnodupC, hpair⟩ := List.nodup_flatMap.mp hnodup
      have hnodupDs : (ds.flatMap Tree.vertices).Nodup :=
        (List.nodup_append.mp hnodupFlat).2.1
      cases hfindc : findSubtree x c with
      | some s =>
          have hlistEq : findSubtree.findSubtreeList x (c :: ds) = some s := by
            simp [findSubtree.findSubtreeList, hfindc]
          rw [hlistEq] at h
          have hsub : s = sub := Option.some.inj h
          rw [hsub] at hfindc
          have hxsub : x ∈ Tree.vertices sub := by
            have hroot : sub.root = x := root_findSubtree hfindc
            rw [← hroot]
            exact root_mem_vertices sub
          have hxc : x ∈ Tree.vertices c :=
            mem_vertices_findSubtree hfindc hxsub
          have hnotDs : ∀ d ∈ ds, x ∉ Tree.vertices d := by
            intro d hd hxd
            obtain ⟨hhead, -⟩ := List.pairwise_cons.mp hpair
            exact hhead d hd hxc hxd
          have hpruneDs : pruneAt.pruneList x ds = ds :=
            pruneList_eq_self_of_forall_not_mem hnotDs
          cases hprune : pruneAt x c with
          | some c' =>
              have hpermC : (Tree.vertices c).Perm
                  (Tree.vertices c' ++ Tree.vertices sub) :=
                hih c List.mem_cons_self sub c' (hnodupC c List.mem_cons_self)
                  hfindc hprune
              have hlist : pruneAt.pruneList x (c :: ds) =
                  c' :: pruneAt.pruneList x ds := by
                simp [pruneAt.pruneList, hprune]
              rw [hlist, hpruneDs]
              simp only [List.flatMap_cons]
              exact (hpermC.append_right _).trans (perm_rotate3 _ _ _)
          | none =>
              cases c with
              | node r₀ cs₀ =>
                  have hr₀ : r₀ = x := by
                    by_contra hr₀
                    have hsome : pruneAt x (.node r₀ cs₀) =
                        some (.node r₀ (pruneAt.pruneList x cs₀)) := by
                      simp [pruneAt, hr₀]
                    rw [hsome] at hprune
                    cases hprune
                  have hsubt : findSubtree x (.node r₀ cs₀) =
                      some (.node r₀ cs₀) := by simp [findSubtree, hr₀]
                  rw [hsubt] at hfindc
                  have hst : (Tree.node r₀ cs₀ : Tree V) = sub :=
                    Option.some.inj hfindc
                  subst hst
                  have hlist : pruneAt.pruneList x
                      ((Tree.node r₀ cs₀) :: ds) =
                      pruneAt.pruneList x ds := by
                    simp [pruneAt.pruneList, hprune]
                  rw [hlist, hpruneDs]
                  simp only [List.flatMap_cons]
                  exact List.perm_append_comm
      | none =>
          have hlistEq : findSubtree.findSubtreeList x (c :: ds) =
              findSubtree.findSubtreeList x ds := by
            simp [findSubtree.findSubtreeList, hfindc]
          rw [hlistEq] at h
          have hxc : x ∉ Tree.vertices c := by
            intro hxc
            obtain ⟨s, hs⟩ := findSubtree_eq_some_of_mem hxc
            rw [hs] at hfindc
            cases hfindc
          have hprune : pruneAt x c = some c :=
            pruneAt_eq_self_of_not_mem hxc
          have hlist : pruneAt.pruneList x (c :: ds) =
              c :: pruneAt.pruneList x ds := by
            simp [pruneAt.pruneList, hprune]
          have hrest := ih hnodupDs
            (fun d hd => hih d (List.mem_cons_of_mem c hd)) sub h
          rw [hlist]
          simp only [List.flatMap_cons]
          exact (hrest.append_left _).trans
            (List.Perm.of_eq (List.append_assoc _ _ _).symm)

/-- In a duplicate-free tree, pruning at `x` partitions the vertex list
into the remainder and the detached subtree, up to permutation. -/
public theorem perm_vertices_pruneAt {x : V} :
    ∀ {t sub t' : Tree V}, (Tree.vertices t).Nodup →
      findSubtree x t = some sub → pruneAt x t = some t' →
      (Tree.vertices t).Perm (Tree.vertices t' ++ Tree.vertices sub) := by
  intro t
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro sub t' hnodup hsub hprune
      have hr : r ≠ x := by
        intro hreq
        have heq : pruneAt x (.node r cs) = none := by simp [pruneAt, hreq]
        rw [heq] at hprune
        cases hprune
      have heq : pruneAt x (.node r cs) =
          some (.node r (pruneAt.pruneList x cs)) := by simp [pruneAt, hr]
      rw [heq] at hprune
      have hst : (Tree.node r (pruneAt.pruneList x cs) : Tree V) = t' :=
        Option.some.inj hprune
      subst hst
      have hsubeq : findSubtree x (.node r cs) =
          findSubtree.findSubtreeList x cs := by simp [findSubtree, hr]
      rw [hsubeq] at hsub
      have hnodup' : (cs.flatMap Tree.vertices).Nodup := by
        have hh := hnodup
        rw [Tree.vertices_node, List.nodup_cons] at hh
        exact hh.2
      have hflat := perm_flatMap_pruneList cs hnodup' ih sub hsub
      have hnode : ∀ ds : List (Tree V), Tree.vertices (.node r ds) =
          r :: ds.flatMap Tree.vertices := by
        intro ds
        simp [Tree.vertices_node]
      rw [hnode cs, hnode (pruneAt.pruneList x cs)]
      exact (hflat.cons r).trans (List.Perm.of_eq List.cons_append.symm)


/-- Pruning keeps the root of the tree. -/
public theorem root_pruneAt {x : V} {t t' : Tree V}
    (h : pruneAt x t = some t') : t'.root = t.root := by
  cases t with
  | node r cs =>
      by_cases hr : r = x
      · have heq : pruneAt x (.node r cs) = none := by simp [pruneAt, hr]
        rw [heq] at h
        cases h
      · have heq : pruneAt x (.node r cs) =
            some (.node r (pruneAt.pruneList x cs)) := by simp [pruneAt, hr]
        rw [heq] at h
        have hst : (Tree.node r (pruneAt.pruneList x cs) : Tree V) = t' :=
          Option.some.inj h
        rw [← hst]
        rfl

private theorem pruneAt_eq_some_of_root_ne {x : V} {t : Tree V}
    (h : t.root ≠ x) : ∃ t', pruneAt x t = some t' := by
  cases t with
  | node r cs =>
      have hr : r ≠ x := h
      exact ⟨.node r (pruneAt.pruneList x cs), by simp [pruneAt, hr]⟩

private theorem mem_pruneList_spec {x : V} :
    ∀ {ds : List (Tree V)} {c' : Tree V},
      c' ∈ pruneAt.pruneList x ds → ∃ c ∈ ds, pruneAt x c = some c' := by
  intro ds
  induction ds with
  | nil =>
      intro c' h
      simp [pruneAt.pruneList] at h
  | cons d ds ih =>
      intro c' h
      cases hd : pruneAt x d with
      | some d' =>
          have heq : pruneAt.pruneList x (d :: ds) =
              d' :: pruneAt.pruneList x ds := by
            simp [pruneAt.pruneList, hd]
          rw [heq, List.mem_cons] at h
          rcases h with rfl | h
          · exact ⟨d, List.mem_cons_self, hd⟩
          · obtain ⟨c, hc, hpc⟩ := ih h
            exact ⟨c, List.mem_cons_of_mem d hc, hpc⟩
      | none =>
          have heq : pruneAt.pruneList x (d :: ds) =
              pruneAt.pruneList x ds := by
            simp [pruneAt.pruneList, hd]
          rw [heq] at h
          obtain ⟨c, hc, hpc⟩ := ih h
          exact ⟨c, List.mem_cons_of_mem d hc, hpc⟩

/-- Pruning keeps every edge whose endpoints survive: in a duplicate-free
tree, an edge of the original tree with both endpoints in the pruned
remainder is an edge of the remainder. Together with
`mem_vertices_pruneAt` (which gives the converse inclusion of vertices)
this specifies `pruneAt` at edge level on the surviving vertices. -/
public theorem adjacent_pruneAt_of_mem_mem {a b x : V} :
    ∀ {t t' : Tree V}, (Tree.vertices t).Nodup →
      pruneAt x t = some t' → Adjacent a b t →
      a ∈ Tree.vertices t' → b ∈ Tree.vertices t' →
      Adjacent a b t' := by
  intro t
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro t' hnodup hprune hadj ha hb
      have hr : r ≠ x := by
        intro hreq
        have heq : pruneAt x (.node r cs) = none := by simp [pruneAt, hreq]
        rw [heq] at hprune
        cases hprune
      have heq : pruneAt x (.node r cs) =
          some (.node r (pruneAt.pruneList x cs)) := by simp [pruneAt, hr]
      rw [heq] at hprune
      have hst : (Tree.node r (pruneAt.pruneList x cs) : Tree V) = t' :=
        Option.some.inj hprune
      subst hst
      have hflat : (cs.flatMap Tree.vertices).Nodup := by
        rw [Tree.vertices_node, List.nodup_cons] at hnodup
        exact hnodup.2
      obtain ⟨hnodupC, -⟩ := List.nodup_flatMap.mp hflat
      rw [adjacent_node] at hadj ⊢
      rcases hadj with ⟨hr2, c, hc, hroot⟩ | ⟨hr2, c, hc, hroot⟩ | hadj
      · have hbx : b ≠ x := (mem_vertices_pruneAt heq hb).2
        obtain ⟨c', hc'⟩ := pruneAt_eq_some_of_root_ne (t := c) (by
          rw [hroot]
          exact hbx)
        refine Or.inl ⟨hr2, c', mem_pruneList_of_pruneAt_some hc' hc, ?_⟩
        rw [root_pruneAt hc']
        exact hroot
      · have hax : a ≠ x := (mem_vertices_pruneAt heq ha).2
        obtain ⟨c', hc'⟩ := pruneAt_eq_some_of_root_ne (t := c) (by
          rw [hroot]
          exact hax)
        refine Or.inr (Or.inl ⟨hr2, c',
          mem_pruneList_of_pruneAt_some hc' hc, ?_⟩)
        rw [root_pruneAt hc']
        exact hroot
      · rw [adjacentList_iff] at hadj ⊢
        obtain ⟨c, hc, hadj⟩ := hadj
        have key : ∀ {v : V}, v ∈ Tree.vertices c →
            v ∈ Tree.vertices (.node r (pruneAt.pruneList x cs)) →
            ∃ c', c' ∈ pruneAt.pruneList x cs ∧ pruneAt x c = some c' ∧
              v ∈ Tree.vertices c' := by
          intro v hvc hv
          rw [mem_vertices_node] at hv
          rcases hv with hvr | ⟨c', hc', hvc'⟩
          · exfalso
            rw [hvr] at hvc
            exact root_not_mem_flatMap_children hnodup
              (List.mem_flatMap.mpr ⟨c, hc, hvc⟩)
          · obtain ⟨c₁, hc₁, hpc₁⟩ := mem_pruneList_spec hc'
            have hvc₁ : v ∈ Tree.vertices c₁ :=
              (mem_vertices_pruneAt hpc₁ hvc').1
            have hc₁c : c₁ = c :=
              eq_of_mem_vertices_of_nodup_flatMap hflat hc₁ hc hvc₁ hvc
            subst hc₁c
            exact ⟨c', hc', hpc₁, hvc'⟩
        obtain ⟨c₁', hc₁'m, hpc₁, hac₁'⟩ := key hadj.mem_left ha
        obtain ⟨c₂', hc₂'m, hpc₂, hbc₂'⟩ := key hadj.mem_right hb
        have hcc : c₁' = c₂' := Option.some.inj (hpc₁.symm.trans hpc₂)
        subst hcc
        exact Or.inr (Or.inr ⟨c₁', hc₁'m,
          ih c hc (hnodupC c hc) hpc₁ hadj hac₁' hbc₂'⟩)

/-- The path from the root of a tree down to `x`, root first, if `x` occurs in
the tree. This is the preferred path installed by `access x`. -/
public def rootPath (x : V) : Tree V → Option (List V)
  | .node r cs =>
      if r = x then some [r] else (rootPathList x cs).map (fun p => r :: p)
where
  rootPathList (x : V) : List (Tree V) → Option (List V)
    | [] => none
    | c :: cs =>
        match rootPath x c with
        | some p => some p
        | none => rootPathList x cs

private theorem rootPathList_eq_some_spec {x : V} :
    ∀ {cs : List (Tree V)} {p : List V},
      rootPath.rootPathList x cs = some p → ∃ c ∈ cs, rootPath x c = some p := by
  intro cs
  induction cs with
  | nil => intro p h; simp [rootPath.rootPathList] at h
  | cons c cs ih =>
      intro p h
      cases hc : rootPath x c with
      | some p' =>
          have heq : rootPath.rootPathList x (c :: cs) = some p' := by
            simp [rootPath.rootPathList, hc]
          rw [heq] at h
          have hpp : p' = p := Option.some.inj h
          exact ⟨c, by simp, by rw [hc, hpp]⟩
      | none =>
          have heq : rootPath.rootPathList x (c :: cs) =
              rootPath.rootPathList x cs := by
            simp [rootPath.rootPathList, hc]
          rw [heq] at h
          obtain ⟨c', hc', hfind⟩ := ih h
          exact ⟨c', List.mem_cons_of_mem c hc', hfind⟩

private theorem rootPathList_eq_some_of_exists {x : V} :
    ∀ {cs : List (Tree V)},
      (∃ c ∈ cs, ∃ p, rootPath x c = some p) →
      ∃ p, rootPath.rootPathList x cs = some p := by
  intro cs
  induction cs with
  | nil =>
      intro h
      obtain ⟨c, hmem, -⟩ := h
      exact absurd hmem (by simp)
  | cons c cs ih =>
      intro h
      cases hc : rootPath x c with
      | some p => exact ⟨p, by simp [rootPath.rootPathList, hc]⟩
      | none =>
          obtain ⟨c', hmem, p, hp⟩ := h
          have htail : ∃ c ∈ cs, ∃ p, rootPath x c = some p := by
            rw [List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · rw [hc] at hp
              cases hp
            · exact ⟨c', hmem, p, hp⟩
          obtain ⟨p', hp'⟩ := ih htail
          exact ⟨p', by simp [rootPath.rootPathList, hc, hp']⟩

public theorem rootPath_eq_some_of_mem {x : V} {t : Tree V}
    (hx : x ∈ Tree.vertices t) : ∃ p, rootPath x t = some p := by
  revert hx
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro hx
      by_cases hr : r = x
      · exact ⟨[r], by simp [rootPath, hr]⟩
      · have hchild : ∃ c ∈ cs, ∃ p, rootPath x c = some p := by
          rw [mem_vertices_node] at hx
          rcases hx with hx | ⟨c, hc, hxc⟩
          · exact absurd hx.symm hr
          · obtain ⟨p, hp⟩ := ih c hc hxc
            exact ⟨c, hc, p, hp⟩
        obtain ⟨p, hp⟩ := rootPathList_eq_some_of_exists hchild
        exact ⟨r :: p, by simp [rootPath, hr, hp]⟩

private theorem rootPath_node_cases {x r : V} {cs : List (Tree V)} {p : List V}
    (h : rootPath x (.node r cs) = some p) :
    (r = x ∧ p = [r]) ∨ (r ≠ x ∧ ∃ c ∈ cs, ∃ p', rootPath x c = some p' ∧ p = r :: p') := by
  by_cases hr : r = x
  · have heq : rootPath x (.node r cs) = some [r] := by simp [rootPath, hr]
    rw [heq] at h
    exact Or.inl ⟨hr, (Option.some.inj h).symm⟩
  · have heq : rootPath x (.node r cs) =
        (rootPath.rootPathList x cs).map (fun q => r :: q) := by simp [rootPath, hr]
    rw [heq] at h
    obtain ⟨p', hp', hp⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨c, hc, hfind⟩ := rootPathList_eq_some_spec hp'
    exact Or.inr ⟨hr, c, hc, p', hfind, hp.symm⟩

/-- The deepest vertex of a root path (its last entry) is the target vertex. -/
public theorem getLast?_rootPath {x : V} {t : Tree V} {p : List V}
    (h : rootPath x t = some p) : p.getLast? = some x := by
  revert h
  induction t using Tree.children_ind generalizing p with
  | node r cs ih =>
      intro h
      rcases rootPath_node_cases h with ⟨hr, hp⟩ | ⟨-, c, hc, p', hfind, hp⟩
      · rw [hp]
        simp [hr]
      · rw [hp]
        exact getLast?_cons_of_getLast?_eq_some (ih c hc hfind)

/-- The first vertex of a root path is the root of the tree. -/
public theorem head?_rootPath {x : V} {t : Tree V} {p : List V}
    (h : rootPath x t = some p) : p.head? = some t.root := by
  cases t with
  | node r cs =>
      rcases rootPath_node_cases h with ⟨-, rfl⟩ | ⟨-, -, -, -, -, rfl⟩
      · rfl
      · rfl

/-- Every vertex on a root path is a vertex of the tree. -/
public theorem mem_rootPath {x v : V} {t : Tree V} {p : List V}
    (h : rootPath x t = some p) (hv : v ∈ p) : v ∈ Tree.vertices t := by
  revert h hv
  induction t using Tree.children_ind generalizing p with
  | node r cs ih =>
      intro h hv
      rcases rootPath_node_cases h with ⟨-, hp⟩ | ⟨-, c, hc, p', hfind, hp⟩
      · rw [hp] at hv
        rw [List.mem_singleton] at hv
        exact mem_vertices_node.mpr (Or.inl hv)
      · rw [hp] at hv
        rw [List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact mem_vertices_node.mpr (Or.inl rfl)
        · exact mem_vertices_node.mpr (Or.inr ⟨c, hc, ih c hc hfind hv⟩)

public theorem rootPath_ne_nil {x : V} {t : Tree V} {p : List V}
    (h : rootPath x t = some p) : p ≠ [] := by
  intro hp
  have hlast := getLast?_rootPath h
  rw [hp] at hlast
  simp at hlast

/-- A root path in a duplicate-free tree has distinct vertices. -/
public theorem nodup_rootPath {x : V} :
    ∀ {t : Tree V} {p : List V}, (Tree.vertices t).Nodup →
      rootPath x t = some p → p.Nodup := by
  intro t
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro p hnodup h
      rcases rootPath_node_cases h with ⟨-, rfl⟩ | ⟨-, c, hc, p', hfind, rfl⟩
      · simp
      · have hflat : (cs.flatMap Tree.vertices).Nodup := by
          rw [Tree.vertices_node, List.nodup_cons] at hnodup
          exact hnodup.2
        obtain ⟨hnodupC, -⟩ := List.nodup_flatMap.mp hflat
        rw [List.nodup_cons]
        refine ⟨?_, ih c hc (hnodupC c hc) hfind⟩
        intro hrp
        have hrc : r ∈ Tree.vertices c := mem_rootPath hfind hrp
        exact root_not_mem_flatMap_children hnodup
          (List.mem_flatMap.mpr ⟨c, hc, hrc⟩)

/-- Consecutive vertices of a root path are joined by a parent-child edge
of the tree. -/
public theorem isChain_adjacent_rootPath {x : V} :
    ∀ {t : Tree V} {p : List V}, rootPath x t = some p →
      p.IsChain (fun a b => Adjacent a b t) := by
  intro t
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro p h
      rcases rootPath_node_cases h with ⟨-, rfl⟩ | ⟨-, c, hc, p', hfind, rfl⟩
      · exact List.isChain_singleton r
      · have hchain : p'.IsChain (fun a b => Adjacent a b c) :=
          ih c hc hfind
        have hlift : p'.IsChain
            (fun a b => Adjacent a b (.node r cs)) :=
          hchain.imp_of_mem_imp (fun a b _ _ hadj => by
            rw [adjacent_node]
            exact Or.inr (Or.inr (adjacentList_iff.mpr ⟨c, hc, hadj⟩)))
        refine List.IsChain.cons hlift ?_
        intro b hb
        have hhead : p'.head? = some c.root := head?_rootPath hfind
        rw [hhead] at hb
        have hb2 : c.root = b := by simpa using hb
        subst hb2
        rw [adjacent_node]
        exact Or.inl ⟨rfl, c, hc, rfl⟩

/-- Directed parent-child adjacency in a represented tree: `a` is the parent
of `b` somewhere in the tree. Preferred edges are directed this way, from a
node to its preferred child. -/
public def ParentChild (a b : V) : Tree V → Prop
  | .node r cs => (r = a ∧ ∃ c ∈ cs, c.root = b) ∨ ParentChildList a b cs
where
  /-- Directed parent-child adjacency inside one of a list of subtrees. -/
  ParentChildList (a b : V) : List (Tree V) → Prop
    | [] => False
    | c :: cs => ParentChild a b c ∨ ParentChildList a b cs

omit [DecidableEq V] in
public theorem parentChild_node {a b r : V} {cs : List (Tree V)} :
    ParentChild a b (.node r cs) ↔
      (r = a ∧ ∃ c ∈ cs, c.root = b) ∨ ParentChild.ParentChildList a b cs :=
  Iff.rfl

omit [DecidableEq V] in
public theorem parentChildList_iff {a b : V} :
    ∀ {cs : List (Tree V)},
      ParentChild.ParentChildList a b cs ↔ ∃ c ∈ cs, ParentChild a b c := by
  intro cs
  induction cs with
  | nil => simp [ParentChild.ParentChildList]
  | cons c cs ih =>
      have hcons : ParentChild.ParentChildList a b (c :: cs) ↔
          ParentChild a b c ∨ ParentChild.ParentChildList a b cs := Iff.rfl
      rw [hcons, ih]
      constructor
      · rintro (h | ⟨d, hd, hadj⟩)
        · exact ⟨c, List.mem_cons_self, h⟩
        · exact ⟨d, List.mem_cons_of_mem c hd, hadj⟩
      · rintro ⟨d, hd, hadj⟩
        rw [List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact Or.inl hadj
        · exact Or.inr ⟨d, hd, hadj⟩

omit [DecidableEq V] in
/-- A directed parent-child edge is an undirected edge. -/
public theorem ParentChild.adjacent {a b : V} :
    ∀ {t : Tree V}, ParentChild a b t → Adjacent a b t := by
  intro t
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro h
      rw [parentChild_node] at h
      rw [adjacent_node]
      rcases h with ⟨hr, hc⟩ | h
      · exact Or.inl ⟨hr, hc⟩
      · rw [parentChildList_iff] at h
        obtain ⟨c, hc, hadj⟩ := h
        exact Or.inr (Or.inr (adjacentList_iff.mpr ⟨c, hc, ih c hc hadj⟩))

omit [DecidableEq V] in
/-- The endpoints of a directed parent-child edge are vertices of the tree. -/
public theorem ParentChild.mem_left {a b : V} {t : Tree V}
    (h : ParentChild a b t) : a ∈ Tree.vertices t :=
  h.adjacent.mem_left

omit [DecidableEq V] in
/-- The child endpoint of a directed edge is a vertex of the tree. -/
public theorem ParentChild.mem_right {a b : V} {t : Tree V}
    (h : ParentChild a b t) : b ∈ Tree.vertices t :=
  h.adjacent.mem_right

/-- Consecutive vertices of a root path are joined by a directed
parent-child edge of the tree, from parent to child. -/
public theorem isChain_parentChild_rootPath {x : V} :
    ∀ {t : Tree V} {p : List V}, rootPath x t = some p →
      p.IsChain (fun a b => ParentChild a b t) := by
  intro t
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro p h
      rcases rootPath_node_cases h with ⟨-, rfl⟩ | ⟨-, c, hc, p', hfind, rfl⟩
      · exact List.isChain_singleton r
      · have hchain : p'.IsChain (fun a b => ParentChild a b c) :=
          ih c hc hfind
        have hlift : p'.IsChain
            (fun a b => ParentChild a b (.node r cs)) :=
          hchain.imp_of_mem_imp (fun a b _ _ hadj => by
            rw [parentChild_node]
            exact Or.inr (parentChildList_iff.mpr ⟨c, hc, hadj⟩))
        refine List.IsChain.cons hlift ?_
        intro b hb
        have hhead : p'.head? = some c.root := head?_rootPath hfind
        rw [hhead] at hb
        have hb2 : c.root = b := by simpa using hb
        subst hb2
        rw [parentChild_node]
        exact Or.inl ⟨rfl, c, hc, rfl⟩

/-- The directed edges of a vertex path: consecutive pairs, parent first.
The preferred edges installed by `access x` are `pathEdges` of the
root-to-`x` path. -/
public def pathEdges : List V → List (V × V)
  | [] => []
  | [_] => []
  | a :: b :: rest => (a, b) :: pathEdges (b :: rest)

omit [DecidableEq V] in
private theorem pathEdges_cons_cons (a b : V) (rest : List V) :
    pathEdges (a :: b :: rest) = (a, b) :: pathEdges (b :: rest) := by
  simp [pathEdges]

omit [DecidableEq V] in
private theorem fst_mem_of_mem_pathEdges :
    ∀ {p : List V} {e : V × V}, e ∈ pathEdges p → e.1 ∈ p := by
  intro p
  induction p with
  | nil => intro e he; simp [pathEdges] at he
  | cons a p ih =>
      cases p with
      | nil => intro e he; simp [pathEdges] at he
      | cons b rest =>
          intro e he
          rw [pathEdges_cons_cons, List.mem_cons] at he
          rcases he with rfl | he
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem a (ih he)

omit [DecidableEq V] in
private theorem snd_mem_of_mem_pathEdges :
    ∀ {p : List V} {e : V × V}, e ∈ pathEdges p → e.2 ∈ p := by
  intro p
  induction p with
  | nil => intro e he; simp [pathEdges] at he
  | cons a p ih =>
      cases p with
      | nil => intro e he; simp [pathEdges] at he
      | cons b rest =>
          intro e he
          rw [pathEdges_cons_cons, List.mem_cons] at he
          rcases he with rfl | he
          · exact List.mem_cons_of_mem a List.mem_cons_self
          · exact List.mem_cons_of_mem a (ih he)

omit [DecidableEq V] in
private theorem mem_pathEdges_of_isChain {R : V → V → Prop} :
    ∀ {p : List V}, p.IsChain R → ∀ {e : V × V}, e ∈ pathEdges p →
      R e.1 e.2 := by
  intro p
  induction p with
  | nil => intro _ e he; simp [pathEdges] at he
  | cons a p ih =>
      cases p with
      | nil => intro _ e he; simp [pathEdges] at he
      | cons b rest =>
          intro hchain e he
          have h2 := List.isChain_cons_cons.mp hchain
          rw [pathEdges_cons_cons, List.mem_cons] at he
          rcases he with rfl | he
          · exact h2.1
          · exact ih h2.2 he

omit [DecidableEq V] in
private theorem nodup_pathEdges :
    ∀ {p : List V}, p.Nodup → (pathEdges p).Nodup := by
  intro p
  induction p with
  | nil => intro _; simp [pathEdges]
  | cons a p ih =>
      cases p with
      | nil => intro _; simp [pathEdges]
      | cons b rest =>
          intro h
          have htail : (b :: rest).Nodup := (List.nodup_cons.mp h).2
          rw [pathEdges_cons_cons, List.nodup_cons]
          refine ⟨?_, ih htail⟩
          intro hmem
          have h1 : a ∈ b :: rest := fst_mem_of_mem_pathEdges hmem
          exact (List.nodup_cons.mp h).1 h1

omit [DecidableEq V] in
private theorem eq_of_mem_pathEdges :
    ∀ {p : List V}, p.Nodup → ∀ {e₁ e₂ : V × V}, e₁ ∈ pathEdges p →
      e₂ ∈ pathEdges p → e₁.1 = e₂.1 → e₁ = e₂ := by
  intro p
  induction p with
  | nil => intro _ e₁ e₂ he; simp [pathEdges] at he
  | cons a p ih =>
      cases p with
      | nil => intro _ e₁ e₂ he; simp [pathEdges] at he
      | cons b rest =>
          intro h e₁ e₂ he₁ he₂ hf
          have htail : (b :: rest).Nodup := (List.nodup_cons.mp h).2
          have hna : a ∉ b :: rest := (List.nodup_cons.mp h).1
          rw [pathEdges_cons_cons, List.mem_cons] at he₁ he₂
          rcases he₁ with rfl | he₁ <;> rcases he₂ with rfl | he₂
          · rfl
          · exfalso
            have h1 : e₂.1 ∈ b :: rest := fst_mem_of_mem_pathEdges he₂
            rw [← hf] at h1
            exact hna h1
          · exfalso
            have h1 : e₁.1 ∈ b :: rest := fst_mem_of_mem_pathEdges he₁
            rw [hf] at h1
            exact hna h1
          · exact ih htail he₁ he₂ hf

omit [DecidableEq V] in
private theorem mem_pathEdges_cons_tail {a : V} {p : List V} {e : V × V}
    (h : e ∈ pathEdges p) : e ∈ pathEdges (a :: p) := by
  cases p with
  | nil => simp [pathEdges] at h
  | cons b rest =>
      rw [pathEdges_cons_cons]
      exact List.mem_cons_of_mem _ h

omit [DecidableEq V] in
private theorem mem_pathEdges_of_mem_cons {a : V} {p : List V} {e : V × V}
    (h : e.1 ≠ a) (hmem : e ∈ pathEdges (a :: p)) : e ∈ pathEdges p := by
  cases p with
  | nil => simp [pathEdges] at hmem
  | cons b rest =>
      rw [pathEdges_cons_cons, List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · exfalso
        have h1 : e.1 = (a, b).1 := congrArg Prod.fst heq
        exact h h1
      · exact hmem

/-- The preferred-path decomposition of one represented tree, given a list
of preferred (solid) edges `edges` directed from parent to preferred child.
Returns `(down, rest)`: `down` is the preferred path starting at the root of
the tree and following preferred edges downward, and `rest` is the list of
all other preferred paths of the tree. When a node has several preferred
children in `edges` (excluded in valid states by the at-most-one condition),
the first one in child order extends the downward path and the others head
their own paths in `rest`. -/
public def decomp (edges : List (V × V)) : Tree V → List V × List (List V)
  | .node r cs =>
      match decompList edges r cs with
      | (ext, rest) => (r :: ext, rest)
where
  /-- Combine the decompositions of the children of `r`: returns the
  downward continuation below `r` (the root path of the preferred child, or
  `[]` when no child is preferred) and every other path below `r`. -/
  decompList (edges : List (V × V)) (r : V) :
      List (Tree V) → List V × List (List V)
    | [] => ([], [])
    | c :: cs =>
        match decomp edges c, decompList edges r cs with
        | (cdown, crest), (ext, rest) =>
            if (r, c.root) ∈ edges then
              (cdown, crest ++ if ext = [] then rest else ext :: rest)
            else
              (ext, (cdown :: crest) ++ rest)

/-- All preferred paths of one represented tree under the preferred-edge
list `edges`: the downward path from the root, then every other path. -/
public def treePaths (edges : List (V × V)) (t : Tree V) : List (List V) :=
  (decomp edges t).1 :: (decomp edges t).2

/-- The downward preferred path of a tree starts at the root of the tree. -/
public theorem decomp_fst_head? (edges : List (V × V)) (t : Tree V) :
    (decomp edges t).1.head? = some t.root := by
  cases t with
  | node r cs =>
      obtain ⟨ext, rest, hdl⟩ : ∃ a b,
          decomp.decompList edges r cs = (a, b) := ⟨_, _, rfl⟩
      have heq : decomp edges (.node r cs) = (r :: ext, rest) := by
        simp [decomp, hdl]
      simp [heq]

private theorem decompList_fst_eq_nil_or {edges : List (V × V)} {r : V} :
    ∀ (ds : List (Tree V)), (decomp.decompList edges r ds).1 = [] ∨
      ∃ c ∈ ds, (r, c.root) ∈ edges ∧
        (decomp.decompList edges r ds).1 = (decomp edges c).1 := by
  intro ds
  induction ds with
  | nil => exact Or.inl (by simp [decomp.decompList])
  | cons c cs ih =>
      obtain ⟨cdown, crest, hc⟩ : ∃ a b, decomp edges c = (a, b) :=
        ⟨_, _, rfl⟩
      obtain ⟨ext, rest, hcs⟩ : ∃ a b,
          decomp.decompList edges r cs = (a, b) := ⟨_, _, rfl⟩
      by_cases hmem : (r, c.root) ∈ edges
      · have heq : decomp.decompList edges r (c :: cs) =
            (cdown, crest ++ if ext = [] then rest else ext :: rest) := by
          simp [decomp.decompList, hc, hcs, hmem]
        exact Or.inr ⟨c, List.mem_cons_self, hmem, by rw [heq, hc]⟩
      · have heq : decomp.decompList edges r (c :: cs) =
            (ext, (cdown :: crest) ++ rest) := by
          simp [decomp.decompList, hc, hcs, hmem]
        rcases ih with hnil | ⟨c', hc', hmem', hext⟩
        · rw [hcs] at hnil
          have hext : ext = [] := hnil
          exact Or.inl (by rw [heq]; exact hext)
        · rw [hcs] at hext
          exact Or.inr ⟨c', List.mem_cons_of_mem c hc', hmem',
            by rw [heq]; exact hext⟩

private theorem decompList_mem_snd {edges : List (V × V)} {r : V} :
    ∀ (ds : List (Tree V)) {p : List V},
      p ∈ (decomp.decompList edges r ds).2 →
      ∃ c ∈ ds, p ∈ treePaths edges c := by
  intro ds
  induction ds with
  | nil =>
      intro p hp
      simp [decomp.decompList] at hp
  | cons c cs ih =>
      obtain ⟨cdown, crest, hc⟩ : ∃ a b, decomp edges c = (a, b) :=
        ⟨_, _, rfl⟩
      obtain ⟨ext, rest, hcs⟩ : ∃ a b,
          decomp.decompList edges r cs = (a, b) := ⟨_, _, rfl⟩
      intro p hp
      by_cases hmem : (r, c.root) ∈ edges
      · have heq : decomp.decompList edges r (c :: cs) =
            (cdown, crest ++ if ext = [] then rest else ext :: rest) := by
          simp [decomp.decompList, hc, hcs, hmem]
        rw [heq] at hp
        have hp2 : p ∈ crest ++ (if ext = [] then rest else ext :: rest) :=
          hp
        rw [List.mem_append] at hp2
        rcases hp2 with hp2 | hp2
        · refine ⟨c, List.mem_cons_self, ?_⟩
          change p ∈ (decomp edges c).1 :: (decomp edges c).2
          rw [List.mem_cons]
          exact Or.inr (by rw [hc]; exact hp2)
        · by_cases hext : ext = []
          · rw [ite_eq_left hext] at hp2
            have hp3 : p ∈ (decomp.decompList edges r cs).2 := by
              rw [hcs]; exact hp2
            obtain ⟨c', hc', hpc'⟩ := ih hp3
            exact ⟨c', List.mem_cons_of_mem c hc', hpc'⟩
          · rw [ite_eq_right hext, List.mem_cons] at hp2
            rcases hp2 with hpe | hp2
            · rw [hpe]
              rcases decompList_fst_eq_nil_or cs with hnil |
                ⟨c', hc', -, hext2⟩
              · rw [hcs] at hnil
                have h1 : ext = [] := hnil
                exact absurd h1 hext
              · rw [hcs] at hext2
                refine ⟨c', List.mem_cons_of_mem c hc', ?_⟩
                change ext ∈ (decomp edges c').1 :: (decomp edges c').2
                rw [List.mem_cons]
                exact Or.inl hext2
            · have hp3 : p ∈ (decomp.decompList edges r cs).2 := by
                rw [hcs]; exact hp2
              obtain ⟨c', hc', hpc'⟩ := ih hp3
              exact ⟨c', List.mem_cons_of_mem c hc', hpc'⟩
      · have heq : decomp.decompList edges r (c :: cs) =
            (ext, (cdown :: crest) ++ rest) := by
          simp [decomp.decompList, hc, hcs, hmem]
        rw [heq] at hp
        have hp2 : p ∈ (cdown :: crest) ++ rest := hp
        rw [List.mem_append] at hp2
        rcases hp2 with hp2 | hp2
        · rw [List.mem_cons] at hp2
          rcases hp2 with hpe | hp2
          · rw [hpe]
            refine ⟨c, List.mem_cons_self, ?_⟩
            change cdown ∈ (decomp edges c).1 :: (decomp edges c).2
            rw [List.mem_cons]
            exact Or.inl (by rw [hc])
          · refine ⟨c, List.mem_cons_self, ?_⟩
            change p ∈ (decomp edges c).1 :: (decomp edges c).2
            rw [List.mem_cons]
            exact Or.inr (by rw [hc]; exact hp2)
        · have hp3 : p ∈ (decomp.decompList edges r cs).2 := by
            rw [hcs]; exact hp2
          obtain ⟨c', hc', hpc'⟩ := ih hp3
          exact ⟨c', List.mem_cons_of_mem c hc', hpc'⟩

private theorem decompList_fst_eq_nil {edges : List (V × V)} {r : V} :
    ∀ (ds : List (Tree V)), (∀ c ∈ ds, (r, c.root) ∉ edges) →
      (decomp.decompList edges r ds).1 = [] := by
  intro ds
  induction ds with
  | nil => intro _; simp [decomp.decompList]
  | cons c cs ih =>
      intro h
      obtain ⟨cdown, crest, hc⟩ : ∃ a b, decomp edges c = (a, b) :=
        ⟨_, _, rfl⟩
      obtain ⟨ext, rest, hcs⟩ : ∃ a b,
          decomp.decompList edges r cs = (a, b) := ⟨_, _, rfl⟩
      have hnot : (r, c.root) ∉ edges := h c List.mem_cons_self
      have heq : decomp.decompList edges r (c :: cs) =
          (ext, (cdown :: crest) ++ rest) := by
        simp [decomp.decompList, hc, hcs, hnot]
      have hih := ih (fun c' hc' => h c' (List.mem_cons_of_mem c hc'))
      rw [hcs] at hih
      rw [heq]
      exact hih

private theorem decompList_fst_eq {edges : List (V × V)} {r : V}
    {c₀ : Tree V} :
    ∀ (ds : List (Tree V)), c₀ ∈ ds → (r, c₀.root) ∈ edges →
      (∀ c ∈ ds, (r, c.root) ∈ edges → c = c₀) →
      (decomp.decompList edges r ds).1 = (decomp edges c₀).1 := by
  intro ds
  induction ds with
  | nil => intro hmem; simp at hmem
  | cons c cs ih =>
      intro hmem hEdge huniq
      obtain ⟨cdown, crest, hc⟩ : ∃ a b, decomp edges c = (a, b) :=
        ⟨_, _, rfl⟩
      obtain ⟨ext, rest, hcs⟩ : ∃ a b,
          decomp.decompList edges r cs = (a, b) := ⟨_, _, rfl⟩
      by_cases hcc : c = c₀
      · have hEdgeC : (r, c.root) ∈ edges := by
          rw [hcc]; exact hEdge
        have heq : decomp.decompList edges r (c :: cs) =
            (cdown, crest ++ if ext = [] then rest else ext :: rest) := by
          simp [decomp.decompList, hc, hcs, hEdgeC]
        rw [heq, ← hcc, hc]
      · have hc₀cs : c₀ ∈ cs := by
          rw [List.mem_cons] at hmem
          rcases hmem with h | h
          · exact absurd h.symm hcc
          · exact h
        have hnot : (r, c.root) ∉ edges :=
          fun hm => hcc (huniq c List.mem_cons_self hm)
        have heq : decomp.decompList edges r (c :: cs) =
            (ext, (cdown :: crest) ++ rest) := by
          simp [decomp.decompList, hc, hcs, hnot]
        have hih := ih hc₀cs hEdge
          (fun c' hc' hm => huniq c' (List.mem_cons_of_mem c hc') hm)
        rw [hcs] at hih
        rw [heq]
        exact hih

private theorem decompList_perm {edges : List (V × V)} {r : V} :
    ∀ (ds : List (Tree V)),
      (∀ c ∈ ds, ((decomp edges c).1 ++ (decomp edges c).2.flatMap id).Perm
        (Tree.vertices c)) →
      ((decomp.decompList edges r ds).1 ++
        (decomp.decompList edges r ds).2.flatMap id).Perm
        (ds.flatMap Tree.vertices) := by
  intro ds
  induction ds with
  | nil => intro _; simp [decomp.decompList]
  | cons c cs ih =>
      intro hih
      obtain ⟨cdown, crest, hc⟩ : ∃ a b, decomp edges c = (a, b) :=
        ⟨_, _, rfl⟩
      obtain ⟨ext, rest, hcs⟩ : ∃ a b,
          decomp.decompList edges r cs = (a, b) := ⟨_, _, rfl⟩
      have hcperm : (cdown ++ crest.flatMap id).Perm (Tree.vertices c) := by
        have h := hih c List.mem_cons_self
        rw [hc] at h
        exact h
      have hcsperm : (ext ++ rest.flatMap id).Perm
          (cs.flatMap Tree.vertices) := by
        have h := ih (fun d hd => hih d (List.mem_cons_of_mem c hd))
        rw [hcs] at h
        exact h
      by_cases hmem : (r, c.root) ∈ edges
      · have heq : decomp.decompList edges r (c :: cs) =
            (cdown, crest ++ if ext = [] then rest else ext :: rest) := by
          simp [decomp.decompList, hc, hcs, hmem]
        have hX : (if ext = [] then rest else ext :: rest).flatMap id =
            ext ++ rest.flatMap id := by
          by_cases hext : ext = []
          · simp [hext]
          · simp [hext, List.flatMap_cons]
        rw [heq]
        change (cdown ++ (crest ++
          (if ext = [] then rest else ext :: rest)).flatMap id).Perm _
        rw [List.flatMap_append, hX, List.flatMap_cons,
          ← List.append_assoc]
        exact hcperm.append hcsperm
      · have heq : decomp.decompList edges r (c :: cs) =
            (ext, (cdown :: crest) ++ rest) := by
          simp [decomp.decompList, hc, hcs, hmem]
        rw [heq]
        change (ext ++ ((cdown :: crest) ++ rest).flatMap id).Perm _
        rw [List.flatMap_append, List.flatMap_cons, List.flatMap_cons]
        exact ((List.Perm.of_eq
            (List.append_assoc ext (cdown ++ crest.flatMap id)
              (rest.flatMap id)).symm).trans
          (List.perm_append_comm.append_right _)).trans
          ((List.Perm.of_eq (List.append_assoc _ _ _)).trans
            (hcperm.append hcsperm))

/-- The decomposition of a tree partitions its vertices: the flattened
paths are a permutation of the vertex list, for every preferred-edge list. -/
public theorem decomp_perm (edges : List (V × V)) (t : Tree V) :
    ((decomp edges t).1 ++ (decomp edges t).2.flatMap id).Perm
      (Tree.vertices t) := by
  induction t using Tree.children_ind with
  | node r cs ih =>
      obtain ⟨ext, rest, hdl⟩ : ∃ a b,
          decomp.decompList edges r cs = (a, b) := ⟨_, _, rfl⟩
      have heq : decomp edges (.node r cs) = (r :: ext, rest) := by
        simp [decomp, hdl]
      have hlist : (ext ++ rest.flatMap id).Perm
          (cs.flatMap Tree.vertices) := by
        have h := decompList_perm (r := r) cs ih
        rw [hdl] at h
        exact h
      rw [heq, Tree.vertices_node]
      change ((r :: ext) ++ rest.flatMap id).Perm
        (r :: cs.flatMap Tree.vertices)
      exact List.Perm.cons r hlist

/-- The preferred paths of a tree partition its vertex set. -/
public theorem perm_treePaths_flatMap (edges : List (V × V)) (t : Tree V) :
    ((treePaths edges t).flatMap id).Perm (Tree.vertices t) := by
  change (((decomp edges t).1 :: (decomp edges t).2).flatMap id).Perm _
  rw [List.flatMap_cons]
  exact decomp_perm edges t

omit [DecidableEq V] in
private theorem adjacent_node_of_mem {a b r : V} {cs : List (Tree V)}
    {c : Tree V} (hc : c ∈ cs) (h : Adjacent a b c) :
    Adjacent a b (.node r cs) := by
  rw [adjacent_node]
  exact Or.inr (Or.inr (adjacentList_iff.mpr ⟨c, hc, h⟩))

/-- Every path in the decomposition of a tree is a genuine path of the
tree: consecutive vertices are joined by a parent-child edge. -/
public theorem decomp_isChain (edges : List (V × V)) (t : Tree V) :
    (decomp edges t).1.IsChain (fun a b => Adjacent a b t) ∧
      ∀ p ∈ (decomp edges t).2, p.IsChain (fun a b => Adjacent a b t) := by
  induction t using Tree.children_ind with
  | node r cs ih =>
      obtain ⟨ext, rest, hdl⟩ : ∃ a b,
          decomp.decompList edges r cs = (a, b) := ⟨_, _, rfl⟩
      have heq : decomp edges (.node r cs) = (r :: ext, rest) := by
        simp [decomp, hdl]
      refine ⟨?_, ?_⟩
      · rw [heq]
        change (r :: ext).IsChain (fun a b => Adjacent a b (.node r cs))
        rcases decompList_fst_eq_nil_or cs with hnil |
          ⟨c₀, hc₀, -, hext⟩
        · rw [hdl] at hnil
          have h1 : ext = [] := hnil
          rw [h1]
          exact List.isChain_singleton r
        · rw [hdl] at hext
          have h2 : ext = (decomp edges c₀).1 := hext
          have hlift : ext.IsChain
              (fun a b => Adjacent a b (.node r cs)) := by
            rw [h2]
            exact ((ih c₀ hc₀).1).imp_of_mem_imp
              (fun a b _ _ hadj => adjacent_node_of_mem hc₀ hadj)
          refine List.IsChain.cons hlift ?_
          intro b hb
          have hhead : ext.head? = some c₀.root := by
            rw [h2]
            exact decomp_fst_head? edges c₀
          rw [hhead] at hb
          have hb2 : c₀.root = b := by simpa using hb
          subst hb2
          rw [adjacent_node]
          exact Or.inl ⟨rfl, c₀, hc₀, rfl⟩
      · intro p hp
        rw [heq] at hp
        have hp2 : p ∈ (decomp.decompList edges r cs).2 := by
          rw [hdl]
          exact hp
        obtain ⟨c, hc, hpc⟩ := decompList_mem_snd cs hp2
        have hchainc : p.IsChain (fun a b => Adjacent a b c) := by
          change p ∈ (decomp edges c).1 :: (decomp edges c).2 at hpc
          rw [List.mem_cons] at hpc
          rcases hpc with rfl | hpc
          · exact (ih c hc).1
          · exact (ih c hc).2 p hpc
        exact hchainc.imp_of_mem_imp
          (fun a b _ _ hadj => adjacent_node_of_mem hc hadj)

/-- Every preferred path of a tree is a genuine path of the tree. -/
public theorem isChain_of_mem_treePaths {edges : List (V × V)} {t : Tree V}
    {p : List V} (hp : p ∈ treePaths edges t) :
    p.IsChain (fun a b => Adjacent a b t) := by
  change p ∈ (decomp edges t).1 :: (decomp edges t).2 at hp
  rw [List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact (decomp_isChain edges t).1
  · exact (decomp_isChain edges t).2 p hp

/-- The downward path installed by the access edge update: when the edge
list `E` contains exactly the edges of the root-to-`x` path at vertices of
that path, the decomposition of the tree has that whole root path as its
downward preferred path. -/
public theorem decomp_fst_eq_rootPath {x : V} {E : List (V × V)} :
    ∀ {t : Tree V} {p : List V}, (Tree.vertices t).Nodup →
      rootPath x t = some p →
      (∀ e ∈ pathEdges p, e ∈ E) →
      (∀ e ∈ E, e.1 ∈ p → e ∈ pathEdges p) →
      (decomp E t).1 = p := by
  intro t
  induction t using Tree.children_ind with
  | node r cs ih =>
      intro p hnodup hrp hsub hmin
      have hpNodup : p.Nodup := nodup_rootPath hnodup hrp
      have hflat : (cs.flatMap Tree.vertices).Nodup := by
        have h := hnodup
        rw [Tree.vertices_node, List.nodup_cons] at h
        exact h.2
      obtain ⟨ext, rest, hdl⟩ : ∃ a b,
          decomp.decompList E r cs = (a, b) := ⟨_, _, rfl⟩
      have heq : decomp E (.node r cs) = (r :: ext, rest) := by
        simp [decomp, hdl]
      rcases rootPath_node_cases hrp with ⟨-, rfl⟩ |
        ⟨-, c₀, hc₀, p', hrp', rfl⟩
      · have hnil : ext = [] := by
          have h := decompList_fst_eq_nil (edges := E) (r := r) cs
            (fun c _ hmem => by
              have h1 : (r, c.root) ∈ pathEdges [r] :=
                hmin _ hmem (by simp)
              simp [pathEdges] at h1)
          rw [hdl] at h
          exact h
        rw [heq, hnil]
      · have hrNot : r ∉ p' := (List.nodup_cons.mp hpNodup).1
        have hp'ne : p' ≠ [] := rootPath_ne_nil hrp'
        cases p' with
        | nil => simp at hp'ne
        | cons b rest' =>
            have hbroot : b = c₀.root := by
              simpa using head?_rootPath hrp'
            subst hbroot
            have hEdge : (r, c₀.root) ∈
                pathEdges (r :: c₀.root :: rest') := by
              rw [pathEdges_cons_cons]
              exact List.mem_cons_self
            have hEdgeE : (r, c₀.root) ∈ E := hsub _ hEdge
            have huniq : ∀ c ∈ cs, (r, c.root) ∈ E → c = c₀ := by
              intro c hc hmem
              have h1 : (r, c.root) ∈
                  pathEdges (r :: c₀.root :: rest') :=
                hmin _ hmem (by simp)
              have heqEdge : (r, c.root) = (r, c₀.root) :=
                eq_of_mem_pathEdges hpNodup h1 hEdge rfl
              have hrootEq : c.root = c₀.root :=
                congrArg Prod.snd heqEdge
              have hmem1 : c₀.root ∈ Tree.vertices c :=
                hrootEq ▸ root_mem_vertices c
              have hmem2 : c₀.root ∈ Tree.vertices c₀ :=
                root_mem_vertices c₀
              exact eq_of_mem_vertices_of_nodup_flatMap hflat hc hc₀
                hmem1 hmem2
            have hlist : (decomp.decompList E r cs).1 =
                (decomp E c₀).1 :=
              decompList_fst_eq cs hc₀ hEdgeE huniq
            have hextEq : ext = (decomp E c₀).1 := by
              rw [hdl] at hlist
              exact hlist
            have hnodupC : (Tree.vertices c₀).Nodup :=
              (List.nodup_flatMap.mp hflat).1 c₀ hc₀
            have hsub' : ∀ e ∈ pathEdges (c₀.root :: rest'), e ∈ E := by
              intro e he
              exact hsub e (mem_pathEdges_cons_tail he)
            have hmin' : ∀ e ∈ E, e.1 ∈ (c₀.root :: rest') →
                e ∈ pathEdges (c₀.root :: rest') := by
              intro e heE he1
              have h1 : e ∈ pathEdges (r :: c₀.root :: rest') :=
                hmin e heE (List.mem_cons_of_mem r he1)
              have hne : e.1 ≠ r := by
                intro hf
                rw [hf] at he1
                exact hrNot he1
              exact mem_pathEdges_of_mem_cons hne h1
            have hdown0 : (decomp E c₀).1 = c₀.root :: rest' :=
              ih c₀ hc₀ hnodupC hrp' hsub' hmin'
            rw [heq, hextEq, hdown0]

/-- A link-cut tree state: the represented forest, together with the current
preferred (solid) edges. Each preferred edge is directed from a node to its
preferred child in the represented forest; the preferred-path decomposition
`paths` is derived from the edge list as the maximal solid chains in each
represented tree (`treePaths`). `preferred = []` means every edge is dashed,
so every vertex is its own singleton path. -/
public structure State (V : Type u) where
  /-- The represented forest. -/
  forest : List (Tree V)
  /-- The preferred edges, as `(parent, child)` pairs. -/
  preferred : List (V × V)

namespace State

variable {s : State V}

/-- `x` is a vertex of the represented forest. -/
public def Mem (s : State V) (x : V) : Prop :=
  ∃ t ∈ s.forest, x ∈ Tree.vertices t

/-- Undirected connectivity in the represented forest: some represented tree
contains both vertices. This is the abstraction of the structure. -/
public def Connected (s : State V) (x y : V) : Prop :=
  ∃ t ∈ s.forest, x ∈ Tree.vertices t ∧ y ∈ Tree.vertices t

omit [DecidableEq V] in
public theorem connected_refl_of_mem {x : V} (h : s.Mem x) : s.Connected x x := by
  obtain ⟨t, ht, hx⟩ := h
  exact ⟨t, ht, hx, hx⟩

omit [DecidableEq V] in
public theorem Connected.symm {x y : V} (h : s.Connected x y) : s.Connected y x := by
  obtain ⟨t, ht, hx, hy⟩ := h
  exact ⟨t, ht, hy, hx⟩

omit [DecidableEq V] in
public theorem Connected.mem_left {x y : V} (h : s.Connected x y) : s.Mem x := by
  obtain ⟨t, ht, hx, -⟩ := h
  exact ⟨t, ht, hx⟩

omit [DecidableEq V] in
public theorem Connected.mem_right {x y : V} (h : s.Connected x y) : s.Mem y :=
  h.symm.mem_left

omit [DecidableEq V] in
/-- Connectivity can equally be read off the Euler tours of the represented
trees. -/
public theorem connected_iff_tour {x y : V} :
    s.Connected x y ↔ ∃ t ∈ s.forest, x ∈ Tree.tour t ∧ y ∈ Tree.tour t := by
  simp only [Connected, Tree.mem_tour_iff]

/-- The state invariant bundle used below: the vertex lists of the represented
trees are collectively duplicate-free (so the trees are vertex-disjoint), and
the preferred edges are a functional set of represented directed edges: no
duplicates, every preferred edge is a parent-child edge of some represented
tree, and each vertex has at most one preferred child. The duplicate-free
vertex condition also pins down the parent of each vertex, so the maximal
solid chains (`treePaths`) are genuine disjoint paths. -/
public def Valid (s : State V) : Prop :=
  (s.forest.flatMap Tree.vertices).Nodup ∧
    s.preferred.Nodup ∧
    (∀ e ∈ s.preferred, ∃ t ∈ s.forest, ParentChild e.1 e.2 t) ∧
    (∀ e₁ ∈ s.preferred, ∀ e₂ ∈ s.preferred, e₁.1 = e₂.1 → e₁ = e₂)

omit [DecidableEq V] in
/-- A state with no preferred edges is valid exactly when its forest is
duplicate-free. This is the invariant after every structural operation,
which resets all edges to dashed. -/
public theorem valid_of_preferred_nil (hpre : s.preferred = [])
    (h : (s.forest.flatMap Tree.vertices).Nodup) : s.Valid := by
  refine ⟨h, ?_, ?_, ?_⟩ <;> simp [hpre]

omit [DecidableEq V] in
private theorem tree_eq_of_mem_mem_of_nodup :
    ∀ {f : List (Tree V)}, (f.flatMap Tree.vertices).Nodup →
      ∀ {t₁ t₂ : Tree V} {v : V}, t₁ ∈ f → t₂ ∈ f → v ∈ Tree.vertices t₁ →
        v ∈ Tree.vertices t₂ → t₁ = t₂ := by
  intro f
  induction f with
  | nil => intro _ t₁ t₂ v h₁; exact absurd h₁ (by simp)
  | cons a f ih =>
      intro hnodup t₁ t₂ v h₁ h₂ hv₁ hv₂
      have hflat : ((a :: f).flatMap Tree.vertices) =
          Tree.vertices a ++ f.flatMap Tree.vertices := List.flatMap_cons ..
      rw [hflat] at hnodup
      obtain ⟨-, hp2, hcross⟩ := List.pairwise_append.mp hnodup
      have htail : (f.flatMap Tree.vertices).Nodup := hp2
      rw [List.mem_cons] at h₁ h₂
      rcases h₁ with rfl | h₁ <;> rcases h₂ with rfl | h₂
      · rfl
      · exfalso
        have hvf : v ∈ f.flatMap Tree.vertices :=
          List.mem_flatMap.mpr ⟨t₂, h₂, hv₂⟩
        exact hcross v hv₁ v hvf rfl
      · exfalso
        have hvf : v ∈ f.flatMap Tree.vertices :=
          List.mem_flatMap.mpr ⟨t₁, h₁, hv₁⟩
        exact hcross v hv₂ v hvf rfl
      · exact ih htail h₁ h₂ hv₁ hv₂

/-- The preferred-path decomposition of a state: in each represented tree,
the maximal chains of preferred edges (`treePaths`), deepest continuation
last within each path. Vertices incident to no preferred edge are singleton
paths. Unlike a single distinguished path, this retains the preferred paths
of every subtree: only edges incident to the latest accessed root path
change under `access`. -/
public def paths (s : State V) : List (List V) :=
  s.forest.flatMap (treePaths s.preferred)

private theorem perm_flatMap_treePaths {E : List (V × V)} :
    ∀ (f : List (Tree V)),
      ((f.flatMap (treePaths E)).flatMap id).Perm
        (f.flatMap Tree.vertices) := by
  intro f
  induction f with
  | nil => simp
  | cons t f ih =>
      rw [List.flatMap_cons, List.flatMap_append, List.flatMap_cons]
      exact (perm_treePaths_flatMap E t).append ih

private theorem perm_paths_flatMap (s : State V) :
    ((paths s).flatMap id).Perm (s.forest.flatMap Tree.vertices) :=
  perm_flatMap_treePaths s.forest

/-- The decomposition partitions the vertex set of the represented forest:
a vertex lies on some preferred path exactly when it is in the forest. This
holds for every state, with no validity hypothesis. -/
public theorem mem_paths_flatMap {v : V} :
    v ∈ (paths s).flatMap id ↔ v ∈ s.forest.flatMap Tree.vertices := by
  constructor
  · intro hv
    exact (perm_paths_flatMap s).subset hv
  · intro hv
    exact (perm_paths_flatMap s).symm.subset hv

/-- The flattened decomposition is duplicate-free: every vertex of a valid
state lies on exactly one preferred path. With `mem_paths_flatMap`, the
paths partition the vertex set. -/
public theorem nodup_paths_flatMap (hs : s.Valid) :
    ((paths s).flatMap id).Nodup :=
  (perm_paths_flatMap s).nodup_iff.mpr hs.1

/-- Distinct preferred paths of a valid state are vertex-disjoint. -/
public theorem pairwise_disjoint_paths (hs : s.Valid) :
    (paths s).Pairwise List.Disjoint :=
  (List.nodup_flatMap.mp (nodup_paths_flatMap hs)).2

/-- Every preferred path of a valid state has distinct vertices. -/
public theorem nodup_of_mem_paths {p : List V} (hs : s.Valid)
    (hp : p ∈ paths s) : p.Nodup :=
  (List.nodup_flatMap.mp (nodup_paths_flatMap hs)).1 p hp

/-- Every preferred path is a genuine path of the represented forest:
consecutive vertices are joined by a parent-child edge of one represented
tree (`isChain_of_mem_treePaths`). This holds for every state, with no
validity hypothesis. -/
public theorem isChain_of_mem_paths {p : List V} (hp : p ∈ paths s) :
    p.IsChain (fun a b => ∃ t ∈ s.forest, Adjacent a b t) := by
  obtain ⟨t, ht, hpt⟩ : ∃ t ∈ s.forest, p ∈ treePaths s.preferred t := by
    have h : p ∈ s.forest.flatMap (treePaths s.preferred) := hp
    rwa [List.mem_flatMap] at h
  exact (isChain_of_mem_treePaths hpt).imp_of_mem_imp
    (fun a b _ _ hadj => ⟨t, ht, hadj⟩)

/-- Make the path from the represented root to `x` preferred, as in the
textbook `access`. Every edge of the root-to-`x` path becomes solid, the
previously preferred child edge of each vertex on that path is dropped
(made dashed), and every preferred edge whose parent endpoint lies off the
path is retained: this is what keeps off-path preferred paths alive across
accesses (for example, with root `1`, children `2 → 4` and `3 → 5`,
`access 5` after `access 4` keeps the preferred path `[2, 4]`, since the
edge `2`-`4` has parent endpoint off the `1`-`3`-`5` path; see the
regression tests in `LinkCutTreeTests`). The represented forest is
unchanged. On a vertex outside the forest this is the identity. -/
public def access (x : V) (s : State V) : State V :=
  match findTree x s.forest with
  | some t =>
      match rootPath x t with
      | some p =>
          ⟨s.forest,
            (s.preferred.filter (fun e => e.1 ∉ p)) ++ pathEdges p⟩
      | none => s
  | none => s

public theorem access_eq_of_findTree_rootPath {x : V} {t : Tree V} {p : List V}
    (hft : findTree x s.forest = some t) (hrp : rootPath x t = some p) :
    access x s =
      ⟨s.forest, (s.preferred.filter (fun e => e.1 ∉ p)) ++ pathEdges p⟩ := by
  simp [access, hft, hrp]

/-- An off-path preferred edge survives `access x`: an edge whose parent
endpoint does not lie on the root-to-`x` path is retained. This is the
edge-level statement behind retaining off-path preferred paths. -/
public theorem mem_preferred_access {x : V} {e : V × V}
    (he : e ∈ s.preferred)
    (h : ∀ t p, findTree x s.forest = some t → rootPath x t = some p →
      e.1 ∉ p) :
    e ∈ (access x s).preferred := by
  cases hft : findTree x s.forest with
  | none =>
      have hacc : access x s = s := by simp [access, hft]
      rw [hacc]
      exact he
  | some t =>
      cases hrp : rootPath x t with
      | none =>
          have hacc : access x s = s := by simp [access, hft, hrp]
          rw [hacc]
          exact he
      | some p =>
          rw [access_eq_of_findTree_rootPath hft hrp]
          exact List.mem_append_left _
            (List.mem_filter.mpr ⟨he, by simp [h t p hft hrp]⟩)

/-- Every edge of the accessed root path is preferred after `access x`. -/
public theorem mem_preferred_access_of_mem_pathEdges {x : V} {t : Tree V}
    {p : List V} {e : V × V} (hft : findTree x s.forest = some t)
    (hrp : rootPath x t = some p) (he : e ∈ pathEdges p) :
    e ∈ (access x s).preferred := by
  rw [access_eq_of_findTree_rootPath hft hrp]
  exact List.mem_append_right _ he

/-- Access changes only the preferred edges, never the represented forest. -/
public theorem access_forest (x : V) : (access x s).forest = s.forest := by
  cases hft : findTree x s.forest with
  | none => simp [access, hft]
  | some t =>
      cases hrp : rootPath x t with
      | none => simp [access, hft, hrp]
      | some p => simp [access, hft, hrp]

public theorem connected_access_iff {x y z : V} :
    (access x s).Connected y z ↔ s.Connected y z := by
  change (∃ t ∈ (access x s).forest, _) ↔ (∃ t ∈ s.forest, _)
  rw [access_forest]

public theorem mem_access_iff {x y : V} : (access x s).Mem y ↔ s.Mem y := by
  change (∃ t ∈ (access x s).forest, _) ↔ (∃ t ∈ s.forest, _)
  rw [access_forest]

private theorem findTree_some_of_mem {x : V} (hx : s.Mem x) :
    ∃ t, findTree x s.forest = some t ∧ t ∈ s.forest ∧ x ∈ Tree.vertices t := by
  obtain ⟨t, ht, hxt⟩ := hx
  exact findTree_eq_some_of_exists ⟨t, ht, hxt⟩

/-- After `access x` in a valid state, the root-to-`x` path of the tree
containing `x` is one of the preferred paths of the decomposition, and
`x` is its last (deepest) vertex: `p.getLast? = some x`. No auxiliary
splay tree is modeled, so no claim is made about a splay-tree root. This
is only the endpoint property of the accessed preferred path. Other
preferred paths off that root path are retained (`mem_preferred_access`). -/
public theorem access_last {x : V} (hs : s.Valid) (hx : s.Mem x) :
    ∃ p ∈ paths (access x s), p.getLast? = some x ∧
      ∃ t ∈ s.forest, rootPath x t = some p := by
  obtain ⟨t, hft, ht, hxt⟩ := findTree_some_of_mem hx
  obtain ⟨p, hrp⟩ := rootPath_eq_some_of_mem hxt
  have hacc : access x s =
      ⟨s.forest, (s.preferred.filter (fun e => e.1 ∉ p)) ++ pathEdges p⟩ :=
    access_eq_of_findTree_rootPath hft hrp
  have hnodupT : (Tree.vertices t).Nodup :=
    (List.nodup_flatMap.mp hs.1).1 t ht
  have hdown : (decomp
      ((s.preferred.filter (fun e => e.1 ∉ p)) ++ pathEdges p) t).1 = p := by
    refine decomp_fst_eq_rootPath hnodupT hrp ?_ ?_
    · intro e he
      exact List.mem_append_right _ he
    · intro e he he1
      rw [List.mem_append] at he
      rcases he with he | he
      · exfalso
        obtain ⟨-, h2⟩ := List.mem_filter.mp he
        have h3 : e.1 ∉ p := by simpa using h2
        exact h3 he1
      · exact he
  have hpt : p ∈ treePaths
      ((s.preferred.filter (fun e => e.1 ∉ p)) ++ pathEdges p) t := by
    have h1 : p ∈ (decomp
        ((s.preferred.filter (fun e => e.1 ∉ p)) ++ pathEdges p) t).1 ::
        (decomp
          ((s.preferred.filter (fun e => e.1 ∉ p)) ++ pathEdges p) t).2 := by
      rw [hdown]
      exact List.mem_cons_self
    exact h1
  refine ⟨p, ?_, getLast?_rootPath hrp, t, ht, hrp⟩
  rw [hacc]
  exact List.mem_flatMap.mpr ⟨t, ht, hpt⟩

/-
The textbook `expose` operation (`access` followed by splaying the
auxiliary tree of the accessed path) is not modeled in this module.
`access` above performs only the preferred-path update. There is no
auxiliary splay tree, splay operation, or `expose` definition here.
The endpoint fact that splaying would establish in the imperative
structure is the list-level statement `access_last` (`x` is the last
vertex of its preferred path).
-/

/-- Access preserves the state invariant: the new preferred edges are the
retained off-path edges together with the edges of the accessed root path;
the two groups have disjoint parent endpoints (off versus on the path), so
duplicate-freeness and the at-most-one-preferred-child condition carry over. -/
public theorem Valid.access {x : V} (hs : s.Valid) : (State.access x s).Valid := by
  cases hft : findTree x s.forest with
  | none =>
      have hacc : State.access x s = s := by simp [State.access, hft]
      rw [hacc]; exact hs
  | some t =>
      cases hrp : rootPath x t with
      | none =>
          have hacc : State.access x s = s := by simp [State.access, hft, hrp]
          rw [hacc]; exact hs
      | some p =>
          have hacc : State.access x s =
              ⟨s.forest,
                (s.preferred.filter (fun e => e.1 ∉ p)) ++ pathEdges p⟩ :=
            access_eq_of_findTree_rootPath hft hrp
          obtain ⟨ht, -⟩ := findTree_eq_some_spec hft
          have hnodupT : (Tree.vertices t).Nodup :=
            (List.nodup_flatMap.mp hs.1).1 t ht
          have hpNodup : p.Nodup := nodup_rootPath hnodupT hrp
          rw [hacc]
          refine ⟨hs.1, ?_, ?_, ?_⟩
          · change ((s.preferred.filter (fun e => e.1 ∉ p)) ++
              pathEdges p).Nodup
            rw [List.nodup_append]
            refine ⟨hs.2.1.filter _, nodup_pathEdges hpNodup, ?_⟩
            intro a ha b hb hab
            obtain ⟨-, ha2⟩ := List.mem_filter.mp ha
            have ha3 : a.1 ∉ p := by simpa using ha2
            have hb3 : b.1 ∈ p := fst_mem_of_mem_pathEdges hb
            subst hab
            exact ha3 hb3
          · intro e he
            have he2 : e ∈ (s.preferred.filter (fun e => e.1 ∉ p)) ++
                pathEdges p := he
            rw [List.mem_append] at he2
            rcases he2 with he2 | he2
            · exact hs.2.2.1 e (List.mem_of_mem_filter he2)
            · exact ⟨t, ht,
                mem_pathEdges_of_isChain
                  (isChain_parentChild_rootPath hrp) he2⟩
          · intro e₁ he₁ e₂ he₂ hf
            have h1 : e₁ ∈ (s.preferred.filter (fun e => e.1 ∉ p)) ++
                pathEdges p := he₁
            have h2 : e₂ ∈ (s.preferred.filter (fun e => e.1 ∉ p)) ++
                pathEdges p := he₂
            rw [List.mem_append] at h1 h2
            rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
            · exact hs.2.2.2 _ (List.mem_of_mem_filter h1) _
                (List.mem_of_mem_filter h2) hf
            · exfalso
              obtain ⟨-, hf2⟩ := List.mem_filter.mp h1
              have hf3 : e₁.1 ∉ p := by simpa using hf2
              have h3 : e₂.1 ∈ p := fst_mem_of_mem_pathEdges h2
              rw [← hf] at h3
              exact hf3 h3
            · exfalso
              obtain ⟨-, hf2⟩ := List.mem_filter.mp h2
              have hf3 : e₂.1 ∉ p := by simpa using hf2
              have h3 : e₁.1 ∈ p := fst_mem_of_mem_pathEdges h1
              rw [hf] at h3
              exact hf3 h3
            · exact eq_of_mem_pathEdges hpNodup h1 h2 hf

/-- Reroot the represented tree containing `x` at `x` (`rerootAt`): the
edges on the path from the old root to `x` are reversed and every other
edge is kept, so the undirected represented tree is unchanged. Preferred
edges are reset (all dashed). On a vertex outside the forest this only
resets the preferred edges. -/
public def makeRoot (x : V) (s : State V) : State V :=
  { s with
    preferred := []
    forest :=
      match findTree x s.forest with
      | some t =>
          match rerootAt x t with
          | some t' => removeTree x s.forest ++ [t']
          | none => s.forest
      | none => s.forest }

public theorem makeRoot_preferred (x : V) : (makeRoot x s).preferred = [] :=
  rfl

public theorem makeRoot_forest_eq {x : V} {t t' : Tree V}
    (hft : findTree x s.forest = some t) (hreroot : rerootAt x t = some t') :
    (makeRoot x s).forest = removeTree x s.forest ++ [t'] := by
  simp [makeRoot, hft, hreroot]

/-- After `makeRoot x`, some represented tree is rooted at `x` and has `x`
as a vertex: the rerooted old tree of `x`. -/
public theorem makeRoot_root {x : V} (hx : s.Mem x) :
    ∃ t ∈ (makeRoot x s).forest, t.root = x ∧ x ∈ Tree.vertices t := by
  obtain ⟨t, hft, -, hxt⟩ := findTree_some_of_mem hx
  obtain ⟨t', ht'eq, ht'root⟩ := rerootAt_eq_some_of_mem hxt
  have hfor : (makeRoot x s).forest = removeTree x s.forest ++ [t'] := by
    simp [makeRoot, hft, ht'eq]
  exact ⟨t', by rw [hfor]; exact List.mem_append_right _ (by simp), ht'root,
    (mem_vertices_rerootAt ht'eq).mpr hxt⟩

/-- `makeRoot x` keeps `x` connected to exactly the vertices it was
connected to: rerooting spans the same vertex set as the old tree (and,
by `rerootAt`, the same undirected edges). Vertex disjointness is the
side condition that pins down which tree that is. -/
public theorem connected_makeRoot {x y : V} (hs : s.Valid)
    (h : s.Connected x y) : (makeRoot x s).Connected x y := by
  obtain ⟨t₀, ht₀, hx₀, hy₀⟩ := h
  obtain ⟨t, hft, ht, hxt⟩ := findTree_some_of_mem ⟨t₀, ht₀, hx₀⟩
  have hteq : t = t₀ :=
    tree_eq_of_mem_mem_of_nodup hs.1 ht ht₀ hxt hx₀
  obtain ⟨t', ht'eq, -⟩ := rerootAt_eq_some_of_mem hxt
  have hfor : (makeRoot x s).forest = removeTree x s.forest ++ [t'] := by
    simp [makeRoot, hft, ht'eq]
  have hmem : t' ∈ (makeRoot x s).forest := by
    rw [hfor]
    exact List.mem_append_right _ (by simp)
  have hyt : y ∈ Tree.vertices t := by rw [hteq]; exact hy₀
  exact ⟨t', hmem, (mem_vertices_rerootAt ht'eq).mpr hxt,
    (mem_vertices_rerootAt ht'eq).mpr hyt⟩

/-- Rerooting preserves the state invariant: the new forest has the same
flat vertex list as the old one up to permutation (the rerooted tree
replaces its original), and the preferred edges are reset. -/
public theorem Valid.makeRoot {x : V} (hs : s.Valid) :
    (State.makeRoot x s).Valid := by
  refine valid_of_preferred_nil (makeRoot_preferred x) ?_
  cases hft : findTree x s.forest with
  | none =>
      have hfor : (State.makeRoot x s).forest = s.forest := by
        simp [State.makeRoot, hft]
      rw [hfor]
      exact hs.1
  | some t =>
      cases hreroot : rerootAt x t with
      | none =>
          have hfor : (State.makeRoot x s).forest = s.forest := by
            simp [State.makeRoot, hft, hreroot]
          rw [hfor]
          exact hs.1
      | some t' =>
          rw [makeRoot_forest_eq hft hreroot]
          have hperm : ((removeTree x s.forest).flatMap Tree.vertices ++
              Tree.vertices t').Perm (s.forest.flatMap Tree.vertices) :=
            ((perm_vertices_rerootAt hreroot).append_left _).trans
              (perm_flatMap_removeTree hs.1 hft)
          have hflat : ((removeTree x s.forest ++ [t']).flatMap
              Tree.vertices) =
              (removeTree x s.forest).flatMap Tree.vertices ++
                Tree.vertices t' := by
            simp [List.flatMap_append]
          rw [hflat]
          exact hperm.nodup_iff.mpr hs.1


/-- Link the represented trees of `x` and `y` with the new edge `x`-`y`,
as in the textbook operation: the tree of `x` is first rerooted at `x`
(`rerootAt`, so `x` becomes its root with every old edge kept) and then
grafted as a new child subtree of `y` (`graftAt`), adding exactly the edge
from `y` to `x`. Linking two vertices of the same tree, or a vertex
outside the forest, leaves the forest unchanged. Preferred edges are
reset. -/
public def link (x y : V) (s : State V) : State V :=
  { s with
    preferred := []
    forest :=
      match findTree x s.forest, findTree y s.forest with
      | some tx, some ty =>
          if x ∈ Tree.vertices ty then s.forest
          else
            match rerootAt x tx with
            | some tx' =>
                match graftAt y tx' ty with
                | some tj => removeTree x (removeTree y s.forest) ++ [tj]
                | none => s.forest
            | none => s.forest
      | _, _ => s.forest }

public theorem link_preferred (x y : V) : (link x y s).preferred = [] :=
  rfl

public theorem link_forest_eq {x y : V} {tx ty tx' tj : Tree V}
    (hftx : findTree x s.forest = some tx)
    (hfty : findTree y s.forest = some ty)
    (hxy : x ∉ Tree.vertices ty)
    (hreroot : rerootAt x tx = some tx')
    (hgraft : graftAt y tx' ty = some tj) :
    (link x y s).forest = removeTree x (removeTree y s.forest) ++ [tj] := by
  simp [link, hftx, hfty, hxy, hreroot, hgraft]

/-- A link connects its endpoints: after `link x y`, `x` and `y` lie in one
represented tree. No invariant on the state is needed. -/
public theorem connected_link {x y : V} (hx : s.Mem x) (hy : s.Mem y) :
    (link x y s).Connected x y := by
  obtain ⟨tx, hftx, -, hxtx⟩ := findTree_some_of_mem hx
  obtain ⟨ty, hfty, hty, hyty⟩ := findTree_some_of_mem hy
  by_cases hxy : x ∈ Tree.vertices ty
  · have hfor : (link x y s).forest = s.forest := by
      simp [link, hftx, hfty, hxy]
    exact ⟨ty, by rw [hfor]; exact hty, hxy, hyty⟩
  · obtain ⟨tx', hreroot, -⟩ := rerootAt_eq_some_of_mem hxtx
    have hxtx' : x ∈ Tree.vertices tx' :=
      (mem_vertices_rerootAt hreroot).mpr hxtx
    obtain ⟨tj, htj⟩ := graftAt_eq_some_of_mem hyty (newChild := tx')
    have hfor : (link x y s).forest =
        removeTree x (removeTree y s.forest) ++ [tj] :=
      link_forest_eq hftx hfty hxy hreroot htj
    have htjfor : tj ∈ (link x y s).forest := by
      rw [hfor]
      exact List.mem_append_right _ (by simp)
    exact ⟨tj, htjfor, (mem_vertices_graftAt htj).mpr (Or.inr hxtx'),
      (mem_vertices_graftAt htj).mpr (Or.inl hyty)⟩

/-- Linking preserves the state invariant: the joined tree has the union
of the two old vertex lists up to permutation (rerooting and grafting both
permute), the rest of the forest is untouched, and the preferred path is
reset. -/
public theorem Valid.link {x y : V} (hs : s.Valid) :
    (State.link x y s).Valid := by
  refine valid_of_preferred_nil (link_preferred x y) ?_
  cases hftx : findTree x s.forest with
  | none =>
      have hfor : (State.link x y s).forest = s.forest := by
        simp [State.link, hftx]
      rw [hfor]
      exact hs.1
  | some tx =>
      cases hfty : findTree y s.forest with
      | none =>
          have hfor : (State.link x y s).forest = s.forest := by
            simp [State.link, hftx, hfty]
          rw [hfor]
          exact hs.1
      | some ty =>
          by_cases hxy : x ∈ Tree.vertices ty
          · have hfor : (State.link x y s).forest = s.forest := by
              simp [State.link, hftx, hfty, hxy]
            rw [hfor]
            exact hs.1
          · cases hreroot : rerootAt x tx with
            | none =>
                have hfor : (State.link x y s).forest = s.forest := by
                  simp [State.link, hftx, hfty, hxy, hreroot]
                rw [hfor]
                exact hs.1
            | some tx' =>
                cases hgraft : graftAt y tx' ty with
                | none =>
                    have hfor : (State.link x y s).forest = s.forest := by
                      simp [State.link, hftx, hfty, hxy, hreroot, hgraft]
                    rw [hfor]
                    exact hs.1
                | some tj =>
                    rw [link_forest_eq hftx hfty hxy hreroot hgraft]
                    obtain ⟨htxF, hxTx⟩ := findTree_eq_some_spec hftx
                    obtain ⟨htyF, hyTy⟩ := findTree_eq_some_spec hfty
                    have hyTx : y ∉ Tree.vertices tx := by
                      intro hyTx
                      have hEq : tx = ty :=
                        tree_eq_of_mem_mem_of_nodup hs.1 htxF htyF hyTx hyTy
                      subst hEq
                      exact hxy hxTx
                    have hTxRem : tx ∈ removeTree y s.forest :=
                      mem_removeTree.mpr ⟨htxF, hyTx⟩
                    obtain ⟨ts, hftS, htsMem, hxTs⟩ :=
                      findTree_eq_some_of_exists ⟨tx, hTxRem, hxTx⟩
                    have htsF : ts ∈ s.forest :=
                      (mem_removeTree.mp htsMem).1
                    have htsEq : ts = tx :=
                      tree_eq_of_mem_mem_of_nodup hs.1 htsF htxF hxTs hxTx
                    rw [htsEq] at hftS
                    have hremY : ((removeTree y s.forest).flatMap
                        Tree.vertices ++ Tree.vertices ty).Perm
                        (s.forest.flatMap Tree.vertices) :=
                      perm_flatMap_removeTree hs.1 hfty
                    have hremYNodup : ((removeTree y s.forest).flatMap
                        Tree.vertices).Nodup :=
                      (List.pairwise_append.mp
                        (hremY.nodup_iff.mpr hs.1)).1
                    have hremX : ((removeTree x (removeTree y s.forest)).flatMap
                        Tree.vertices ++ Tree.vertices tx).Perm
                        ((removeTree y s.forest).flatMap Tree.vertices) :=
                      perm_flatMap_removeTree hremYNodup hftS
                    have hTj : (Tree.vertices tj).Perm
                        (Tree.vertices ty ++ Tree.vertices tx) :=
                      (perm_vertices_graftAt hgraft).trans
                        ((perm_vertices_rerootAt hreroot).append_left _)
                    have hperm : ((removeTree x
                        (removeTree y s.forest)).flatMap Tree.vertices ++
                        Tree.vertices tj).Perm
                        (s.forest.flatMap Tree.vertices) :=
                      ((hTj.append_left _).trans
                        ((List.Perm.of_eq (List.append_assoc _ _ _).symm).trans
                          ((perm_rotate3 _ _ _).trans
                            (hremX.append_right _)))).trans hremY
                    have hflat : ((removeTree x
                        (removeTree y s.forest) ++ [tj]).flatMap
                        Tree.vertices) =
                        (removeTree x
                          (removeTree y s.forest)).flatMap Tree.vertices ++
                          Tree.vertices tj := by
                      simp [List.flatMap_append]
                    rw [hflat]
                    exact hperm.nodup_iff.mpr hs.1


/-- Detach the subtree rooted at `x` from its represented tree (the rooted
`cut`): the result contains the detached subtree itself, rooted at `x`,
and the remainder of the old tree with that subtree pruned off
(`pruneAt`), keeping every remaining edge. When `x` is the root of its
tree the remainder is empty and only the detached tree remains. Preferred
edges are reset. -/
public def cut (x : V) (s : State V) : State V :=
  { s with
    preferred := []
    forest :=
      match findTree x s.forest with
      | some t =>
          match findSubtree x t with
          | some sub =>
              match pruneAt x t with
              | some rem => removeTree x s.forest ++ [rem, sub]
              | none => removeTree x s.forest ++ [sub]
          | none => s.forest
      | none => s.forest }

public theorem cut_preferred (x : V) : (cut x s).preferred = [] :=
  rfl

public theorem cut_forest_eq_some {x : V} {t sub rem : Tree V}
    (hft : findTree x s.forest = some t) (hsub : findSubtree x t = some sub)
    (hprune : pruneAt x t = some rem) :
    (cut x s).forest = removeTree x s.forest ++ [rem, sub] := by
  simp [cut, hft, hsub, hprune]

public theorem cut_forest_eq_none {x : V} {t sub : Tree V}
    (hft : findTree x s.forest = some t) (hsub : findSubtree x t = some sub)
    (hprune : pruneAt x t = none) :
    (cut x s).forest = removeTree x s.forest ++ [sub] := by
  simp [cut, hft, hsub, hprune]

/-- A cut separates: after `cut x`, `x` is no longer connected to any
vertex of its old tree that lies outside the subtree rooted at `x`. No
invariant on the state is needed: `x` cannot occur in the pruned
remainder (`mem_vertices_pruneAt`). -/
public theorem not_connected_cut {x y : V} {t sub : Tree V}
    (hft : findTree x s.forest = some t) (hsub : findSubtree x t = some sub)
    (hy : y ∉ Tree.vertices sub) :
    ¬ (cut x s).Connected x y := by
  intro hcon
  obtain ⟨s₀, hs₀, hxs₀, hys₀⟩ := hcon
  have hxsub : x ∈ Tree.vertices sub := by
    have hroot : sub.root = x := root_findSubtree hsub
    rw [← hroot]
    exact root_mem_vertices sub
  cases hprune : pruneAt x t with
  | none =>
      rw [cut_forest_eq_none hft hsub hprune] at hs₀
      simp only [List.mem_append, List.mem_singleton] at hs₀
      rcases hs₀ with hs₀ | hs₀
      · exact (mem_removeTree.mp hs₀).2 hxs₀
      · rw [hs₀] at hys₀
        exact hy hys₀
  | some rem =>
      rw [cut_forest_eq_some hft hsub hprune] at hs₀
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hs₀
      rcases hs₀ with hs₀ | hs₀ | hs₀
      · exact (mem_removeTree.mp hs₀).2 hxs₀
      · rw [hs₀] at hxs₀
        exact (mem_vertices_pruneAt hprune hxs₀).2 rfl
      · rw [hs₀] at hys₀
        exact hy hys₀

/-- After `cut x`, the detached subtree occurs in the forest with root
`x`, so `x` itself remains a vertex, as does every vertex of its old tree
on the other side of the cut. The duplicate-free hypothesis is the
validity side condition under which pruning partitions the vertex set
(`mem_vertices_pruneAt_of_mem_not_mem`). -/
public theorem mem_cut {x y : V} {t sub : Tree V}
    (hnodup : (Tree.vertices t).Nodup)
    (hft : findTree x s.forest = some t) (hsub : findSubtree x t = some sub)
    (hy : y ∈ Tree.vertices t) (hy' : y ∉ Tree.vertices sub) :
    (cut x s).Mem x ∧ (cut x s).Mem y := by
  have hxsub : x ∈ Tree.vertices sub := by
    have hroot : sub.root = x := root_findSubtree hsub
    rw [← hroot]
    exact root_mem_vertices sub
  cases hprune : pruneAt x t with
  | none =>
      have hfor := cut_forest_eq_none hft hsub hprune
      have hsubmem : sub ∈ (cut x s).forest := by
        rw [hfor]
        exact List.mem_append_right _ (by simp)
      refine ⟨⟨sub, hsubmem, hxsub⟩, ?_⟩
      cases t with
      | node r cs =>
          have hr : r = x := by
            by_contra hr
            have hsome : pruneAt x (.node r cs) =
                some (.node r (pruneAt.pruneList x cs)) := by
              simp [pruneAt, hr]
            rw [hsome] at hprune
            cases hprune
          have hsubt : findSubtree x (.node r cs) = some (.node r cs) := by
            simp [findSubtree, hr]
          rw [hsubt] at hsub
          have hst2 : (Tree.node r cs : Tree V) = sub := Option.some.inj hsub
          subst hst2
          exact absurd hy hy'
  | some rem =>
      have hfor := cut_forest_eq_some hft hsub hprune
      have hsubmem : sub ∈ (cut x s).forest := by
        rw [hfor]
        exact List.mem_append_right _ (by simp)
      have hremmem : rem ∈ (cut x s).forest := by
        rw [hfor]
        exact List.mem_append_right _ (by simp)
      have hyrem : y ∈ Tree.vertices rem :=
        mem_vertices_pruneAt_of_mem_not_mem hnodup hsub hprune hy hy'
      exact ⟨⟨sub, hsubmem, hxsub⟩, ⟨rem, hremmem, hyrem⟩⟩

/-- Cutting preserves the state invariant: pruning partitions the cut
tree's vertex list into remainder plus detached subtree up to permutation
(`perm_vertices_pruneAt`), the rest of the forest is untouched, and the
preferred edges are reset. -/
public theorem Valid.cut {x : V} (hs : s.Valid) : (State.cut x s).Valid := by
  refine valid_of_preferred_nil (cut_preferred x) ?_
  cases hft : findTree x s.forest with
  | none =>
      have hfor : (State.cut x s).forest = s.forest := by
        simp [State.cut, hft]
      rw [hfor]
      exact hs.1
  | some t =>
      cases hsub : findSubtree x t with
      | none =>
          have hfor : (State.cut x s).forest = s.forest := by
            simp [State.cut, hft, hsub]
          rw [hfor]
          exact hs.1
      | some sub =>
          cases hprune : pruneAt x t with
          | none =>
              rw [cut_forest_eq_none hft hsub hprune]
              cases t with
              | node r cs =>
                  have hr : r = x := by
                    by_contra hr
                    have hsome : pruneAt x (.node r cs) =
                        some (.node r (pruneAt.pruneList x cs)) := by
                      simp [pruneAt, hr]
                    rw [hsome] at hprune
                    cases hprune
                  have hsubt : findSubtree x (.node r cs) =
                      some (.node r cs) := by simp [findSubtree, hr]
                  rw [hsubt] at hsub
                  have hst : (Tree.node r cs : Tree V) = sub :=
                    Option.some.inj hsub
                  subst hst
                  have hflat : ((removeTree x s.forest ++
                      [Tree.node r cs]).flatMap Tree.vertices) =
                      (removeTree x s.forest).flatMap Tree.vertices ++
                        Tree.vertices (.node r cs) := by
                    simp [List.flatMap_append]
                  rw [hflat]
                  exact (perm_flatMap_removeTree hs.1 hft).nodup_iff.mpr hs.1
          | some rem =>
              rw [cut_forest_eq_some hft hsub hprune]
              obtain ⟨htF, -⟩ := findTree_eq_some_spec hft
              have hnodupT : (Tree.vertices t).Nodup :=
                (List.nodup_flatMap.mp hs.1).1 t htF
              have hpart : (Tree.vertices t).Perm
                  (Tree.vertices rem ++ Tree.vertices sub) :=
                perm_vertices_pruneAt hnodupT hsub hprune
              have hperm : ((removeTree x s.forest).flatMap Tree.vertices ++
                  (Tree.vertices rem ++ Tree.vertices sub)).Perm
                  (s.forest.flatMap Tree.vertices) :=
                (hpart.symm.append_left _).trans
                  (perm_flatMap_removeTree hs.1 hft)
              have hflat : ((removeTree x s.forest ++ [rem, sub]).flatMap
                  Tree.vertices) =
                  (removeTree x s.forest).flatMap Tree.vertices ++
                    (Tree.vertices rem ++ Tree.vertices sub) := by
                simp [List.flatMap_append]
              rw [hflat]
              exact hperm.nodup_iff.mpr hs.1


/-- Undirected edge cut, the textbook composite: reroot at `x`
(`makeRoot x`, which reverses only the root-to-`x` path and keeps every
undirected edge), then detach the subtree rooted at `y`. When `x` and `y`
are joined by an edge of a valid represented tree, the rerooting makes
`y` the root of a child subtree of `x`, so the rooted `cut y` splits the
component into the two sides of the edge `x`-`y`
(`not_connected_cutEdge`), and every other edge is retained
(`adjacent_cutEdge`); the branched-tree tests in `LinkCutTreeTests`
exhibit this on concrete forests.

The adjacency precondition is checked, not assumed: the composite runs
only when some represented tree has `x` and `y` adjacent
(`adjacentB_eq_true_iff`). Without that guard the bare composite would
cut at `y` regardless of `x` (for instance `cutEdge 99 2` on the chain
`1 → 2` would detach `2` although there is no `99`-`2` edge). When no
represented tree has the edge, `cutEdge x y` leaves the forest unchanged
(`cutEdge_eq_of_not_adjacent`); as with the other structural operations,
the preferred edges are reset either way. -/
public def cutEdge (x y : V) (s : State V) : State V :=
  if s.forest.any (adjacentB x y) then cut y (makeRoot x s)
  else { s with preferred := [] }

public theorem cutEdge_preferred (x y : V) :
    (cutEdge x y s).preferred = [] := by
  unfold cutEdge
  split
  · exact cut_preferred y
  · rfl

private theorem forest_any_adjacentB {x y : V} :
    s.forest.any (adjacentB x y) = true ↔
      ∃ t ∈ s.forest, Adjacent x y t := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ht, adjacentB_eq_true_iff.mp h⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ht, adjacentB_eq_true_iff.mpr h⟩

/-- On an adjacent pair, `cutEdge` is the textbook composite `cut y`
after `makeRoot x`. -/
public theorem cutEdge_eq_cut_makeRoot_of_adjacent {x y : V}
    (hadj : ∃ t ∈ s.forest, Adjacent x y t) :
    cutEdge x y s = cut y (makeRoot x s) := by
  unfold cutEdge
  rw [ite_eq_left (forest_any_adjacentB.mpr hadj)]

/-- On a non-adjacent pair, `cutEdge` does not touch the forest: there is
no `x`-`y` edge to remove, and in particular no other edge at `y` is cut.
Only the preferred edges are reset, as for every structural operation. -/
public theorem cutEdge_eq_of_not_adjacent {x y : V}
    (hadj : ¬ ∃ t ∈ s.forest, Adjacent x y t) :
    cutEdge x y s = { s with preferred := [] } := by
  have hfalse : ¬ (s.forest.any (adjacentB x y) = true) :=
    fun h => hadj (forest_any_adjacentB.mp h)
  unfold cutEdge
  rw [ite_eq_right hfalse]

/-- Edge cutting preserves the state invariant: on an adjacent pair it is
the composite of `makeRoot` and `cut`, and otherwise it only resets the
preferred path. -/
public theorem Valid.cutEdge {x y : V} (hs : s.Valid) :
    (State.cutEdge x y s).Valid := by
  unfold State.cutEdge
  split
  · exact Valid.cut (Valid.makeRoot hs)
  · exact valid_of_preferred_nil rfl hs.1

omit [DecidableEq V] in
private theorem exists_child_root_eq_of_adjacent_root {x y : V} {t : Tree V}
    (hnodup : (Tree.vertices t).Nodup) (hroot : t.root = x)
    (hadj : Adjacent x y t) :
    ∃ (cs : List (Tree V)) (c₀ : Tree V),
      t = .node x cs ∧ c₀ ∈ cs ∧ c₀.root = y := by
  cases t with
  | node r cs =>
      have hr : r = x := hroot
      have hadj0 : Adjacent x y (.node r cs) := hadj
      rw [adjacent_node] at hadj
      rcases hadj with ⟨-, c₀, hc₀, hroot₀⟩ | ⟨hr2, -⟩ | hadj
      · exact ⟨cs, c₀, by rw [hr], hc₀, hroot₀⟩
      · exfalso
        have hxy : x = y := hr.symm.trans hr2
        exact not_adjacent_self_of_nodup hnodup (hxy ▸ hadj0)
      · exfalso
        rw [adjacentList_iff] at hadj
        obtain ⟨c, hc, hadj⟩ := hadj
        have hnot := root_not_mem_flatMap_children hnodup
        rw [hr] at hnot
        exact hnot (List.mem_flatMap.mpr ⟨c, hc, hadj.mem_left⟩)

/-- An edge cut separates its endpoints: in a valid state, after
`cutEdge x y` on an adjacent pair, `x` and `y` lie in different
represented trees. Rerooting at `x` keeps the edge (`adjacent_rerootAt`)
and makes the subtree at `y` root-free of `x`, so the rooted separation
theorem `not_connected_cut` applies. -/
public theorem not_connected_cutEdge {x y : V} (hs : s.Valid)
    (hadj : ∃ t ∈ s.forest, Adjacent x y t) :
    ¬ (cutEdge x y s).Connected x y := by
  rw [cutEdge_eq_cut_makeRoot_of_adjacent hadj]
  obtain ⟨t₀, ht₀, hadj₀⟩ := hadj
  have hx₀ : x ∈ Tree.vertices t₀ := hadj₀.mem_left
  have hy₀ : y ∈ Tree.vertices t₀ := hadj₀.mem_right
  obtain ⟨t, hft, ht, hxt⟩ := findTree_some_of_mem ⟨t₀, ht₀, hx₀⟩
  have hteq : t = t₀ := tree_eq_of_mem_mem_of_nodup hs.1 ht ht₀ hxt hx₀
  subst hteq
  have hnodup : (Tree.vertices t).Nodup :=
    (List.nodup_flatMap.mp hs.1).1 t ht
  obtain ⟨t', hreroot, ht'root⟩ := rerootAt_eq_some_of_mem hxt
  have hnodup' : (Tree.vertices t').Nodup :=
    (perm_vertices_rerootAt hreroot).nodup_iff.mpr hnodup
  have hadj' : Adjacent x y t' := (adjacent_rerootAt hnodup hreroot).mpr hadj₀
  have hxne : x ≠ y := fun h => not_adjacent_self_of_nodup hnodup' (h ▸ hadj')
  have hyt' : y ∈ Tree.vertices t' :=
    (mem_vertices_rerootAt hreroot).mpr hy₀
  have hmk : (makeRoot x s).forest = removeTree x s.forest ++ [t'] :=
    makeRoot_forest_eq hft hreroot
  have ht'mem : t' ∈ (makeRoot x s).forest := by
    rw [hmk]
    exact List.mem_append_right _ (by simp)
  obtain ⟨t'', hftY, ht''mem, hyt''⟩ :=
    findTree_eq_some_of_exists ⟨t', ht'mem, hyt'⟩
  have ht''eq : t'' = t' :=
    tree_eq_of_mem_mem_of_nodup (Valid.makeRoot hs).1 ht''mem ht'mem
      hyt'' hyt'
  have hftY' : findTree y (makeRoot x s).forest = some t' := by
    rwa [ht''eq] at hftY
  obtain ⟨sub, hsub⟩ := findSubtree_eq_some_of_mem hyt'
  have hxnot : x ∉ Tree.vertices sub := by
    have h := root_not_mem_vertices_findSubtree hnodup' hsub (t := t')
      (y := y) (by rw [ht'root]; exact hxne.symm)
    rwa [ht'root] at h
  have hnot := not_connected_cut (s := makeRoot x s) hftY' hsub hxnot
  intro hcon
  exact hnot hcon.symm

/-- An edge cut retains every other edge: in a valid state, after
`cutEdge x y` on an adjacent pair, every represented edge other than
`x`-`y` itself is still an edge of some represented tree. Edges of other
trees pass through untouched; edges of the cut tree survive the
rerooting (`adjacent_rerootAt`) and then lie on one side of the prune,
where they are kept by `adjacent_pruneAt_of_mem_mem` (remainder side) or
`adjacent_findSubtree_of_mem_mem` (detached side); the only edge
crossing the prune is `x`-`y` (`adjacent_node_crossing`). -/
public theorem adjacent_cutEdge {x y a b : V} (hs : s.Valid)
    (hadj : ∃ t ∈ s.forest, Adjacent x y t)
    (hab : ∃ t ∈ s.forest, Adjacent a b t)
    (hxy : ¬ ((a = x ∧ b = y) ∨ (a = y ∧ b = x))) :
    ∃ t ∈ (cutEdge x y s).forest, Adjacent a b t := by
  have hce := cutEdge_eq_cut_makeRoot_of_adjacent hadj
  obtain ⟨t₀, ht₀, hadj₀⟩ := hadj
  obtain ⟨t₁, ht₁, hadj₁⟩ := hab
  have hx₀ : x ∈ Tree.vertices t₀ := hadj₀.mem_left
  have hy₀ : y ∈ Tree.vertices t₀ := hadj₀.mem_right
  obtain ⟨t, hft, ht, hxt⟩ := findTree_some_of_mem ⟨t₀, ht₀, hx₀⟩
  have hteq : t = t₀ := tree_eq_of_mem_mem_of_nodup hs.1 ht ht₀ hxt hx₀
  subst hteq
  have hnodup : (Tree.vertices t).Nodup :=
    (List.nodup_flatMap.mp hs.1).1 t ht
  obtain ⟨t', hreroot, ht'root⟩ := rerootAt_eq_some_of_mem hxt
  have hnodup' : (Tree.vertices t').Nodup :=
    (perm_vertices_rerootAt hreroot).nodup_iff.mpr hnodup
  have hadj' : Adjacent x y t' := (adjacent_rerootAt hnodup hreroot).mpr hadj₀
  have hxne : x ≠ y := fun h => not_adjacent_self_of_nodup hnodup' (h ▸ hadj')
  obtain ⟨cs', c₀, ht'eq, hc₀, hc₀root⟩ :=
    exists_child_root_eq_of_adjacent_root hnodup' ht'root hadj'
  have hnodup'n : (Tree.vertices (.node x cs')).Nodup := ht'eq ▸ hnodup'
  have hsub : findSubtree y t' = some c₀ := by
    rw [ht'eq]
    exact findSubtree_eq_child_of_root_eq hnodup'n hc₀ hc₀root hxne
  obtain ⟨rem, hprune⟩ := pruneAt_eq_some_of_root_ne (x := y) (t := t')
    (by rw [ht'root]; exact hxne)
  have hmk : (makeRoot x s).forest = removeTree x s.forest ++ [t'] :=
    makeRoot_forest_eq hft hreroot
  have ht'mem : t' ∈ (makeRoot x s).forest := by
    rw [hmk]
    exact List.mem_append_right _ (by simp)
  have hyt' : y ∈ Tree.vertices t' :=
    (mem_vertices_rerootAt hreroot).mpr hy₀
  obtain ⟨t'', hftY, ht''mem, hyt''⟩ :=
    findTree_eq_some_of_exists ⟨t', ht'mem, hyt'⟩
  have ht''eq : t'' = t' :=
    tree_eq_of_mem_mem_of_nodup (Valid.makeRoot hs).1 ht''mem ht'mem
      hyt'' hyt'
  have hftY' : findTree y (makeRoot x s).forest = some t' := by
    rwa [ht''eq] at hftY
  have hfor : (cutEdge x y s).forest =
      removeTree y (makeRoot x s).forest ++ [rem, c₀] := by
    rw [hce]
    exact cut_forest_eq_some hftY' hsub hprune
  by_cases ht₁t : t₁ = t
  · subst ht₁t
    have hadj₁' : Adjacent a b t' :=
      (adjacent_rerootAt hnodup hreroot).mpr hadj₁
    have hat' : a ∈ Tree.vertices t' :=
      (mem_vertices_rerootAt hreroot).mpr hadj₁.mem_left
    have hbt' : b ∈ Tree.vertices t' :=
      (mem_vertices_rerootAt hreroot).mpr hadj₁.mem_right
    have hperm : (Tree.vertices t').Perm
        (Tree.vertices rem ++ Tree.vertices c₀) :=
      perm_vertices_pruneAt hnodup' hsub hprune
    have hnodupRC : (Tree.vertices rem ++ Tree.vertices c₀).Nodup :=
      hperm.nodup_iff.mp hnodup'
    have hcross : ∀ v ∈ Tree.vertices rem, v ∉ Tree.vertices c₀ := by
      intro v hvrem hvc₀
      exact (List.nodup_append.mp hnodupRC).2.2 v hvrem v hvc₀ rfl
    have hmemA : a ∈ Tree.vertices rem ∨ a ∈ Tree.vertices c₀ := by
      have h : a ∈ Tree.vertices rem ++ Tree.vertices c₀ :=
        hperm.subset hat'
      rwa [List.mem_append] at h
    have hmemB : b ∈ Tree.vertices rem ∨ b ∈ Tree.vertices c₀ := by
      have h : b ∈ Tree.vertices rem ++ Tree.vertices c₀ :=
        hperm.subset hbt'
      rwa [List.mem_append] at h
    have hremmem : rem ∈ (cutEdge x y s).forest := by
      rw [hfor]
      exact List.mem_append_right _ (by simp)
    have hc₀mem : c₀ ∈ (cutEdge x y s).forest := by
      rw [hfor]
      exact List.mem_append_right _ (by simp)
    rcases hmemA with ha | ha <;> rcases hmemB with hb | hb
    · exact ⟨rem, hremmem,
        adjacent_pruneAt_of_mem_mem hnodup' hprune hadj₁' ha hb⟩
    · exfalso
      have hadj₁n : Adjacent b a (.node x cs') := ht'eq ▸ hadj₁'.symm
      obtain ⟨hax, hby⟩ :=
        adjacent_node_crossing hnodup'n hc₀ hadj₁n hb (hcross a ha)
      rw [hc₀root] at hby
      exact hxy (Or.inl ⟨hax, hby⟩)
    · exfalso
      have hadj₁n : Adjacent a b (.node x cs') := ht'eq ▸ hadj₁'
      obtain ⟨hbx, hay⟩ :=
        adjacent_node_crossing hnodup'n hc₀ hadj₁n ha (hcross b hb)
      rw [hc₀root] at hay
      exact hxy (Or.inr ⟨hay, hbx⟩)
    · exact ⟨c₀, hc₀mem,
        adjacent_findSubtree_of_mem_mem hnodup' hsub hadj₁' ha hb⟩
  · have hx1 : x ∉ Tree.vertices t₁ := fun h =>
      ht₁t (tree_eq_of_mem_mem_of_nodup hs.1 ht₁ ht h hxt)
    have hy1 : y ∉ Tree.vertices t₁ := fun h =>
      ht₁t (tree_eq_of_mem_mem_of_nodup hs.1 ht₁ ht h hy₀)
    have ht₁mk : t₁ ∈ (makeRoot x s).forest := by
      rw [hmk]
      exact List.mem_append_left _ (mem_removeTree.mpr ⟨ht₁, hx1⟩)
    have ht₁for : t₁ ∈ (cutEdge x y s).forest := by
      rw [hfor]
      exact List.mem_append_left _ (mem_removeTree.mpr ⟨ht₁mk, hy1⟩)
    exact ⟨t₁, ht₁for, hadj₁⟩


end State

namespace State

/-- Two isolated vertices become connected by a link. -/
example : (link 1 2 ⟨[.node 1 [], .node 2 []], []⟩ : State Nat).Connected 1 2 :=
  connected_link (s := ⟨[.node 1 [], .node 2 []], []⟩)
    ⟨.node 1 [], by simp, by simp [Tree.vertices_node]⟩
    ⟨.node 2 [], by simp, by simp [Tree.vertices_node]⟩

/-- After `access 2` in the two-vertex chain `1 → 2`, the edge `1`-`2` is
preferred, the preferred path is `[1, 2]`, and `2` is its last
(deepest) vertex. -/
example : (access 2 ⟨[.node 1 [.node 2 []]], []⟩ : State Nat).preferred =
    [(1, 2)] := by
  have hacc : access 2 (⟨[.node 1 [.node 2 []]], []⟩ : State Nat) =
      ⟨[.node 1 [.node 2 []]],
        (([] : List (Nat × Nat)).filter (fun e => e.1 ∉ [1, 2])) ++
          pathEdges [1, 2]⟩ :=
    access_eq_of_findTree_rootPath
      (s := ⟨[.node 1 [.node 2 []]], []⟩) (t := .node 1 [.node 2 []])
      (p := [1, 2])
      (by simp [findTree, Tree.vertices_node])
      (by decide)
  rw [hacc]
  decide

end State

end LinkCutTree

end Cslib.Algorithms.Lean
