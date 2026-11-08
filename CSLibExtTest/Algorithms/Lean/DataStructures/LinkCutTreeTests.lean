/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.LinkCutTree

/-!
# Tests for the link-cut tree specification API

These client examples exercise connectivity, access, link, cut, and rerooting
through the public executable and correctness API on a concrete two-tree
forest.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.LinkCutTreeTests

open EulerTourTree LinkCutTree

public def treeA : Tree Nat := .node 1 [.node 2 []]

public def treeB : Tree Nat := .node 3 []

public def state : State Nat := ⟨[treeA, treeB], []⟩

example : Tree.vertices treeA = [1, 2] := by
  simp [treeA, Tree.vertices_node]

example : Tree.tour treeA = [1, 2, 1] := by
  simp [treeA, Tree.tour_node]

example : state.Mem 2 := by
  exact ⟨treeA, by simp [state], by simp [treeA, Tree.vertices_node]⟩

example : state.Connected 1 2 := by
  exact ⟨treeA, by simp [state], by simp [treeA, Tree.vertices_node],
    by simp [treeA, Tree.vertices_node]⟩

example : state.Connected 2 1 :=
  (show state.Connected 1 2 from
    ⟨treeA, by simp [state], by simp [treeA, Tree.vertices_node],
      by simp [treeA, Tree.vertices_node]⟩).symm

example : (State.access 2 state).forest = state.forest :=
  State.access_forest 2

example : ∃ p ∈ State.paths (State.access 2 state),
    p.getLast? = some 2 := by
  obtain ⟨p, hp, hlast, -⟩ := State.access_last
    (State.valid_of_preferred_nil (s := state) rfl
      (by simp [state, treeA, treeB, Tree.vertices_node]))
    (show state.Mem 2 from
      ⟨treeA, by simp [state], by simp [treeA, Tree.vertices_node]⟩)
  exact ⟨p, hp, hlast⟩

example : (State.link 2 3 state).Connected 2 3 :=
  State.connected_link
    ⟨treeA, by simp [state], by simp [treeA, Tree.vertices_node]⟩
    ⟨treeB, by simp [state], by simp [treeB, Tree.vertices_node]⟩

example : (State.link 2 3 state).preferred = [] :=
  State.link_preferred 2 3

example : (State.cut 2 state).preferred = [] :=
  State.cut_preferred 2

example : ∃ t ∈ (State.makeRoot 2 state).forest,
    t.root = 2 ∧ 2 ∈ Tree.vertices t :=
  State.makeRoot_root
    ⟨treeA, by simp [state], by simp [treeA, Tree.vertices_node]⟩

example (s : State Nat) (x y z : Nat) :
    (State.access x s).Connected y z ↔ s.Connected y z :=
  State.connected_access_iff

example (s : State Nat) (x y : Nat) :
    s.Connected x y ↔
      ∃ t ∈ s.forest, x ∈ Tree.tour t ∧ y ∈ Tree.tour t :=
  State.connected_iff_tour

/-- The branched tree `1` with children `2` and `3`. This is the
regression case for adjacency preservation of the structural operations:
rerooting, linking, and cutting must keep the branch `1`-`3` intact when
the edge `1`-`2` is manipulated, rather than rebuilding the tree as a
preorder spine. -/
public def branchedTree : Tree Nat := .node 1 [.node 2 [], .node 3 []]

public def branchedState : State Nat := ⟨[branchedTree], []⟩

example : Tree.vertices branchedTree = [1, 2, 3] := by
  simp [branchedTree, Tree.vertices_node]

example : findSubtree 2 branchedTree = some (.node 2 []) := by
  simp [branchedTree, findSubtree, findSubtree.findSubtreeList]

/-- `makeRoot 1` on a tree already rooted at `1` is the identity on the
forest: no path edges need reversing. -/
example : (State.makeRoot 1 branchedState).forest = [branchedTree] := by
  simp [branchedState, branchedTree, State.makeRoot, findTree, removeTree,
    rerootAt, Tree.vertices_node]

/-- `makeRoot 2` reverses the single path edge `1`-`2`, producing the
chain `2 → 1 → 3` with both original undirected edges kept. -/
example : (State.makeRoot 2 branchedState).forest =
    [.node 2 [.node 1 [.node 3 []]]] := by
  simp [branchedState, branchedTree, State.makeRoot, findTree, removeTree,
    rerootAt, rerootAt.rerootAtList, graftAt, Tree.vertices_node]

example : (State.makeRoot 2 branchedState).Connected 1 3 := by
  have hfor : (State.makeRoot 2 branchedState).forest =
      [.node 2 [.node 1 [.node 3 []]]] := by
    simp [branchedState, branchedTree, State.makeRoot, findTree, removeTree,
      rerootAt, rerootAt.rerootAtList, graftAt, Tree.vertices_node]
  exact ⟨.node 2 [.node 1 [.node 3 []]], by rw [hfor]; simp,
    by simp [Tree.vertices_node], by simp [Tree.vertices_node]⟩

/-- The rooted `cut 2` prunes exactly the subtree at `2`, leaving
`1 → 3` with the branch intact: components `{1, 3}` and `{2}`. -/
example : (State.cut 2 branchedState).forest =
    [.node 1 [.node 3 []], .node 2 []] := by
  simp [branchedState, branchedTree, State.cut, findTree, findSubtree,
    findSubtree.findSubtreeList, removeTree, pruneAt, pruneAt.pruneList,
    Tree.vertices_node]

example :
    (State.cut 2 branchedState).forest.map Tree.vertices = [[1, 3], [2]] := by
  simp [branchedState, branchedTree, State.cut, findTree, findSubtree,
    findSubtree.findSubtreeList, removeTree, pruneAt, pruneAt.pruneList,
    Tree.vertices_node]

example : (State.cut 2 branchedState).Connected 1 3 := by
  have hfor : (State.cut 2 branchedState).forest =
      [.node 1 [.node 3 []], .node 2 []] := by
    simp [branchedState, branchedTree, State.cut, findTree, findSubtree,
      findSubtree.findSubtreeList, removeTree, pruneAt, pruneAt.pruneList,
      Tree.vertices_node]
  exact ⟨.node 1 [.node 3 []], by rw [hfor]; simp,
    by simp [Tree.vertices_node], by simp [Tree.vertices_node]⟩

example : ¬ (State.cut 2 branchedState).Connected 1 2 := by
  intro h
  obtain ⟨t, ht, h1, h2⟩ := h
  have hfor : (State.cut 2 branchedState).forest =
      [.node 1 [.node 3 []], .node 2 []] := by
    simp [branchedState, branchedTree, State.cut, findTree, findSubtree,
      findSubtree.findSubtreeList, removeTree, pruneAt, pruneAt.pruneList,
      Tree.vertices_node]
  rw [hfor] at ht
  simp at ht
  rcases ht with rfl | rfl <;> simp [Tree.vertices_node] at h1 h2

/-- Undirected edge cut: `cutEdge 1 2` removes the edge `1`-`2`, leaving
`{1, 3}` and `{2}`. -/
example : (State.cutEdge 1 2 branchedState).forest =
    [.node 1 [.node 3 []], .node 2 []] := by
  simp [State.cutEdge, adjacentB, adjacentB.adjacentBList, branchedState, branchedTree, State.cut,
    State.makeRoot, findTree, findSubtree, findSubtree.findSubtreeList,
    removeTree, rerootAt, pruneAt, pruneAt.pruneList, Tree.vertices_node]

/-- The same edge from the other endpoint: `cutEdge 2 1` reroots at `2`
first, then detaches `1` with its remaining branch to `3`. -/
example : (State.cutEdge 2 1 branchedState).forest =
    [.node 2 [], .node 1 [.node 3 []]] := by
  simp [State.cutEdge, adjacentB, adjacentB.adjacentBList, branchedState, branchedTree, State.cut,
    State.makeRoot, findTree, findSubtree, findSubtree.findSubtreeList,
    removeTree, rerootAt, rerootAt.rerootAtList, graftAt, pruneAt,
    pruneAt.pruneList, Tree.vertices_node]

example : (State.cutEdge 2 1 branchedState).Connected 1 3 := by
  have hfor : (State.cutEdge 2 1 branchedState).forest =
      [.node 2 [], .node 1 [.node 3 []]] := by
    simp [State.cutEdge, adjacentB, adjacentB.adjacentBList, branchedState, branchedTree, State.cut,
      State.makeRoot, findTree, findSubtree, findSubtree.findSubtreeList,
      removeTree, rerootAt, rerootAt.rerootAtList, graftAt, pruneAt,
      pruneAt.pruneList, Tree.vertices_node]
  exact ⟨.node 1 [.node 3 []], by rw [hfor]; simp,
    by simp [Tree.vertices_node], by simp [Tree.vertices_node]⟩

/-- Linking creates the endpoint edge: the tree of `2` (`1 → 2`) is
rerooted at `2` (`2 → 1`) and grafted under `3`, so the new edge is
`3`-`2`, not `3`-`1`. -/
example : (State.link 2 3 state).forest =
    [.node 3 [.node 2 [.node 1 []]]] := by
  simp [state, treeA, treeB, State.link, findTree, removeTree, rerootAt,
    rerootAt.rerootAtList, graftAt, Tree.vertices_node]

/-- The composition case: link the branched tree under an isolated vertex
`4`, then cut `2`. Adjacency preservation requires the result to keep
`4`-`1`-`3` together (`{4, 1, 3}` and `{2}`); flattening the linked tree
to a spine would wrongly group `2` with `3`. -/
public def linkState : State Nat := ⟨[.node 4 [], branchedTree], []⟩

example : (State.link 1 4 linkState).forest =
    [.node 4 [.node 1 [.node 2 [], .node 3 []]]] := by
  simp [linkState, branchedTree, State.link, findTree, removeTree,
    rerootAt, graftAt, Tree.vertices_node]

example : (State.cut 2 (State.link 1 4 linkState)).forest =
    [.node 4 [.node 1 [.node 3 []]], .node 2 []] := by
  simp [linkState, branchedTree, State.cut, State.link, findTree,
    findSubtree, findSubtree.findSubtreeList, removeTree, rerootAt,
    graftAt, pruneAt, pruneAt.pruneList, Tree.vertices_node]

example :
    (State.cut 2 (State.link 1 4 linkState)).forest.map Tree.vertices =
      [[4, 1, 3], [2]] := by
  simp [linkState, branchedTree, State.cut, State.link, findTree,
    findSubtree, findSubtree.findSubtreeList, removeTree, rerootAt,
    graftAt, pruneAt, pruneAt.pruneList, Tree.vertices_node]

example : (State.cut 2 (State.link 1 4 linkState)).Connected 4 3 := by
  have hfor : (State.cut 2 (State.link 1 4 linkState)).forest =
      [.node 4 [.node 1 [.node 3 []]], .node 2 []] := by
    simp [linkState, branchedTree, State.cut, State.link, findTree,
      findSubtree, findSubtree.findSubtreeList, removeTree, rerootAt,
      graftAt, pruneAt, pruneAt.pruneList, Tree.vertices_node]
  exact ⟨.node 4 [.node 1 [.node 3 []]], by rw [hfor]; simp,
    by simp [Tree.vertices_node], by simp [Tree.vertices_node]⟩

example : ¬ (State.cut 2 (State.link 1 4 linkState)).Connected 4 2 := by
  intro h
  obtain ⟨t, ht, h4, h2⟩ := h
  have hfor : (State.cut 2 (State.link 1 4 linkState)).forest =
      [.node 4 [.node 1 [.node 3 []]], .node 2 []] := by
    simp [linkState, branchedTree, State.cut, State.link, findTree,
      findSubtree, findSubtree.findSubtreeList, removeTree, rerootAt,
      graftAt, pruneAt, pruneAt.pruneList, Tree.vertices_node]
  rw [hfor] at ht
  simp at ht
  rcases ht with rfl | rfl <;> simp [Tree.vertices_node] at h4 h2

/-- A depth-two tree: rerooting at `4` must reverse the path
`1`-`2`-`4` one edge at a time (`4 → 2 → 1`, with `5` still under `2` and
`3` still under `1`), not attach `1` directly under `4`. -/
public def deepTree : Tree Nat :=
  .node 1 [.node 2 [.node 4 [], .node 5 []], .node 3 []]

public def deepState : State Nat := ⟨[deepTree], []⟩

example : (State.makeRoot 4 deepState).forest =
    [.node 4 [.node 2 [.node 5 [], .node 1 [.node 3 []]]]] := by
  simp [deepState, deepTree, State.makeRoot, findTree, removeTree,
    rerootAt, rerootAt.rerootAtList, graftAt, graftAt.graftAtList,
    Tree.vertices_node]

/-- Cutting the edge `4`-`2` at depth two isolates `4` and keeps
`{1, 2, 3, 5}` together with every original edge. -/
example : (State.cutEdge 4 2 deepState).forest =
    [.node 4 [], .node 2 [.node 5 [], .node 1 [.node 3 []]]] := by
  simp [State.cutEdge, adjacentB, adjacentB.adjacentBList, deepState,
    deepTree, State.cut, State.makeRoot,
    findTree, findSubtree, findSubtree.findSubtreeList, removeTree,
    rerootAt, rerootAt.rerootAtList, graftAt, graftAt.graftAtList,
    pruneAt, pruneAt.pruneList, Tree.vertices_node]

example :
    (State.cutEdge 4 2 deepState).forest.map Tree.vertices =
      [[4], [2, 5, 1, 3]] := by
  simp [State.cutEdge, adjacentB, adjacentB.adjacentBList, deepState,
    deepTree, State.cut, State.makeRoot,
    findTree, findSubtree, findSubtree.findSubtreeList, removeTree,
    rerootAt, rerootAt.rerootAtList, graftAt, graftAt.graftAtList,
    pruneAt, pruneAt.pruneList, Tree.vertices_node]

example : Adjacent 1 2 branchedTree := by
  simp [branchedTree, Adjacent, Adjacent.AdjacentList]

example : Adjacent 1 2 deepTree := by
  simp [deepTree, Adjacent, Adjacent.AdjacentList]

example : ¬ Adjacent 1 4 deepTree := by
  simp [deepTree, Adjacent, Adjacent.AdjacentList]

/-- Rerooting preserves every undirected edge of the deep tree, through
the public `adjacent_rerootAt` theorem. -/
example (a b : Nat) (t' : Tree Nat) (h : rerootAt 4 deepTree = some t') :
    Adjacent a b t' ↔ Adjacent a b deepTree :=
  adjacent_rerootAt (by simp [deepTree, Tree.vertices_node]) h

#check Cslib.Algorithms.Lean.LinkCutTree.adjacent_graftAt
#check Cslib.Algorithms.Lean.LinkCutTree.adjacent_rerootAt
#check Cslib.Algorithms.Lean.LinkCutTree.perm_vertices_rerootAt
#check Cslib.Algorithms.Lean.LinkCutTree.State.Valid.makeRoot
#check Cslib.Algorithms.Lean.LinkCutTree.State.Valid.link
#check Cslib.Algorithms.Lean.LinkCutTree.State.Valid.cut
#check Cslib.Algorithms.Lean.LinkCutTree.State.Valid.cutEdge
#check Cslib.Algorithms.Lean.LinkCutTree.State.not_connected_cutEdge
#check Cslib.Algorithms.Lean.LinkCutTree.State.adjacent_cutEdge
#check Cslib.Algorithms.Lean.LinkCutTree.State.cutEdge_eq_of_not_adjacent
#check Cslib.Algorithms.Lean.LinkCutTree.State.mem_paths_flatMap
#check Cslib.Algorithms.Lean.LinkCutTree.State.nodup_paths_flatMap
#check Cslib.Algorithms.Lean.LinkCutTree.State.pairwise_disjoint_paths
#check Cslib.Algorithms.Lean.LinkCutTree.State.isChain_of_mem_paths
#check Cslib.Algorithms.Lean.LinkCutTree.State.access_last
#check Cslib.Algorithms.Lean.LinkCutTree.adjacent_pruneAt_of_mem_mem

private theorem branchedState_valid : branchedState.Valid :=
  State.valid_of_preferred_nil rfl
    (by simp [branchedState, branchedTree, Tree.vertices_node])

private theorem linkState_valid : linkState.Valid :=
  State.valid_of_preferred_nil rfl
    (by simp [linkState, branchedTree, Tree.vertices_node])

example : (State.makeRoot 2 branchedState).Valid :=
  State.Valid.makeRoot branchedState_valid

example : (State.cut 2 branchedState).Valid :=
  State.Valid.cut branchedState_valid

example : (State.cutEdge 2 1 branchedState).Valid :=
  State.Valid.cutEdge branchedState_valid

example : (State.link 1 4 linkState).Valid :=
  State.Valid.link linkState_valid

example : (State.cut 2 (State.link 1 4 linkState)).Valid :=
  State.Valid.cut (State.Valid.link linkState_valid)

/-- Validity recovered after `link` and `cut` composes with the
connectivity API: rerooting the cut forest at `3` keeps `3` connected
to `4`, via `connected_makeRoot` at the composed validity proof. -/
example :
    (State.makeRoot 3 (State.cut 2 (State.link 1 4 linkState))).Connected
      3 4 :=
  State.connected_makeRoot (State.Valid.cut (State.Valid.link linkState_valid))
    (by
      have hfor : (State.cut 2 (State.link 1 4 linkState)).forest =
          [.node 4 [.node 1 [.node 3 []]], .node 2 []] := by
        simp [linkState, branchedTree, State.cut, State.link, findTree,
          findSubtree, findSubtree.findSubtreeList, removeTree,
          rerootAt, graftAt, pruneAt, pruneAt.pruneList,
          Tree.vertices_node]
      exact ⟨.node 4 [.node 1 [.node 3 []]], by rw [hfor]; simp,
        by simp [Tree.vertices_node], by simp [Tree.vertices_node]⟩)

/-- The guard's regression case: `99` has no edge to `2`, so
`cutEdge 99 2` must not detach `2` from `1`; the forest is unchanged and
`1` stays connected to `2`. -/
example : (State.cutEdge 99 2 ⟨[.node 1 [.node 2 []]], []⟩ :
    State Nat).forest = [.node 1 [.node 2 []]] := by
  simp [State.cutEdge, adjacentB, adjacentB.adjacentBList]

example : (State.cutEdge 99 2 ⟨[.node 1 [.node 2 []]], []⟩ :
    State Nat).Connected 1 2 := by
  have hfor : (State.cutEdge 99 2 ⟨[.node 1 [.node 2 []]], []⟩ :
      State Nat).forest = [.node 1 [.node 2 []]] := by
    simp [State.cutEdge, adjacentB, adjacentB.adjacentBList]
  exact ⟨.node 1 [.node 2 []], by rw [hfor]; simp,
    by simp [Tree.vertices_node], by simp [Tree.vertices_node]⟩

example : State.cutEdge 99 2 branchedState =
    { branchedState with preferred := [] } :=
  State.cutEdge_eq_of_not_adjacent (by
    simp [branchedState, branchedTree, Adjacent, Adjacent.AdjacentList])

/-- Separation through the public theorem, not by computation. -/
example : ¬ (State.cutEdge 1 2 branchedState).Connected 1 2 :=
  State.not_connected_cutEdge branchedState_valid
    ⟨branchedTree, by simp [branchedState],
      by simp [branchedTree, Adjacent, Adjacent.AdjacentList]⟩

/-- Retention through the public theorem: the untouched branch edge
`1`-`3` survives cutting `1`-`2`. -/
example : ∃ t ∈ (State.cutEdge 1 2 branchedState).forest, Adjacent 1 3 t :=
  State.adjacent_cutEdge branchedState_valid
    ⟨branchedTree, by simp [branchedState],
      by simp [branchedTree, Adjacent, Adjacent.AdjacentList]⟩
    ⟨branchedTree, by simp [branchedState],
      by simp [branchedTree, Adjacent, Adjacent.AdjacentList]⟩
    (by decide)

private theorem state_valid : state.Valid :=
  State.valid_of_preferred_nil rfl
    (by simp [state, treeA, treeB, Tree.vertices_node])

example : State.paths (State.access 2 state) = [[1, 2], [3]] := by
  simp [state, treeA, treeB, State.access, State.paths, findTree, rootPath,
    rootPath.rootPathList, pathEdges, treePaths, decomp,
    decomp.decompList, Tree.vertices_node]

example : ((State.paths (State.access 2 state)).flatMap id).Nodup :=
  State.nodup_paths_flatMap (State.Valid.access state_valid)

example : (State.paths (State.access 2 state)).Pairwise List.Disjoint :=
  State.pairwise_disjoint_paths (State.Valid.access state_valid)

example (p : List Nat) (hp : p ∈ State.paths (State.access 2 state)) :
    p.IsChain (fun a b =>
      ∃ t ∈ (State.access 2 state).forest, Adjacent a b t) :=
  State.isChain_of_mem_paths hp

/-- Membership in the flattened decomposition needs no validity
hypothesis: stated for every state. -/
example (s : State Nat) (v : Nat) :
    v ∈ (State.paths s).flatMap id ↔ v ∈ s.forest.flatMap Tree.vertices :=
  State.mem_paths_flatMap

/-- The fork tree `1` with children `2 → 4` and `3 → 5`. This is the
regression case for off-path preferred paths: `access` must update only the
edges on the accessed root path. After `access 4` the preferred path is
`[1, 2, 4]`; a following `access 5` installs `[1, 3, 5]` and must retain
`[2, 4]` (dropping only the edge `1`-`2`), rather than discarding it to
singletons as a single-distinguished-path state would. -/
public def forkTree : Tree Nat :=
  .node 1 [.node 2 [.node 4 []], .node 3 [.node 5 []]]

public def forkState : State Nat := ⟨[forkTree], []⟩

example : State.paths forkState = [[1], [2], [4], [3], [5]] := by
  decide

example : State.paths (State.access 4 forkState) =
    [[1, 2, 4], [3], [5]] := by
  simp [forkState, forkTree, State.access, State.paths, findTree, rootPath,
    rootPath.rootPathList, pathEdges, treePaths, decomp,
    decomp.decompList, Tree.vertices_node]

/-- The off-path preferred path `[2, 4]` survives `access 5`. -/
example : [2, 4] ∈ State.paths
    (State.access 5 (State.access 4 forkState)) := by
  simp [forkState, forkTree, State.access, State.paths, findTree, rootPath,
    rootPath.rootPathList, pathEdges, treePaths, decomp,
    decomp.decompList, Tree.vertices_node]

example : State.paths (State.access 5 (State.access 4 forkState)) =
    [[1, 3, 5], [2, 4]] := by
  simp [forkState, forkTree, State.access, State.paths, findTree, rootPath,
    rootPath.rootPathList, pathEdges, treePaths, decomp,
    decomp.decompList, Tree.vertices_node]

private theorem forkState_valid : forkState.Valid :=
  State.valid_of_preferred_nil rfl
    (by simp [forkState, forkTree, Tree.vertices_node])

example : (State.access 5 (State.access 4 forkState)).Valid :=
  State.Valid.access (State.Valid.access forkState_valid)

/-- Retention through the public edge-level theorem, not by computation:
the edge `(2, 4)` installed by `access 4` has parent endpoint `2` off the
root-to-`5` path `[1, 3, 5]`, so `mem_preferred_access` keeps it. -/
example : (2, 4) ∈
    (State.access 5 (State.access 4 forkState)).preferred :=
  State.mem_preferred_access
    (State.mem_preferred_access_of_mem_pathEdges
      (s := forkState) (t := forkTree) (p := [1, 2, 4])
      (by simp [forkState, findTree, forkTree, Tree.vertices_node])
      (by decide) (by decide)) (by
    intro t p hft hrp
    have hfor : (State.access 4 forkState).forest = [forkTree] := by
      rw [State.access_forest]
      rfl
    rw [hfor] at hft
    have hftree : findTree 5 ([forkTree] : List (Tree Nat)) =
        some forkTree := by
      simp [findTree, forkTree, Tree.vertices_node]
    rw [hftree] at hft
    have ht : t = forkTree := Option.some.inj hft.symm
    subst ht
    have hrpath : rootPath 5 forkTree = some [1, 3, 5] := by decide
    rw [hrpath] at hrp
    have hp : p = [1, 3, 5] := Option.some.inj hrp.symm
    rw [hp]
    decide)

example : ∃ p ∈ State.paths
      (State.access 5 (State.access 4 forkState)),
    p.getLast? = some 5 := by
  obtain ⟨p, hp, hlast, -⟩ := State.access_last (x := 5)
    (State.Valid.access forkState_valid)
    (State.mem_access_iff.mpr
      ⟨forkTree, by simp [forkState],
        by simp [forkTree, Tree.vertices_node]⟩)
  exact ⟨p, hp, hlast⟩

#check Cslib.Algorithms.Lean.LinkCutTree.ParentChild
#check Cslib.Algorithms.Lean.LinkCutTree.pathEdges
#check Cslib.Algorithms.Lean.LinkCutTree.decomp_fst_eq_rootPath
#check Cslib.Algorithms.Lean.LinkCutTree.State.mem_preferred_access
#check Cslib.Algorithms.Lean.LinkCutTree.State.valid_of_preferred_nil

#print axioms Cslib.Algorithms.Lean.LinkCutTree.State.connected_link
#print axioms Cslib.Algorithms.Lean.LinkCutTree.State.access_last
#print axioms Cslib.Algorithms.Lean.LinkCutTree.State.not_connected_cut
#print axioms Cslib.Algorithms.Lean.LinkCutTree.State.makeRoot_root
#print axioms Cslib.Algorithms.Lean.LinkCutTree.State.connected_makeRoot
#print axioms Cslib.Algorithms.Lean.LinkCutTree.adjacent_rerootAt
#print axioms Cslib.Algorithms.Lean.LinkCutTree.adjacent_graftAt
#print axioms Cslib.Algorithms.Lean.LinkCutTree.State.Valid.link
#print axioms Cslib.Algorithms.Lean.LinkCutTree.State.Valid.cut
#print axioms Cslib.Algorithms.Lean.LinkCutTree.State.not_connected_cutEdge
#print axioms Cslib.Algorithms.Lean.LinkCutTree.State.adjacent_cutEdge
#print axioms Cslib.Algorithms.Lean.LinkCutTree.State.mem_paths_flatMap
#print axioms Cslib.Algorithms.Lean.LinkCutTree.State.nodup_paths_flatMap
#print axioms Cslib.Algorithms.Lean.LinkCutTree.State.isChain_of_mem_paths
#print axioms Cslib.Algorithms.Lean.LinkCutTree.decomp_fst_eq_rootPath
#print axioms Cslib.Algorithms.Lean.LinkCutTree.State.mem_preferred_access

end Cslib.Algorithms.Lean.LinkCutTreeTests
