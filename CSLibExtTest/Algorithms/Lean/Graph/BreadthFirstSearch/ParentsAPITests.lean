/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.BreadthFirstSearch.Parents.Correctness
public import CSLibExt.Algorithms.Lean.Graph.BreadthFirstSearch.Parents.Costs

/-! Ordinary downstream imports expose the complete frozen parent-tree/path/cost API. -/

@[expose] public section

set_option autoImplicit false

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.BreadthFirstSearch

#check bfsWithParents_ret
#check predecessor_eq_none_iff
#check predecessor_edge
#check predecessor_distance
#check predecessor_eq_find?
#check predecessor_chain_unique
#check predecessor_chain_nodup
#check predecessor_relation_acyclic
#check BFSForest.pathTo?_source
#check BFSForest.pathTo?_eq_none_iff
#check BFSForest.pathTo?_spec
#check bfsWithParents_time
#check bfsWithParents_time_le
#check BFSForest.pathTo?_time
#check BFSForest.pathTo?_time_of_not_reachable

universe u
variable {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
variable (graph : DirectedAdjacency V) (source target parent : V) (distance : Nat)

example : (bfsWithParents graph source).ret.toBFSResult = bfs graph source :=
  bfsWithParents_ret graph source

example : (bfsWithParents graph source).ret.predecessor target = none ↔
    target = source ∨ ¬ graph.Reachable source target :=
  predecessor_eq_none_iff graph source target

example (saved : (bfsWithParents graph source).ret.predecessor target = some parent) :
    graph.Edge parent target :=
  predecessor_edge graph source target parent saved

example (saved : (bfsWithParents graph source).ret.predecessor target = some parent) :
    ∃ distance : Nat, (bfsWithParents graph source).ret.distance parent = some distance ∧
      (bfsWithParents graph source).ret.distance target = some (distance + 1) :=
  predecessor_distance graph source target parent saved

example (nonsource : target ≠ source) :
    (bfsWithParents graph source).ret.predecessor target =
      (bfs graph source).order.find?
        (fun vertex => (graph.adjacency vertex).contains target) :=
  predecessor_eq_find? graph source target nonsource

example (reachable : graph.Reachable source target) :
    ∃! chain : List V, chain.IsChainFromTo
      (fun parent child => (bfsWithParents graph source).ret.predecessor child = some parent)
      source target :=
  predecessor_chain_unique graph source target reachable

example : ¬ Relation.TransGen
    (fun parent child => (bfsWithParents graph source).ret.predecessor child = some parent)
    target target :=
  predecessor_relation_acyclic graph source target

example : ((bfsWithParents graph source).ret.pathTo? source source).ret = some [source] :=
  BFSForest.pathTo?_source (bfsWithParents graph source).ret source

example : ((bfsWithParents graph source).ret.pathTo? source target).ret = none ↔
    ¬ graph.Reachable source target :=
  BFSForest.pathTo?_eq_none_iff graph source target

example : (bfsWithParents graph source).time =
    graph.vertices.length +
      ((bfs graph source).order.map fun vertex => (graph.adjacency vertex).length).sum +
      (bfs graph source).order.length + ((bfs graph source).order.length - 1) :=
  bfsWithParents_time graph source

example : (bfsWithParents graph source).time ≤ 3 * graph.vertices.length +
    (graph.vertices.map fun vertex => (graph.adjacency vertex).length).sum :=
  bfsWithParents_time_le graph source

example (found : (bfs graph source).distance target = some distance) :
    ((bfsWithParents graph source).ret.pathTo? source target).time = 3 * distance + 2 :=
  BFSForest.pathTo?_time graph source target distance found

example (unreachable : ¬ graph.Reachable source target) :
    ((bfsWithParents graph source).ret.pathTo? source target).time = 2 :=
  BFSForest.pathTo?_time_of_not_reachable graph source target unreachable

end
