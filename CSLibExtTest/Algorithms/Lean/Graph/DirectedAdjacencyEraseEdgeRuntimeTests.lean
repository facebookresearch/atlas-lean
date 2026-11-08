/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.DirectedAdjacency.EraseEdge
public meta import CSLibExt.Algorithms.Lean.Graph.DirectedAdjacency.EraseEdge
public meta import CSLibExt.Algorithms.Lean.Graph.DirectedAdjacency

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.DirectedAdjacencyEraseEdgeRuntimeTests

open DirectedAdjacency

inductive Vertex
  | a
  | b
  | c
  | d
  deriving DecidableEq, Repr

open Vertex

private def runtimeGraph : DirectedAdjacency Vertex where
  vertices := [a, b, c, d]
  vertices_nodup := by decide
  vertices_complete vertex := by cases vertex <;> simp
  adjacency
    | a => [b, c, b]
    | b => [a]
    | c => []
    | d => [d, d]

#eval (eraseEdge runtimeGraph a b).vertices
#eval (eraseEdge runtimeGraph a b).adjacency a
#eval (eraseEdge runtimeGraph a b).adjacency b
#eval (eraseEdge runtimeGraph a b).adjacency d
#eval (eraseEdge runtimeGraph d d).adjacency d
#eval (eraseEdge runtimeGraph c a).adjacency c
#eval (eraseEdge (eraseEdge runtimeGraph a b) a b).adjacency a
#eval (eraseEdge runtimeGraph a b).hasEdge a b
#eval (eraseEdge runtimeGraph a b).hasEdge a c
#eval (eraseEdge runtimeGraph a b).hasEdge b a

example : (eraseEdge runtimeGraph a b).adjacency a = [c] := by
  decide

example : (eraseEdge runtimeGraph a b).adjacency d = [d, d] := by
  decide

example : (eraseEdge runtimeGraph d d).hasEdge d d = false := by
  decide

example : (eraseEdge runtimeGraph a b).Reachable a c := by
  exact reachable_iff_exists_walk.mpr
    ⟨1, Relation.RelatesInSteps.single
      (by simp [DirectedAdjacency.Edge, eraseEdge, runtimeGraph])⟩

end Cslib.Algorithms.Lean.DirectedAdjacencyEraseEdgeRuntimeTests
