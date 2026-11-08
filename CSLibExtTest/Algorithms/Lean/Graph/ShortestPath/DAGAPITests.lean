/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.DAG

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.DAGShortestPathsAPITests

open BellmanFord DAGShortestPaths

example {n : Nat} (edges : List (Edge n)) (source : Fin n) (order : List (Fin n))
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order) :
    (run edges source order horder).time.vertexVisits = n :=
  run_vertexVisits edges source order horder

example {n : Nat} (edges : List (Edge n)) (source : Fin n) (order : List (Fin n))
    (horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order) :
    (run edges source order horder).time.edgeRelaxations = edges.length :=
  run_edgeRelaxations edges source order horder

example {n : Nat} (edges : List (Edge n)) (source : Fin n) (result : Distances n) :
    (dagShortestPaths edges source).ret = .ok result ↔
      ∃ order, ∃ horder : TopologicalSort.IsTopologicalOrder (toDirectedAdjacency edges) order,
        TopologicalSort.sort (toDirectedAdjacency edges) = .success order ∧
        result = (run edges source order horder).ret :=
  dagShortestPaths_eq_ok_iff edges source result

example {n : Nat} (edges : List (Edge n)) (source : Fin n)
    (processed remaining : List (Fin n)) :
    (dagShortestPaths edges source).ret = .error (processed, remaining) ↔
      TopologicalSort.sort (toDirectedAdjacency edges) = .failure processed remaining :=
  dagShortestPaths_eq_error_iff edges source processed remaining

#check dagShortestPaths_returns_iff_acyclic
#check dagShortestPaths_distance_spec
#check dagShortestPaths_distance_eq_none_iff
#check dagShortestPaths_pathTo?_spec
#check dagShortestPaths_failure_cycle

end Cslib.Algorithms.Lean.DAGShortestPathsAPITests
