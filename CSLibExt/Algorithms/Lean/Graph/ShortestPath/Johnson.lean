/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.Johnson.Correctness
public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.Johnson.Costs

/-!
# Integer Johnson all-pairs shortest paths

The five-name facade provides the actual signed-weight Johnson composition with complete
distance/failure correctness and exact selected-event counts for its dense specialization.
General real weights, sparse-heap source bounds, full machine/bit costs and predecessor matrices
remain separate extensions; the selected-event polynomial does not assert those bounds.
-/
