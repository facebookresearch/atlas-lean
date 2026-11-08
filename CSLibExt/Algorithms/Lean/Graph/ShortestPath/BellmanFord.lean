/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.BellmanFord.Costs

/-!
# Bellman-Ford shortest paths

This facade exposes Bellman-Ford over ordered integer-weighted edge occurrences, together with
exact shortest-path, reachable-negative-cycle, predecessor, reconstruction, and cost theorems.

The implementation follows Cormen, Leiserson, Rivest, and Stein, *Introduction to Algorithms*,
fourth edition, Section 22.1 and Exercise 22.1-7. Proof infrastructure is split across the
documented `BellmanFord` implementation modules imported above.
-/
