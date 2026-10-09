/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.FloydWarshall.Correctness

/-!
# Floyd-Warshall all-pairs shortest paths

This facade exposes the executable algorithm, its exact event counts, shortest-distance
correctness under the no-negative-cycle hypothesis, and sound negative-diagonal detection.
-/
