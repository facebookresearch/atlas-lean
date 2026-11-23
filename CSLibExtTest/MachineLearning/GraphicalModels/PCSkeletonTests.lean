/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.PCSkeleton

namespace Cslib.MachineLearning.GraphicalModels.PCSkeleton

/-- The XOR collider law is not adjacency-faithful: root `0` is independent of its
child `2` although they are adjacent. -/
example : ¬ xorNet.AdjacencyFaithful (lawOracle xorNet.joint) :=
  xorNet_not_adjacencyFaithful

/-- Run against the XOR law, the adjacency phase deletes the true `0`–`2` edge, so its
output is not the network's skeleton. -/
example : (pcAdjacency (lawOracle xorNet.joint)).skeleton ≠ xorNet.skeleton :=
  pcAdjacency_xorNet_ne_skeleton

/-- The XOR law is Markov to its graph. -/
example : xorNet.MarkovOracle (lawOracle xorNet.joint) := xorNet_markovOracle

end Cslib.MachineLearning.GraphicalModels.PCSkeleton
