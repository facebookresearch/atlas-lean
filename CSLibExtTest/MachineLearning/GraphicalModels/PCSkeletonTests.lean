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


/-- An oracle that declares every query independent. -/
private def alwaysIndep : CIOracle 3 where
  Indep _ _ _ := True
  decIndep _ _ _ := isTrue trivial

/-- An oracle that declares every query dependent. -/
private def neverIndep : CIOracle 3 where
  Indep _ _ _ := False
  decIndep _ _ _ := isFalse id

/-- Direct computation: against the always-independent oracle the phase deletes
every edge already in round 0, recording the empty separator. -/
example : ∀ i j : Fin 3, ¬ (pcAdjacency alwaysIndep).skeleton.Adj i j := by decide

example : (pcAdjacency alwaysIndep).sepset 0 2 = ∅ := by decide

/-- Direct computation: against the never-independent oracle the phase keeps the
complete skeleton. -/
example : ∀ i j : Fin 3, (pcAdjacency neverIndep).skeleton.Adj i j ↔ i ≠ j := by decide

end Cslib.MachineLearning.GraphicalModels.PCSkeleton
