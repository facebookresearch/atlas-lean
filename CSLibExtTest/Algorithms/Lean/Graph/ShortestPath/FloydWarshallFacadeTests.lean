/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.FloydWarshall

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.FloydWarshallFacadeTests

/-- error: Unknown constant `Cslib.Algorithms.Lean.FloydWarshall.floydWarshall.initializeRow` -/
#guard_msgs in
#check Cslib.Algorithms.Lean.FloydWarshall.floydWarshall.initializeRow

/-- error: Unknown constant `Cslib.Algorithms.Lean.FloydWarshall.floydWarshall.buildInitial` -/
#guard_msgs in
#check Cslib.Algorithms.Lean.FloydWarshall.floydWarshall.buildInitial

/-- error: Unknown constant `Cslib.Algorithms.Lean.FloydWarshall.floydWarshall.buildStageRow` -/
#guard_msgs in
#check Cslib.Algorithms.Lean.FloydWarshall.floydWarshall.buildStageRow

/-- error: Unknown constant `Cslib.Algorithms.Lean.FloydWarshall.floydWarshall.buildStage` -/
#guard_msgs in
#check Cslib.Algorithms.Lean.FloydWarshall.floydWarshall.buildStage

/-- error: Unknown constant `Cslib.Algorithms.Lean.FloydWarshall.floydWarshall.runStages` -/
#guard_msgs in
#check Cslib.Algorithms.Lean.FloydWarshall.floydWarshall.runStages

end Cslib.Algorithms.Lean.FloydWarshallFacadeTests
