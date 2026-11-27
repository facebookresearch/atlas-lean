/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.DominatingSetDefs

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSet

/-- A path on three vertices is a well-formed instance. -/
example : WellFormed (3, [(0, 1), (1, 2)], 1) := by
  unfold WellFormed
  decide

/-- An edge endpoint out of range makes the instance malformed. -/
example : ¬ WellFormed (2, [(0, 2)], 1) := by
  unfold WellFormed
  decide

/-- A self-loop makes the instance malformed. -/
example : ¬ WellFormed (2, [(0, 0)], 1) := by
  unfold WellFormed
  decide

/-- An edge listed in both directions makes the instance malformed. -/
example : ¬ WellFormed (2, [(0, 1), (1, 0)], 1) := by
  unfold WellFormed
  decide

/-- A repeated edge makes the instance malformed. -/
example : ¬ WellFormed (2, [(0, 1), (0, 1)], 1) := by
  unfold WellFormed
  decide

/-- The empty graph on no vertices is dominated by the empty set. -/
example : DominatingSetFeasible (0, [], 0) := by
  refine ⟨∅, ?_, ?_⟩ <;> simp

end MetaMathlibExt.Complexity.NPComplete.DominatingSet
