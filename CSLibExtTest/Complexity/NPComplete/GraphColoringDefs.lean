/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.GraphColoringDefs

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoring

/-- A path on three vertices with two colors is a well-formed instance. -/
example : WellFormed ((3, [(0, 1), (1, 2)], 2) : GraphColoringInstance) := by
  unfold WellFormed
  decide

/-- The empty graph on zero vertices is a well-formed instance. -/
example : WellFormed ((0, [], 0) : GraphColoringInstance) := by
  unfold WellFormed
  decide

/-- A self-loop makes an instance malformed. -/
example : ¬ WellFormed ((2, [(1, 1)], 1) : GraphColoringInstance) := by
  unfold WellFormed
  decide

/-- An edge endpoint outside `{0, …, n - 1}` makes an instance malformed. -/
example : ¬ WellFormed ((2, [(0, 2)], 2) : GraphColoringInstance) := by
  unfold WellFormed
  decide

/-- Listing an edge in both directions makes an instance malformed. -/
example : ¬ WellFormed ((2, [(0, 1), (1, 0)], 2) : GraphColoringInstance) := by
  unfold WellFormed
  decide

/-- A repeated edge makes an instance malformed. -/
example : ¬ WellFormed ((2, [(0, 1), (0, 1)], 2) : GraphColoringInstance) := by
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.GraphColoring
