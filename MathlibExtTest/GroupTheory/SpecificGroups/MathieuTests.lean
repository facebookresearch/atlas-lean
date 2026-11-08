/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.SpecificGroups.Mathieu

/-!
# Images of the standard Mathieu generators

These literal images come from GAP 4.15.1's degree-23 branch of `MathieuGroup`,
in `grp/basicprm.gi`, with labels 1 through 23 shifted to `Fin 23`.
Both checks enumerate every input, including cycle wraparound and fixed points.
-/

@[expose] public section

open MathieuGroup

set_option maxRecDepth 4096 in
/-- The GAP 23-cycle sends 23 to 1 in its original labeling. -/
example : (List.finRange 23).map (fun i => (m23Cycle i).val) =
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 0] := by
  decide

set_option maxRecDepth 4096 in
/-- The GAP product of four 5-cycles fixes the original labels 1, 2, and 6. -/
example : (List.finRange 23).map (fun i => (m23FiveCycles i).val) =
    [0, 1, 16, 12, 3, 5, 8, 17, 2, 6, 11, 22, 13, 18, 19, 14, 9, 10, 4, 21, 15, 20, 7] := by
  decide
