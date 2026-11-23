/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Engineering.Process.Drying

import Mathlib.Tactic.NormNum

/-!
# Tests for moisture basis conversion

Boundary checks for `PhyslibExt.Engineering.Process.Drying`: dry-solid
mass `3` and water mass `1` give wet basis `1 / 4` and dry basis `1 / 3`;
dry material is zero on both bases; no dry solids gives wet basis `1`,
outside the conversion.
-/

namespace Engineering.Process.Drying.Tests

open Engineering.Process.Drying

-- ms = 3, mw = 1 gives wet basis 1 / 4 and dry basis 1 / 3.
example : wetBasis 1 3 = 1 / 4 := by
  unfold wetBasis
  norm_num

example : dryBasis 1 3 = 1 / 3 := by
  rfl

example : dryOfWet (1 / 4 : ℝ) = 1 / 3 := by
  unfold dryOfWet
  norm_num

example : wetOfDry (1 / 3 : ℝ) = 1 / 4 := by
  unfold wetOfDry
  norm_num

-- Dry material has moisture zero on both bases.
example : wetBasis 0 3 = 0 ∧ dryBasis 0 3 = 0 := by
  constructor
  · unfold wetBasis
    norm_num
  · unfold dryBasis
    norm_num

-- No dry solids: the wet basis is 1, outside the conversion domain.
example : wetBasis 1 0 = 1 := by
  unfold wetBasis
  norm_num

end Engineering.Process.Drying.Tests
