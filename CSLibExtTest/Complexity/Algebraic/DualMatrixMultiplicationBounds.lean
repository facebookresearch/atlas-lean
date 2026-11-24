/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Complexity.Algebraic.DualMatrixMultiplicationBounds
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

namespace Cslib.Complexity.Algebraic.DualMatrixMultiplicationBoundsWanted.Tests

-- Even over the two-element field, aspect 3/2 requires exponent strictly greater than two.
example : 2 < rectangularCircuitExponent (ZMod 2) (3 / 2) := by
  apply lt_of_le_of_ne (two_le_rectangularCircuitExponent _ _)
  intro he
  have h := (le_dualCircuitExponent (ZMod 2) (k := 3 / 2) (by norm_num) he.symm).trans
    (upperBoundOne (ZMod 2))
  rw [← ENNReal.ofReal_one] at h
  have := (ENNReal.ofReal_le_ofReal_iff zero_le_one).mp h
  norm_num at this

end Cslib.Complexity.Algebraic.DualMatrixMultiplicationBoundsWanted.Tests
