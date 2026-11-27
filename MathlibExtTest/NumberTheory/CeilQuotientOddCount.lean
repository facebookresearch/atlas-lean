/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CeilQuotientOddCount

/-!
# Tests for the ceiling and floor quotient parity counts
-/

open MetaMathlibExt

-- At zero both denominator intervals are empty. At one the sole ceiling is odd.
example : floorQuotientOddCount 0 = 0 ∧ ceilQuotientOddCount 0 = 0 ∧
    ceilQuotientOddCount 1 = 1 := by decide +kernel

-- At three the odd ceilings occur at denominators one and three.
example : ceilQuotientOddCount 3 = 2 := by decide +kernel

-- For n = 3 all three floor quotients are odd, so only the new endpoint contributes.
example : (ceilQuotientOddCount 4 : ℤ) = 1 := by
  rw [ceilQuotientOddCount_succ_eq 3]
  decide
