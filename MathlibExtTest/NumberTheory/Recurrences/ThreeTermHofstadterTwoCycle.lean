/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.ThreeTermHofstadterTwoCycle

/-! # Boundary cases for the padded two-cycle -/

open MetaMathlibExt

-- At K = 1 and M = K + 5 the sixth term uses the padding at index zero.
-- Lowering M by one makes it read the first initial value instead.
example : threeTermHofstadterTerm true [-7, 2, 6, 2] 6 = some 2 ∧
    threeTermHofstadterTerm true [-7, 2, 5, 2] 6 = some (-5) := by
  decide

-- After any single initial value the even offsets double indefinitely at the threshold.
example (x : ℤ) (k : ℕ) :
    threeTermHofstadterTerm true [x, 2, 6, 2] (1 + 2 * (k + 1)) = some (2 ^ k * 6) := by
  exact (threeTermHofstadter_twoCycle (K := 1) (by decide) (M := 6) (by decide)
    [x] rfl (k + 1)).2 (by omega)
