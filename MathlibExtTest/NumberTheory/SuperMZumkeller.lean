/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SuperMZumkeller

/-! # Tests for the divisor product -/

open MathlibExt.NumberTheory.SuperMZumkellerWanted

example : divisorProd 0 = 1 := by decide

example : divisorProd 1 ^ 2 = 1 := divisorProd_sq 1 (by decide)

-- The middle divisor of a square pairs with itself.
example : divisorProd 9 = 27 := by decide

example : divisorProd 9 ^ 2 = 9 ^ 3 := divisorProd_sq 9 (by decide)

example : divisorProd 6 ^ 2 = 6 ^ 4 := divisorProd_sq 6 (by decide)

example : IsKMPerfect 2 6 := rfl

-- At one, the empty subset and its complement both have product one.
example : IsSuperMZumkeller 1 := by
  exact ⟨∅, Finset.empty_subset _, by decide⟩
