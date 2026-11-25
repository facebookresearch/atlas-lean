/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalks

/-! # Tests for Fibonacci walk counts -/

namespace MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted

-- Length zero has only the even index.
example : evenFibWalkCount 0 = 1 ∧ oddFibWalkCount 0 = 0 := by decide +kernel

-- Length one is the smallest length covered by the theorem.
example : evenFibWalkCount 1 = oddFibWalkCount 1 :=
  evenFibWalkCount_odd_length_eq_oddFibWalkCount 1 le_rfl

-- At length five the three distinct summands are paired by reflection.
example : evenFibWalkCount 5 = 19 ∧ oddFibWalkCount 5 = 19 := by decide +kernel

example : higherFibWalk fibQ 2 5 = 38 ∧ fibWalkCount 5 = 38 := by decide +kernel

example : IsStandardHigherFib 1 (fun _ => 1) := by
  simp [IsStandardHigherFib, IsHigherFibRecurrence]

example : weightedHigherFibMomentSum fibQ 2 (-1) 1 2 = 0 := by decide
example : weightedHigherFibMomentSum fibQ 2 2 1 2 = 18 := by decide +kernel

end MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted
