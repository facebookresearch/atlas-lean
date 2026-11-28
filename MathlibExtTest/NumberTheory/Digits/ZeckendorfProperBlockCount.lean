/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.ZeckendorfProperBlockCount

/-! # Tests for counting proper Zeckendorf blocks -/

open MetaMathlibExt

-- On a singleton interval, zero is an admissible final digit.
example : IsProperLStarBlock [2, 3, 0] 0 4 4 := by
  refine ⟨le_rfl, fun i hi => ?_, by decide, fun _ _ => rfl⟩
  exact (maxLStarBlock_of_lt hi).symm

-- The interval starts away from zero and its endpoint wraps around to the second digit.
example : {ζ : ℕ → ℕ | IsProperLStarBlock [2, 3, 0] ζ 4 8}.ncard = 3 :=
  ncard_properLStarBlock [2, 3, 0] (by decide) (by decide) (by decide)

-- A zero endpoint bound gives an empty set of blocks.
example : {ζ : ℕ → ℕ | IsProperLStarBlock [2, 3, 0] ζ 4 6} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro ζ hζ
  exact Nat.not_lt_zero _ hζ.2.2.1
