/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ErdosProblem818
import Mathlib.Tactic.NormNum

/-! # Tests for the small-doubling product bound -/

open scoped Pointwise
open MathlibExt.NumberTheory.ErdosProblem818Wanted

-- The constants for doubling at most two work for both a two-element set containing zero
-- and a three-element set containing both signs.
example : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
    c * 2 ^ 2 / (Real.log 2) ^ C ≤ 2 ∧ c * 3 ^ 2 / (Real.log 3) ^ C ≤ 3 := by
  obtain ⟨C, hC, c, hc, h⟩ := conjecture_holds 2 (by norm_num)
  refine ⟨C, hC, c, hc, ?_, ?_⟩
  · let A : Finset ℤ := {-1, 0}
    have hn : A.card = 2 := by decide
    have hs : (A + A).card = 3 := by decide
    have hp : (A * A).card = 2 := by decide
    simpa only [hn, hp, Nat.cast_ofNat] using h A hn.ge (by rw [hs, hn]; norm_num)
  · let A : Finset ℤ := {-1, 0, 1}
    have hn : A.card = 3 := by decide
    have hs : (A + A).card = 5 := by decide
    have hp : (A * A).card = 3 := by decide
    simpa only [hn, hp, Nat.cast_ofNat] using
      h A (by omega) (by rw [hs, hn]; norm_num)
