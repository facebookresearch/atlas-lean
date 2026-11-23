/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Beatty.FloorFiber
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt.beatty_floor_fiber_card_succ_iff

private theorem two_thirds (t : ℕ) :
    {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * (2 / 3)⌋ = t}.ncard = 2 ↔
      {n : ℕ | 0 < n ∧ n * 2 = t}.ncard = 1 := by
  have hfloor (n : ℕ) : ⌊(n : ℝ) * 2⌋ = ((n * 2 : ℕ) : ℤ) := by
    rw [← Int.floor_natCast (R := ℝ) (n * 2)]
    simp
  simpa only [show (2 / 3 : ℝ) / (1 - 2 / 3) = 2 by norm_num, hfloor, Nat.cast_inj] using
    beatty_floor_fiber_card_succ_iff (α := 2 / 3) (k := 1) (by norm_num) (by norm_num) t

-- The closed lower endpoint includes n = 3, for which n * (2 / 3) = 2.
example : {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * (2 / 3)⌋ = 2}.ncard = 2 := by
  apply (two_thirds 2).mpr
  have h : {n : ℕ | 0 < n ∧ n * 2 = 2} = {1} := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    omega
  rw [h, Set.ncard_singleton]

-- At t = 0 the only candidate for slope 2 is the excluded index zero.
example : {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * (2 / 3)⌋ = 0}.ncard ≠ 2 := by
  apply (two_thirds 0).not.mpr
  have h : {n : ℕ | 0 < n ∧ n * 2 = 0} = ∅ := by
    ext n
    simp [Nat.pos_iff_ne_zero]
  rw [h, Set.ncard_empty]
  decide

end MetaMathlibExt.beatty_floor_fiber_card_succ_iff
