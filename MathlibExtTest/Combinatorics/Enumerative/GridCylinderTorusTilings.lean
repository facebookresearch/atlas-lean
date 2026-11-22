/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.GridCylinderTorusTilings

/-! # Tests for `MathlibExt.Combinatorics.Enumerative.GridCylinderTorusTilings` -/

namespace MetaMathlibExt

-- For `n = 5` and `a = 2` the coefficient is `(5 + 1) / 2 = 3`, and the unique solution is
-- `3 * (-1 - 2) = -9 = 1` in `ZMod 5`.
example : {x : ZMod 5 | x = -1 - x - 2} = {1} := by
  rw [reflection_shift_solutions_odd 5 2 (by decide)]
  exact congrArg _ (by decide)

-- That residue does solve the equation: `-1 - 1 - 2 = -4 = 1` in `ZMod 5`.
example : (1 : ZMod 5) = -1 - 1 - 2 := by decide

-- For `n = 7` and `a = 3`, every solution equals `4 * (-1 - 3) = -16 = 5` in `ZMod 7`.
example (x : ZMod 7) (hx : x = -1 - x - 3) : x = 5 := by
  have h : x ∈ {x : ZMod 7 | x = -1 - x - 3} := hx
  rw [reflection_shift_solutions_odd 7 3 (by decide), Set.mem_singleton_iff] at h
  exact h.trans (by decide)

-- Edge case `n = 1`: `ZMod 1` has a single element, and it is the solution for every `a`.
example (a : ZMod 1) : {x : ZMod 1 | x = -1 - x - a} = {0} := by
  rw [reflection_shift_solutions_odd 1 a odd_one]
  exact congrArg _ (Subsingleton.elim _ _)

-- For every odd modulus and every shift the equation has exactly one solution.
example (n : ℕ) [NeZero n] (a : ZMod n) (hn : Odd n) : ∃! x : ZMod n, x = -1 - x - a := by
  obtain ⟨hmem, huniq⟩ :=
    Set.eq_singleton_iff_unique_mem.mp (reflection_shift_solutions_odd n a hn)
  exact ⟨_, hmem, huniq⟩

-- The hypothesis `Odd n` is needed: modulo `4` the equation `x = -1 - x - 0` says `2 * x = -1`,
-- and has no solution because `2 * x` is even.
example : ∀ x : ZMod 4, x ≠ -1 - x - 0 := by decide

end MetaMathlibExt
