/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Set.Card
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

-- For `n = 6` and `a = 3` the two integers are `(-1 - 3) / 2 = -2` and `(6 - 1 - 3) / 2 = 1`,
-- so the solutions are `4` and `1` in `ZMod 6`.
example : {x : ZMod 6 | x = -1 - x - 3} = {4, 1} := by
  rw [reflection_shift_solutions_even_odd 6 3 (by decide) (by decide)]
  exact congrArg₂ (fun b c => ({b, c} : Set (ZMod 6))) (by decide) (by decide)

-- Both residues do solve the equation: `-1 - 4 - 3 = -8 = 4` and `-1 - 1 - 3 = -5 = 1`.
example : (4 : ZMod 6) = -1 - 4 - 3 ∧ (1 : ZMod 6) = -1 - 1 - 3 := by decide

-- For `n = 8` and `a = 5`, every solution is `(-1 - 5) / 2 = -3 = 5` or `(8 - 1 - 5) / 2 = 1`.
example (x : ZMod 8) (hx : x = -1 - x - 5) : x = 5 ∨ x = 1 := by
  have h : x ∈ {x : ZMod 8 | x = -1 - x - 5} := hx
  rw [reflection_shift_solutions_even_odd 8 5 (by decide) (by decide)] at h
  rcases h with h | h
  · exact Or.inl (h.trans (by decide))
  · exact Or.inr ((Set.mem_singleton_iff.mp h).trans (by decide))

-- Edge case `n = 2`: the only shift with odd representative is `1`, and the two residues
-- `(-1 - 1) / 2 = -1 = 1` and `(2 - 1 - 1) / 2 = 0` exhaust `ZMod 2`.
example : {x : ZMod 2 | x = -1 - x - 1} = Set.univ := by
  rw [reflection_shift_solutions_even_odd 2 1 (by decide) (by decide), Set.eq_univ_iff_forall]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  decide

-- For every even modulus and every shift with odd representative, the residue of
-- `(-1 - a.val) / 2` solves the equation.
example (n : ℕ) [NeZero n] (a : ZMod n) (hn : Even n) (ha : Odd a.val) :
    ((((-1 : ℤ) - a.val) / 2 : ℤ) : ZMod n) =
      -1 - ((((-1 : ℤ) - a.val) / 2 : ℤ) : ZMod n) - a := by
  have h : ((((-1 : ℤ) - a.val) / 2 : ℤ) : ZMod n) ∈ {x : ZMod n | x = -1 - x - a} := by
    rw [reflection_shift_solutions_even_odd n a hn ha]
    exact Set.mem_insert _ _
  exact h

-- The two residues differ by `n / 2`, so the equation always has exactly two solutions.
example (n : ℕ) [NeZero n] (a : ZMod n) (hn : Even n) (ha : Odd a.val) :
    {x : ZMod n | x = -1 - x - a}.ncard = 2 := by
  rw [reflection_shift_solutions_even_odd n a hn ha, Set.ncard_pair]
  obtain ⟨k, hk⟩ := hn
  obtain ⟨j, hj⟩ := ha
  have hk0 : 0 < k := by
    have := NeZero.pos n
    omega
  rw [Ne, ZMod.intCast_eq_intCast_iff_dvd_sub, hj, hk]
  push_cast
  rw [show ((k : ℤ) + k - 1 - (2 * j + 1)) / 2 - (-1 - (2 * j + 1)) / 2 = k by omega]
  intro h
  have := Int.le_of_dvd (by omega) h
  omega

-- The hypothesis `Even n` is needed: modulo `5` with `a = 1`, the second residue is
-- `(5 - 1 - 1) / 2 = 1` (integer division rounds down), and `1` is not a solution.
example : (((((5 : ℕ) : ℤ) - 1 - (1 : ZMod 5).val) / 2 : ℤ) : ZMod 5) = 1 ∧
    (1 : ZMod 5) ≠ -1 - 1 - 1 := by decide

-- The hypothesis `Odd a.val` is needed: modulo `4` with `a = 2` the equation says
-- `2 * x = -3`, and has no solution because `2 * x` is even.
example : ∀ x : ZMod 4, x ≠ -1 - x - 2 := by decide

end MetaMathlibExt
