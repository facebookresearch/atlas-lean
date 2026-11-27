/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.GroupTheory.SpecificGroups.Dihedral
import MathlibExt.GroupTheory.LargeAutomorphismCyclicSubgroupKourovka15Problem32

/-!
# Dihedral boundary case for Kourovka Problem 15.32

The reflection shift gives the required automorphism at `p = 2`, `k = 1`, and `m = 66`.
-/

namespace MathlibExtTest.GroupTheory.LargeAutomorphismCyclicSubgroupKourovka15Problem32

open MathlibExt.GroupTheory.LargeAutomorphismCyclicSubgroupKourovka15Problem32Wanted

open DihedralGroup

/-- Fix each rotation and advance each reflection by one. -/
private def shiftReflection (n : ℕ) : MulAut (DihedralGroup n) where
  toFun
    | r i => r i
    | sr i => sr (i + 1)
  invFun
    | r i => r i
    | sr i => sr (i - 1)
  left_inv := by rintro (i | i) <;> simp
  right_inv := by rintro (i | i) <;> simp
  map_mul' := by
    rintro (i | i) (j | j) <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

private theorem shift_pow_r (n j : ℕ) (i : ZMod n) :
    (shiftReflection n ^ j) (r i) = r i := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', MulAut.mul_apply, ih]
    rfl

private theorem shift_pow_sr (n j : ℕ) (i : ZMod n) :
    (shiftReflection n ^ j) (sr i) = sr (i + (j : ZMod n)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', MulAut.mul_apply, ih, Nat.cast_succ]
    change sr (i + (j : ZMod n) + 1) = sr (i + ((j : ZMod n) + 1))
    rw [add_assoc]

private theorem orderOf_shift (n : ℕ) : orderOf (shiftReflection n) = n := by
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_iff_pow_eq_one.mpr
    apply DFunLike.ext
    rintro (i | i)
    · exact shift_pow_r n n i
    · rw [shift_pow_sr, MulAut.one_apply, ZMod.natCast_self, add_zero]
  · have h := DFunLike.congr_fun (pow_orderOf_eq_one (shiftReflection n)) (sr 0)
    simp only [shift_pow_sr, MulAut.one_apply, zero_add, sr.injEq,
      ZMod.natCast_eq_zero_iff] at h
    exact h

example : ∃ C : Subgroup (DihedralGroup (2 ^ 65)), IsCyclic C ∧ C.index = 2 := by
  simpa using cyclicSubgroupOfIndexFromLargeAutomorphism_holds
    2 1 66 Nat.prime_two (by decide) (DihedralGroup (2 ^ 65))
    (DihedralGroup.nat_card.trans (pow_succ' 2 65).symm)
    ⟨shiftReflection (2 ^ 65), orderOf_shift (2 ^ 65)⟩

end MathlibExtTest.GroupTheory.LargeAutomorphismCyclicSubgroupKourovka15Problem32
