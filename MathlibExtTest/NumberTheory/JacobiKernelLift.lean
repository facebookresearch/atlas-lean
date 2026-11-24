/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import MathlibExt.NumberTheory.JacobiKernelLift

open MetaMathlibExt

-- The class of 3 has negative Jacobi symbol modulo 7, and 45 has a repeated prime factor.
example : ∃ x : ZMod 315, IsUnit x ∧ jacobiSym x.val 315 = 1 ∧
    ZMod.castHom (by decide : 7 ∣ 315) (ZMod 7) x = 3 := by
  obtain ⟨x, hx, hred⟩ := units_subset_image_jacobi_kernel 45 7 (by decide) (by norm_num)
    (by decide) 3 ((ZMod.isUnit_iff_coprime 3 7).mpr (by decide))
  exact ⟨x, hx.1, hx.2, hred⟩

-- The unique residue modulo 1 is also a unit and has a lift in the kernel.
example : ∃ x : ZMod 3, IsUnit x ∧ jacobiSym x.val 3 = 1 ∧
    ZMod.castHom (one_dvd 3) (ZMod 1) x = 0 := by
  obtain ⟨x, hx, hred⟩ := units_subset_image_jacobi_kernel 3 1 (by decide) (by norm_num)
    (by decide) 0 ((ZMod.isUnit_iff_coprime 0 1).mpr (by decide))
  exact ⟨x, hx.1, hx.2, hred⟩

-- 15 is not a square: the units with Jacobi symbol 1 have index two. The class of 2 lies in this
-- subgroup, as (2/15) = (2/3) (2/5) = 1, and the class of 7 does not, as (7/15) = (1/3) (2/5) = -1.
example : ∃ H : Subgroup (ZMod 15)ˣ, H.index = 2 ∧ ZMod.unitOfCoprime 2 (by decide) ∈ H ∧
    ZMod.unitOfCoprime 7 (by decide) ∉ H := by
  obtain ⟨H, hH, hidx⟩ := (jacobi_kernel_index_two 15 (by decide)).1 (by norm_num)
  refine ⟨H, hidx, ?_, ?_⟩ <;> rw [hH, ZMod.coe_unitOfCoprime, ZMod.val_natCast] <;> norm_num

-- Modulo the prime 3 the subgroup has index two in a group of two units: 2 is not in it.
example : ∃ H : Subgroup (ZMod 3)ˣ, H.index = 2 ∧ ZMod.unitOfCoprime 2 (by decide) ∉ H := by
  obtain ⟨H, hH, hidx⟩ := (jacobi_kernel_index_two 3 (by decide)).1 (by norm_num)
  refine ⟨H, hidx, ?_⟩
  rw [hH, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  norm_num

-- 9 = 3 * 3 is a square, so every unit modulo 9 has Jacobi symbol 1.
example (u : (ZMod 9)ˣ) : jacobiSym ((u : ZMod 9).val : ℤ) 9 = 1 :=
  (jacobi_kernel_index_two 9 (by decide)).2 ⟨3, rfl⟩ u

-- The boundary case 1 = 1 * 1: the unique unit of `ZMod 1` has Jacobi symbol 1.
example (u : (ZMod 1)ˣ) : jacobiSym ((u : ZMod 1).val : ℤ) 1 = 1 :=
  (jacobi_kernel_index_two 1 odd_one).2 ⟨1, rfl⟩ u

-- For odd non-square `n`, exactly half of the `φ(n)` units have Jacobi symbol 1.
example (n : ℕ) (hn : Odd n) (hsq : ¬ IsSquare n) : ∃ H : Subgroup (ZMod n)ˣ,
    (∀ u : (ZMod n)ˣ, u ∈ H ↔ jacobiSym ((u : ZMod n).val : ℤ) n = 1) ∧
      2 * Nat.card H = n.totient := by
  obtain ⟨H, hH, hidx⟩ := (jacobi_kernel_index_two n hn).1 hsq
  have : NeZero n := ⟨hn.pos.ne'⟩
  refine ⟨H, hH, ?_⟩
  rw [← hidx, Subgroup.index_mul_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
