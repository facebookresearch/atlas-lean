/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime
import MathlibExt.NumberTheory.JacobiAgreementChineseRemainder

open MetaMathlibExt

-- `2` has Jacobi symbol `1` modulo `15 = 105 / 7` although it is a nonresidue modulo `3` and
-- modulo `5`, and `3` is a nonresidue modulo `7`. The lift agrees with `3` modulo `7`, so its
-- Jacobi symbol modulo `105` is `-1`: it lies in `L(105; 7)` but outside the kernel `S(105)`.
example : ∃ x : ZMod 105, IsUnit x ∧ jacobiSym x.val 105 = -1 ∧
    ZMod.castHom (by decide : 15 ∣ 105) (ZMod 15) x = 2 ∧
    ZMod.castHom (by decide : 7 ∣ 105) (ZMod 7) x = 3 := by
  have hsf : Squarefree 105 := by
    rw [show 105 = 3 * 5 * 7 by rfl]
    exact Nat.squarefree_mul_iff.mpr ⟨by norm_num, Nat.squarefree_mul_iff.mpr ⟨by norm_num,
      Nat.prime_three.prime.squarefree, Nat.prime_five.prime.squarefree⟩,
      (by norm_num : Nat.Prime 7).prime.squarefree⟩
  have hval : (2 : ZMod (105 / 7)).val = 2 := rfl
  obtain ⟨x, ⟨hu, hJ⟩, h15, h7⟩ := jacobi_kernel_prod_units_subset_crt_image 105 7 (by decide)
    hsf (by norm_num) (by norm_num) 2 ⟨by decide, by rw [hval]; norm_num⟩ 3 (by decide)
  refine ⟨x, hu, ?_, h15, h7⟩
  have hx7 : ((x.val : ℕ) : ZMod 7) = 3 := by
    rw [← h7, ZMod.castHom_apply, ZMod.cast_eq_val]
  have hmod : ((x.val : ℕ) : ℤ) % (7 : ℕ) = (3 : ℤ) % (7 : ℕ) := by
    rw [← ZMod.intCast_eq_intCast_iff', Int.cast_natCast, hx7]
    rfl
  rw [hJ, jacobiSym.mod_left' hmod]
  norm_num

-- When `n = p'` is prime, `n / p' = 1`: the residue `0` of `ZMod 1` is a unit with Jacobi
-- symbol `1`, so every unit modulo `p'` lifts.
example : ∃ x : ZMod 7, IsUnit x ∧ ZMod.castHom (dvd_refl 7) (ZMod 7) x = 3 := by
  obtain ⟨x, ⟨hu, -⟩, -, h7⟩ := jacobi_kernel_prod_units_subset_crt_image 7 7 (by decide)
    (by norm_num : Nat.Prime 7).prime.squarefree (by norm_num) (dvd_refl 7) 0
    ⟨by decide, by norm_num⟩ 3 (by decide)
  exact ⟨x, hu, h7⟩
