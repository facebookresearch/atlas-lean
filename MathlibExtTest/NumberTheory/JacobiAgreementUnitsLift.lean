/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime
import MathlibExt.NumberTheory.JacobiAgreementUnitsLift

open MetaMathlibExt

-- The modulus `63 = 9 * 7` is not squarefree, but `7` is coprime to `63 / 7 = 9`. The
-- nonresidue `3` modulo `7` lifts to a unit modulo `63` whose Jacobi symbol modulo `63` is
-- `(3/7) = -1`.
example : ∃ x : ZMod 63, IsUnit x ∧ jacobiSym x.val 63 = -1 ∧
    ZMod.castHom (by decide : 7 ∣ 63) (ZMod 7) x = 3 := by
  obtain ⟨x, ⟨hu, hJ⟩, h7⟩ := units_prime_subset_image_jacobi_eq_legendre 63 7 (by decide)
    (by norm_num) (by decide) (by decide) 3 (by decide)
  refine ⟨x, hu, ?_, h7⟩
  have hx7 : ((x.val : ℕ) : ZMod 7) = 3 := by
    rw [← h7, ZMod.castHom_apply, ZMod.cast_eq_val]
  have hmod : ((x.val : ℕ) : ℤ) % (7 : ℕ) = (3 : ℤ) % (7 : ℕ) := by
    rw [← ZMod.intCast_eq_intCast_iff', Int.cast_natCast, hx7]
    rfl
  rw [hJ, jacobiSym.mod_left' hmod]
  norm_num

-- When `n = p'` is prime, `n / p' = 1` and every unit modulo `p'` lifts to itself.
example : ∃ x : ZMod 7, IsUnit x ∧ jacobiSym x.val 7 = jacobiSym x.val 7 ∧
    ZMod.castHom (dvd_refl 7) (ZMod 7) x = 3 := by
  obtain ⟨x, ⟨hu, hJ⟩, h7⟩ := units_prime_subset_image_jacobi_eq_legendre 7 7 (by decide)
    (by norm_num) (dvd_refl 7) (by decide) 3 (by decide)
  exact ⟨x, hu, hJ, h7⟩
