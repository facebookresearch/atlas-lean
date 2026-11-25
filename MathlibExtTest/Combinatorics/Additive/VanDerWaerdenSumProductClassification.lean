/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.VanDerWaerdenSumProductClassification

open MetaMathlibExt

-- The largest vanishing modulus supplies two consecutive blocks even on the constant unit word.
example : ∃ l : ℕ, 1 < l ∧ 8 ∣ l + 1 := by
  have h := (sumAddMulProd_one_classification (n := 8) (hn := by decide)).2.1 (by decide)
  obtain ⟨l, hl, s, hs⟩ := h 2 (by decide) (fun _ => 1)
  refine ⟨l, hl, (ZMod.natCast_eq_zero_iff (l + 1) 8).mp ?_⟩
  simpa [sumAddMulProdFamily] using hs 1 (by decide)

-- Modulus six attains the exact threshold between one and two blocks.
example : IsMVanishingFamily 1 (sumAddMulProdFamily (1 : ZMod 6)) ∧
    ¬ IsMVanishingFamily 2 (sumAddMulProdFamily (1 : ZMod 6)) := by
  obtain ⟨h₁, h₂⟩ := (sumAddMulProd_one_classification (n := 6) (hn := by decide)).2.2 rfl
  exact ⟨h₁, h₂ 2 (by decide)⟩

-- A prime modulus above seven and a mixed prime power multiple both fail at one block.
example : ¬ IsMVanishingFamily 1 (sumAddMulProdFamily (1 : ZMod 11)) :=
  (sumAddMulProd_one_classification (hn := by decide)).1 (by decide) 1 (by decide)

example : ¬ IsMVanishingFamily 1 (sumAddMulProdFamily (1 : ZMod 24)) :=
  (sumAddMulProd_one_classification (hn := by decide)).1 (by decide) 1 (by decide)
