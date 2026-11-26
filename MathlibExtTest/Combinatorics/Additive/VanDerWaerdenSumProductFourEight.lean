/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.VanDerWaerdenSumProductFourEight

open MetaMathlibExt

-- On the constant sequence of ones modulo four, the block length is three modulo four.
example : ∃ l : ℕ, 1 < l ∧ 4 ∣ l + 1 := by
  have h := isVanishingFamily_sumAddMulProd_one_four_eight (hn := Or.inl rfl)
  obtain ⟨l, hl, s, hs⟩ := h 1 (by decide) (fun _ => 1)
  refine ⟨l, hl, (ZMod.natCast_eq_zero_iff (l + 1) 4).mp ?_⟩
  simpa [sumAddMulProdFamily] using hs 0 (by decide)

-- Modulo eight, the second vanishing block begins just after the first.
example (a : ℕ → ZMod 8) : ∃ l, 1 < l ∧ ∃ s,
    sumAddMulProdFamily 1 l (fun i => a (s + i)) = 0 ∧
    sumAddMulProdFamily 1 l (fun i => a (s + l + i)) = 0 := by
  have h := isVanishingFamily_sumAddMulProd_one_four_eight (hn := Or.inr rfl)
  obtain ⟨l, hl, s, hs⟩ := h 2 (by decide) a
  exact ⟨l, hl, s, by simpa using hs 0 (by decide), by simpa using hs 1 (by decide)⟩
