/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.VanDerWaerdenSumProductThree

open MetaMathlibExt

-- Two consecutive blocks vanish at the same length for every sequence modulo three.
example (a : ℕ → ZMod 3) : ∃ l, 1 < l ∧ ∃ s,
    sumAddMulProdFamily 1 l (fun i => a (s + i)) = 0 ∧
    sumAddMulProdFamily 1 l (fun i => a (s + l + i)) = 0 := by
  obtain ⟨l, hl, s, hs⟩ := isVanishingFamily_sumAddMulProd_one_three 2 (by decide) a
  exact ⟨l, hl, s, by simpa using hs 0 (by decide), by simpa using hs 1 (by decide)⟩

-- On the constant sequence of ones, a vanishing block has length two modulo three.
example : ∃ l : ℕ, 1 < l ∧ 3 ∣ l + 1 := by
  obtain ⟨l, hl, s, hs⟩ := isVanishingFamily_sumAddMulProd_one_three 1 (by decide) (fun _ => 1)
  refine ⟨l, hl, (ZMod.natCast_eq_zero_iff (l + 1) 3).mp ?_⟩
  simpa [sumAddMulProdFamily] using hs 0 (by decide)
