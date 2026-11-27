/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.TestRankNonabelianVarietyKourovka16Problem87

open MathlibExt.GroupTheory.TestRankNonabelianVarietyKourovka16Problem87Wanted

-- With zero generators the quotient is trivial, so the empty set already tests it.
example (W : Set (FreeGroup ℕ)) : HasTestRank (RelativelyFreeGroup W 0) 0 := by
  refine ⟨⟨∅, ?_, Set.encard_empty⟩, fun _ _ => bot_le⟩
  intro f _
  have hf : f = MonoidHom.id _ := by ext i; exact Fin.elim0 i
  rw [hf]
  exact Function.bijective_id

-- Even a nongenerator of the infinite cyclic group can form a singleton test set.
example : IsTestSet ({Multiplicative.ofAdd (2 : ℤ)} : Set (Multiplicative ℤ)) := by
  intro f hf
  let F : ℤ →+ ℤ := f.toAdditive
  have hmul (n : ℤ) : F n = n * F 1 := by
    simpa only [Int.zsmul_eq_mul, mul_one] using F.map_zsmul n (1 : ℤ)
  have htwo : F 2 = 2 := hf _ (Set.mem_singleton _)
  have hone : F 1 = 1 := by
    have := hmul 2
    omega
  have h : f = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    change F x.toAdd = x.toAdd
    rw [hmul, hone, mul_one]
  rw [h]
  exact Function.bijective_id
