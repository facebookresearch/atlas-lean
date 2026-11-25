/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.BraidTorsionFreeQuotient

open MathlibExt.GroupTheory.BraidGroupShared (BraidGroup)
open MathlibExt.GroupTheory.BraidGroupEndomorphismsKourovka14Problem102Wanted

-- Five is the least strand count in the statement.
example :
    ∃ (N : Subgroup (BraidGroup 5)) (_ : N.Normal), N ≠ ⊥ ∧
      (∃ x y : BraidGroup 5 ⧸ N, x * y ≠ y * x) ∧
      ∀ (x : BraidGroup 5 ⧸ N) (k : ℕ), 0 < k → x ^ k = 1 → x = 1 := by
  obtain ⟨N, hN, hne, hnoncomm, htorsion⟩ :=
    braidTorsionFreeNonabelianProperQuotient_holds 5 (by decide)
  refine ⟨N, hN, hne, hnoncomm, ?_⟩
  intro x k hk hx
  by_contra h
  exact htorsion x h (isOfFinOrder_iff_pow_eq_one.mpr ⟨k, hk, hx⟩)
