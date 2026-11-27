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

-- Three is the least strand count of the general statement. The normal subgroup is neither
-- trivial nor everything, since its quotient has two elements that do not commute.
example : ∃ N : Subgroup (BraidGroup 3), N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  obtain ⟨N, hN, hne, ⟨x, y, hxy⟩, -⟩ := exists_torsionFree_nonabelian_proper_quotient 3 le_rfl
  refine ⟨N, hN, hne, fun htop => hxy ?_⟩
  have hone (z : BraidGroup 3 ⧸ N) : z = 1 := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    exact (QuotientGroup.eq_one_iff g).mpr (htop ▸ Subgroup.mem_top g)
  rw [hone x, hone y]
