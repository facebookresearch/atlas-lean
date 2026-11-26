/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.AbelianNormalGeneratorsPGroupKourovka20Problem75

open MathlibExt.GroupTheory.AbelianNormalGeneratorsPGroupKourovka20Problem75Wanted

-- The subgroup violating the doubled bound must be nonnormal.
example : ∃ (p : ℕ) (G : Type) (_ : Group G) (_ : Finite G), p.Prime ∧ IsPGroup p G ∧
    ∃ B : Subgroup G, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧ ¬ B.Normal := by
  classical
  by_contra h
  apply abelianSubgroupGeneratorsLeTwiceNormal_refuted
  intro p k G _ _ hp hG hnormal B hB
  have hn : B.Normal := by
    by_contra hn
    exact h ⟨p, G, inferInstance, inferInstance, hp, hG, B, hB, hn⟩
  obtain ⟨s, hs, hgen⟩ := hnormal B hn hB
  exact ⟨s, by omega, hgen⟩
