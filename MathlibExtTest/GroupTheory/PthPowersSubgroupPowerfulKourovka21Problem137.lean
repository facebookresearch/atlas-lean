/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.PthPowersSubgroupPowerfulKourovka21Problem137

open MathlibExt.GroupTheory.PthPowersSubgroupPowerfulKourovka21Problem137Wanted

-- The exact-exponent claim already fails at the smallest odd prime.
example :
    ¬ ∀ (G : Type) [Group G] [Finite G], IsPGroup 3 G →
      Monoid.exponent G = 3 ^ 2 → ∀ P : Subgroup G,
      (P : Set G) = {g | ∃ x : G, x ^ 3 = g} → ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  intro h
  exact pthPowersSubgroupAbelianExponentPSq_refuted ⟨3, by decide, by decide, h⟩
