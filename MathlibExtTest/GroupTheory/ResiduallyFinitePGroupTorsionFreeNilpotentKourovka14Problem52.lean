/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.ResiduallyFinitePGroupTorsionFreeNilpotentKourovka14Problem52

open MathlibExt.GroupTheory.ResiduallyFinitePGroupTorsionFreeNilpotentKourovka14Problem52Wanted

-- Check that the refutation applies with the full, unfolded quotient conditions.
example : ¬ (∀ (G : Type) [Group G], Group.FG G →
    (∀ p : ℕ, p.Prime → ∀ g : G, g ≠ 1 → ∃ (N : Subgroup G) (_ : N.Normal), g ∉ N ∧
      Finite (G ⧸ N) ∧ IsPGroup p (G ⧸ N)) →
    ∀ g : G, g ≠ 1 → ∃ (N : Subgroup G) (_ : N.Normal), g ∉ N ∧ Group.IsNilpotent (G ⧸ N) ∧
      ∀ y : G ⧸ N, y ≠ 1 → ¬ IsOfFinOrder y) := by
  intro h
  exact residuallyFinitePImpliesResiduallyTorsionFreeNilpotent_refuted h
