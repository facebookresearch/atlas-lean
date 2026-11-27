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

-- A nonidentity element survives some finite p-quotient for every prime, yet maps to
-- the identity in every torsion-free nilpotent quotient of the same group.
example : ∃ (G : Type) (_ : Group G), Group.FG G ∧
    (∀ p : ℕ, p.Prime → ∀ x : G, x ≠ 1 → ∃ (N : Subgroup G) (_ : N.Normal),
      x ∉ N ∧ Finite (G ⧸ N) ∧ IsPGroup p (G ⧸ N)) ∧
    ∃ g : G, g ≠ 1 ∧ ∀ (N : Subgroup G) [N.Normal], Group.IsNilpotent (G ⧸ N) →
      (∀ y : G ⧸ N, y ≠ 1 → ¬ IsOfFinOrder y) → QuotientGroup.mk' N g = 1 := by
  by_contra h
  apply residuallyFinitePImpliesResiduallyTorsionFreeNilpotent_refuted
  intro G _ hfg hp g hg
  by_contra hsep
  apply h
  refine ⟨G, ‹Group G›, hfg, hp, g, hg, ?_⟩
  intro N _ hnil htf
  apply (QuotientGroup.eq_one_iff g).2
  by_contra hgN
  exact hsep ⟨N, ‹N.Normal›, hgN, hnil, htf⟩
