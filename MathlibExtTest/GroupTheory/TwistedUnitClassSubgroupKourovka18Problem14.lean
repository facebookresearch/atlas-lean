/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.TwistedUnitClassSubgroupKourovka18Problem14

open MathlibExt.GroupTheory.TwistedUnitClassSubgroupKourovka18Problem14Wanted

-- The identity automorphism gives the trivial subgroup, even in a noncommutative group.
example (G : Type) [Group G] : twistedUnitClass (MulEquiv.refl G) = {1} := by
  ext g
  simp [twistedUnitClass]

-- Check that the public refutation elaborates with the subgroup condition fully unfolded.
example : ¬ ∀ (G : Type) [Group G], Group.FG G →
    (∀ φ : G ≃* G, ∃ H : Subgroup G, (H : Set G) = Set.range (fun g : G ↦ g⁻¹ * φ g)) →
    ∀ x y : G, x * y = y * x :=
  twistedUnitClassesSubgroupsFGImpliesAbelian_refuted
