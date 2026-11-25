/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.TwistedUnitClassSubgroupKourovka18Problem14Nilpotent

open MathlibExt.GroupTheory.TwistedUnitClassSubgroupKourovka18Problem14Wanted

-- Check the refutation with both the conjecture and the subgroup condition unfolded.
example : ¬ ∀ (G : Type) [Group G],
    (∀ φ : G ≃* G, ∃ H : Subgroup G, (H : Set G) = Set.range (fun g : G ↦ g⁻¹ * φ g)) →
    Group.IsNilpotent G :=
  twistedUnitClassesSubgroupsImpliesNilpotent_refuted
