/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Keith Mills
-/
module

public import MathlibExt.AlgebraicTopology.EilenbergMacLane.Basic

@[expose] public section

namespace MathlibExtTest.AlgebraicTopology.EilenbergMacLane.Basic

open MetaMathlibExt

-- Topology 442: Eilenberg-MacLane Space

/-
If `X` is a `K(G, 1)` then the fundamental group of `X` is in bijection with `G`.

In fact these groups are isomorphic, but currently Mathlib does not have the assertion that
the first homotopy group is isomorphic to the fundamental group, so extending this lemma
in that way would make it no longer a 'sanity check.'
-/

theorem eilenberg_maclane_deg1_fundamental_group : ∀ (X G : Type*) [TopologicalSpace X] [Group G],
  IsEilenbergMaclaneSpace X G 1 → ∀ (x : X), Nonempty (FundamentalGroup X x ≃ G) := by
  intro X G _ _ h x
  have f : HomotopyGroup.Pi 1 X x ≃* G := (h.2 x).1.some
  have g : HomotopyGroup.Pi 1 X x ≃ FundamentalGroup X x := HomotopyGroup.pi1EquivFundamentalGroup
  exact ⟨Equiv.trans g.symm f⟩

end MathlibExtTest.AlgebraicTopology.EilenbergMacLane.Basic

end
