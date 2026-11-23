/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hall π-subgroups and subdirect products (Kourovka Notebook Problem 5.65)

Kourovka Notebook, Archive of Solved Problems, Problem 5.65 (L. A. Shemetkov): is the class of all
finite groups that have Hall π-subgroups closed under taking finite subdirect products?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GroupTheory.DPiHallIntersectionKourovka18Problem31Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.HallSubgroupSubdirectProductKourovka5Problem65Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.65 (L. A.
Shemetkov). UnsolvedMath record UM-00700344 (`KOU-5.65`), dataset ulamai/UnsolvedMath v1.8.0.

Hall `π`-subgroups are `IsHallPiSubgroup` of the Kourovka 18.31 module (order a `π`-number, index
with no prime divisor in `π`). A subdirect product of `G₁` and `G₂` is a group `G` with normal
subgroups `N₁`, `N₂` such that `N₁ ∩ N₂ = 1` and `G ⧸ Nᵢ ≅ Gᵢ`; closure under finite subdirect
products follows from the two-factor case by induction, so the target states that case.
-/

open MathlibExt.GroupTheory.DPiHallIntersectionKourovka18Problem31Wanted (IsHallPiSubgroup)

/-- Kourovka 5.65 (L. A. Shemetkov): the class of finite groups having a Hall `π`-subgroup is closed
under finite subdirect products; equivalently (by induction on the number of factors), if `N₁`,
`N₂` are normal subgroups of a finite group `G` with `N₁ ∩ N₂ = 1` and both `G ⧸ N₁` and `G ⧸ N₂`
have Hall `π`-subgroups, then so does `G`. -/
def hallSubgroupsSubdirectClosed : Prop :=
  ∀ (π : Set ℕ) (G : Type) [Group G] [Finite G] (N₁ N₂ : Subgroup G) [N₁.Normal] [N₂.Normal],
    N₁ ⊓ N₂ = ⊥ → (∃ H : Subgroup (G ⧸ N₁), IsHallPiSubgroup π H) →
    (∃ H : Subgroup (G ⧸ N₂), IsHallPiSubgroup π H) → ∃ H : Subgroup G, IsHallPiSubgroup π H

/--
Resolved true: Revin and Vdovin (2011), Corollary 7, prove that a finite subdirect product of finite
groups having Hall `π`-subgroups has a Hall `π`-subgroup, and the Kourovka Archive answers 5.65
"Yes, it is". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.65
(L. A. Shemetkov); resolution: D. O. Revin and E. P. Vdovin, An existence criterion for Hall
subgroups of finite groups, J. Group Theory 14 (2011), 93-101, arXiv:0803.3868, Corollary 7: a
finite subdirect product of E_π-groups satisfies E_π, which the paper notes answers Kourovka Problem
5.65; Kourovka Archive, Problem 5.65: Yes, it is, https://arxiv.org/abs/0803.3868.
-/
public theorem_wanted hallSubgroupsSubdirectClosed_holds : hallSubgroupsSubdirectClosed

end MathlibExt.GroupTheory.HallSubgroupSubdirectProductKourovka5Problem65Wanted
