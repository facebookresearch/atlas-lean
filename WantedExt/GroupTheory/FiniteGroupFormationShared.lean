/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shared notions for formations of finite groups

Inclusion of classes, local (saturated) formations and residuals, on top of `FiniteGroupClass` and
`IsFormation` from the WantedExt entry for Kourovka Notebook Problem 13.51. Shared by the WantedExt
entries for Kourovka Notebook Problems 9.58, 9.59, 9.60 and 9.73 so that they speak about the same
notions. The residual and saturation predicates of the 12.97 and 11.91 entries are stated for other
carriers (the `GroupClass` structure of 12.97, and isomorphism-closed classes of finite soluble
groups in 11.91), so they do not apply to `FiniteGroupClass`.
-/

module

public import WantedExt.GroupTheory.FiniteModularLatticeFormationsKourovka13Problem51Wanted
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.QuotientGroup.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.FiniteGroupFormationShared

open MathlibExt.GroupTheory.FiniteModularLatticeFormationsKourovka13Problem51Wanted

/-- Inclusion of classes of finite groups: every member of `𝔉` is a member of `𝔊`. -/
def ClassLE (𝔉 𝔊 : FiniteGroupClass) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], 𝔉 G → 𝔊 G

/-- `𝔉` is a local formation of finite groups, stated as a saturated formation containing the
trivial group: `𝔉` is a formation (`IsFormation`), contains the trivial group, and `G ∈ 𝔉` whenever
`G / Φ(G) ∈ 𝔉` (`Φ` the Frattini subgroup). By the Gaschütz-Lubeseder-Schmid theorem a nonempty
formation of finite groups is local (defined by a formation function) iff it is saturated. -/
def IsLocalFormation (𝔉 : FiniteGroupClass) : Prop :=
  IsFormation 𝔉 ∧ 𝔉 Unit ∧ ∀ (G : Type) [Group G] [Finite G], 𝔉 (G ⧸ frattini G) → 𝔉 G

/-- The `𝔉`-residual `G^𝔉` of a finite group `G`: the intersection of the normal subgroups `N` of
`G` with `G / N ∈ 𝔉`. For a formation containing the trivial group it is the smallest such `N`. -/
def residual (𝔉 : FiniteGroupClass) (G : Type) [Group G] [Finite G] : Subgroup G :=
  ⨅ (N : Subgroup G) (_ : N.Normal) (_ : 𝔉 (G ⧸ N)), N

end MathlibExt.GroupTheory.FiniteGroupFormationShared
