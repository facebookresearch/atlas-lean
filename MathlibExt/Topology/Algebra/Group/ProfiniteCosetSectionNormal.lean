/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Separation.Regular
import MathlibExt.Topology.Algebra.Group.ProfiniteCosetSectionZorn
import Mathlib.Topology.Homeomorph.Quotient

/-!
# Continuous sections of closed normal profinite quotients

For a compact Hausdorff totally disconnected topological group `G` and closed normal subgroup
`N`, the quotient map `G → G/N` has a continuous set-theoretic right inverse.

This is the bottom-subgroup case of the nested closed-coset section theorem, using `G/{1} ≃ G`.
A homomorphic, canonical or natural splitting is not asserted.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Set Topology

namespace QuotientGroup

universe u

private noncomputable def quotientBotHomeomorph
    (G : Type u) [Group G] [TopologicalSpace G] :
    (G ⧸ (⊥ : Subgroup G)) ≃ₜ G where
  toEquiv := QuotientGroup.quotientBot.toEquiv
  continuous_toFun := continuous_quot_lift _ continuous_id
  continuous_invFun := QuotientGroup.continuous_mk

@[simp]
private theorem quotientBotHomeomorph_mk
    (G : Type u) [Group G] [TopologicalSpace G] (g : G) :
    quotientBotHomeomorph G (QuotientGroup.mk g) = g :=
  rfl

private theorem quotientMk_comp_quotientBotHomeomorph
    {G : Type u} [Group G] [TopologicalSpace G]
    (N : Subgroup G) [N.Normal] (q : G ⧸ (⊥ : Subgroup G)) :
    QuotientGroup.mk' N (quotientBotHomeomorph G q) =
      QuotientGroup.cosetProjection
        (bot_le : (⊥ : Subgroup G) ≤ N) q := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rfl

/-- **Continuous right inverse of a closed normal quotient map.** Let `G` be a compact
Hausdorff totally disconnected topological group. if `N≤G` is closed and normal, there
exists `s∈C(G/N,G)` with `q_N∘s=id_(G/N)`, where `q_N` is the quotient homomorphism. -/
theorem exists_continuous_section_of_profinite
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (N : Subgroup G) [N.Normal] [IsClosed (N : Set G)] :
    ∃ s : C(G ⧸ N, G),
      Function.RightInverse s (QuotientGroup.mk' N) := by
  obtain ⟨s₀, hs₀⟩ :=
    exists_continuous_section_of_closedSubgroup_le
      (⊥ : Subgroup G) N bot_le
  let e : C(G ⧸ (⊥ : Subgroup G), G) :=
    ⟨quotientBotHomeomorph G, (quotientBotHomeomorph G).continuous⟩
  let s : C(G ⧸ N, G) := e.comp s₀
  refine ⟨s, fun q => ?_⟩
  dsimp only [s, e, ContinuousMap.comp_apply]
  change QuotientGroup.mk' N (quotientBotHomeomorph G (s₀ q)) = q
  rw [quotientMk_comp_quotientBotHomeomorph]
  exact hs₀ q

end QuotientGroup

end
