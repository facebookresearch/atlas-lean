/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthSpatialProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthQExact

/-! The genuine full-axis Conway projection has its actual entire extraspecial kernel. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The entire original full-axis Q stabilizer includes in the actual local stabilizer. -/
def generatedTenthAxisPhaseInclusion :
    generatedTenthAxisQStabilizer →* generatedTenthLocalAxisStabilizer :=
  (inclQ.comp generatedTenthAxisQStabilizer.subtype).codRestrict _ (by
    intro q
    exact q.property)

/-- Faithfulness of the original extraspecial inclusion persists in the actual stabilizer. -/
theorem generatedTenthAxisPhaseInclusion_injective :
    Function.Injective generatedTenthAxisPhaseInclusion := by
  intro q r h
  apply Subtype.ext
  exact inclQ_injective (congrArg Subtype.val h)

/-- The restricted projection kernel is exactly the entire actual extraspecial fixer image. -/
theorem generatedTenthAxisPhaseInclusion_range :
    generatedTenthAxisPhaseInclusion.range = generatedTenthLocalAxisProjection.ker := by
  ext h
  constructor
  · rintro ⟨q, rfl⟩
    change projH (inclQ q.val) = 1
    have hq : inclQ q.val ∈ projH.ker := by
      rw [← inclQ_range_eq_projH_ker]
      exact ⟨q.val, rfl⟩
    exact hq
  · intro hk
    have hker : h.val ∈ projH.ker := hk
    rw [← inclQ_range_eq_projH_ker] at hker
    obtain ⟨q, hq⟩ := hker
    have hphase : q ∈ generatedTenthAxisQStabilizer := by
      change inclQ q ∈ generatedTenthLocalAxisStabilizer
      rw [hq]
      exact h.property
    exact ⟨⟨q, hphase⟩, Subtype.ext hq⟩

/-- The actual restricted Conway projection has precisely one kernel element. -/
theorem generatedTenthLocalAxisProjection_kernel_card :
    Nat.card generatedTenthLocalAxisProjection.ker = 1 := by
  rw [← generatedTenthAxisPhaseInclusion_range]
  have h := Nat.card_congr
    (MonoidHom.ofInjective generatedTenthAxisPhaseInclusion_injective).toEquiv
  rw [← h]
  exact generatedTenth_axis_Q_stabilizer_card

/-- The full original stabilizer has the same cardinal as its actual attained Conway image. -/
theorem generatedTenth_local_stabilizer_card_range :
    Nat.card generatedTenthLocalAxisStabilizer =
      Nat.card generatedTenthProjectedAxisStabilizer := by
  have h := generatedTenthLocalAxisProjection.ker.card_mul_index
  rw [Subgroup.index_ker, generatedTenthLocalAxisProjection_kernel_card, one_mul] at h
  exact h.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
