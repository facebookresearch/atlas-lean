/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhSpatialStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhQExact

/-! Exact kernel and actual range factor for the full seventh-axis Conway projection. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The entire actual Q stabilizer embeds in the full local-axis stabilizer. -/
def generatedSeventhAxisPhaseInclusion :
    generatedSeventhAxisQStabilizer →* generatedSeventhLocalAxisStabilizer :=
  (inclQ.comp generatedSeventhAxisQStabilizer.subtype).codRestrict _ (by
    intro q
    exact q.property)

/-- This genuine phase inclusion is injective. -/
theorem generatedSeventhAxisPhaseInclusion_injective :
    Function.Injective generatedSeventhAxisPhaseInclusion := by
  intro q r h
  apply Subtype.ext
  exact inclQ_injective (congrArg Subtype.val h)

/-- The restricted projection kernel is exactly the image of the full-axis Q stabilizer. -/
theorem generatedSeventhAxisPhaseInclusion_range :
    generatedSeventhAxisPhaseInclusion.range = generatedSeventhLocalAxisProjection.ker := by
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
    have hphase : q ∈ generatedSeventhAxisQStabilizer := by
      change inclQ q ∈ generatedSeventhLocalAxisStabilizer
      rw [hq]
      exact h.property
    exact ⟨⟨q, hphase⟩, Subtype.ext hq⟩

/-- The actual restricted Conway projection kernel has exactly four elements. -/
theorem generatedSeventhLocalAxisProjection_kernel_card :
    Nat.card generatedSeventhLocalAxisProjection.ker = 4 := by
  rw [← generatedSeventhAxisPhaseInclusion_range]
  have h := Nat.card_congr
    (MonoidHom.ofInjective generatedSeventhAxisPhaseInclusion_injective).toEquiv
  rw [← h]
  exact generatedSeventhAxisQStabilizer_card

/-- The full H stabilizer has four elements for each actual Conway projection value. -/
theorem generatedSeventh_local_stabilizer_card_range :
    Nat.card generatedSeventhLocalAxisStabilizer =
      4 * Nat.card generatedSeventhProjectedAxisStabilizer := by
  have h := generatedSeventhLocalAxisProjection.ker.card_mul_index
  rw [Subgroup.index_ker, generatedSeventhLocalAxisProjection_kernel_card] at h
  exact h.symm


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
