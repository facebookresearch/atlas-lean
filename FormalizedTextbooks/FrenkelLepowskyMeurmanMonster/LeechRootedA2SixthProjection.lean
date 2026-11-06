/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2SixthStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQExact

/-! Exact kernel and actual range factor for the full sixth-axis Conway projection. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The entire actual Q stabilizer embeds in the full local-axis stabilizer. -/
def generatedSixthAxisPhaseInclusion :
    generatedSixthAxisQStabilizer →* generatedSixthLocalAxisStabilizer :=
  (inclQ.comp generatedSixthAxisQStabilizer.subtype).codRestrict _ (by
    intro q
    exact q.property)

/-- This genuine phase inclusion is injective. -/
theorem generatedSixthAxisPhaseInclusion_injective :
    Function.Injective generatedSixthAxisPhaseInclusion := by
  intro q r h
  apply Subtype.ext
  exact inclQ_injective (congrArg Subtype.val h)

/-- The restricted projection kernel is exactly the image of the full-axis Q stabilizer. -/
theorem generatedSixthAxisPhaseInclusion_range :
    generatedSixthAxisPhaseInclusion.range = generatedSixthLocalAxisProjection.ker := by
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
    have hphase : q ∈ generatedSixthAxisQStabilizer := by
      change inclQ q ∈ generatedSixthLocalAxisStabilizer
      rw [hq]
      exact h.property
    exact ⟨⟨q, hphase⟩, Subtype.ext hq⟩

/-- The actual restricted Conway projection kernel has exactly4 elements. -/
theorem generatedSixthLocalAxisProjection_kernel_card :
    Nat.card generatedSixthLocalAxisProjection.ker = 4 := by
  rw [← generatedSixthAxisPhaseInclusion_range]
  have h := Nat.card_congr
    (MonoidHom.ofInjective generatedSixthAxisPhaseInclusion_injective).toEquiv
  rw [← h]
  exact generatedSixthAxisQStabilizer_card

/-- The full H stabilizer has4 elements for each actual Conway projection value. -/
theorem generatedSixth_local_stabilizer_card_range :
    Nat.card generatedSixthLocalAxisStabilizer =
      4 * Nat.card generatedSixthProjectedAxisStabilizer := by
  have h := generatedSixthLocalAxisProjection.ker.card_mul_index
  rw [Subgroup.index_ker, generatedSixthLocalAxisProjection_kernel_card] at h
  exact h.symm


/-- The actual projected full-axis stabilizer has at most the full spatial flag order. -/
theorem generatedSixthProjectedAxisStabilizer_card_le :
    Nat.card generatedSixthProjectedAxisStabilizer ≤ 18393661440 := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  have h := Subgroup.card_le_of_le generatedSixthProjectedAxisStabilizer_le_spatial
  rwa [generatedSixthCo1SpatialStabilizer_card] at h

/-- The full actual sixth-axis local stabilizer is bounded by four times its spatial flag group. -/
theorem generatedSixthLocalAxisStabilizer_card_le :
    Nat.card generatedSixthLocalAxisStabilizer ≤ 73574645760 := by
  rw [generatedSixth_local_stabilizer_card_range]
  have h := generatedSixthProjectedAxisStabilizer_card_le
  omega

/-- Projection surjectivity gives the full actual sixth stabilizer count. -/
theorem generatedSixthLocalAxisStabilizer_card_of_projection
    (h : generatedSixthProjectedAxisStabilizer = generatedSixthCo1SpatialStabilizer) :
    Nat.card generatedSixthLocalAxisStabilizer = 73574645760 := by
  rw [generatedSixth_local_stabilizer_card_range, h, generatedSixthCo1SpatialStabilizer_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
