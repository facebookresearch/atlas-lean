/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightSpatialProjection
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightQSupportUpper

/-! The genuine full-axis Conway projection has its actual entire extraspecial kernel. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The entire original full-axis Q stabilizer includes in the actual local stabilizer. -/
def generatedFifthRootEightAxisPhaseInclusion :
    generatedFifthRootEightAxisQStabilizer →* generatedFifthRootEightLocalAxisStabilizer :=
  (inclQ.comp generatedFifthRootEightAxisQStabilizer.subtype).codRestrict _ (by
    intro q
    exact q.property)

/-- Faithfulness of the original extraspecial inclusion persists in the actual stabilizer. -/
theorem generatedFifthRootEightAxisPhaseInclusion_injective :
    Function.Injective generatedFifthRootEightAxisPhaseInclusion := by
  intro q r h
  apply Subtype.ext
  exact inclQ_injective (congrArg Subtype.val h)

/-- The restricted projection kernel is exactly the entire actual extraspecial fixer image. -/
theorem generatedFifthRootEightAxisPhaseInclusion_range :
    generatedFifthRootEightAxisPhaseInclusion.range =
      generatedFifthRootEightLocalAxisProjection.ker := by
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
    have hphase : q ∈ generatedFifthRootEightAxisQStabilizer := by
      change inclQ q ∈ generatedFifthRootEightLocalAxisStabilizer
      rw [hq]
      exact h.property
    exact ⟨⟨q, hphase⟩, Subtype.ext hq⟩

/-- The restricted projection kernel has exactly the actual full-axis extraspecial order. -/
theorem generatedFifthRootEightLocalAxisProjection_kernel_card :
    Nat.card generatedFifthRootEightLocalAxisProjection.ker =
      Nat.card generatedFifthRootEightAxisQStabilizer := by
  rw [← generatedFifthRootEightAxisPhaseInclusion_range]
  have h := Nat.card_congr
    (MonoidHom.ofInjective generatedFifthRootEightAxisPhaseInclusion_injective).toEquiv
  exact h.symm

/-- The actual entire local stabilizer factors through its genuine Q kernel and attained image. -/
theorem generatedFifthRootEight_local_stabilizer_card_Q_mul_range :
    Nat.card generatedFifthRootEightLocalAxisStabilizer =
      Nat.card generatedFifthRootEightAxisQStabilizer *
        Nat.card generatedFifthRootEightProjectedAxisStabilizer := by
  have h := generatedFifthRootEightLocalAxisProjection.ker.card_mul_index
  rw [Subgroup.index_ker, generatedFifthRootEightLocalAxisProjection_kernel_card] at h
  exact h.symm

/-- The complete original spatial quotient has exactly88704000 genuine Conway values. -/
theorem generatedFifthRootEight_Co1_spatial_stabilizer_card :
    Nat.card generatedFifthRootEightCo1SpatialStabilizer = 88704000 := by
  have h := generatedFifthRootEight_spatial_card_twice_Co1
  rw [generatedFifthRootEight_matrix_stabilizer_card] at h
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
