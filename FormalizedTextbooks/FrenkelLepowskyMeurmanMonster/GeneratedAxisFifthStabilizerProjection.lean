/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthQOrbit

/-! The actual full fifth-axis stabilizer has exactly32 elements per Conway projection value. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual full local stabilizer of the original fifth axis. -/
def generatedFifthLocalAxisStabilizer : Subgroup H :=
  MulAction.stabilizer H generatedFifthAxis

/-- The genuine Conway projection restricted to the actual full-axis stabilizer. -/
def generatedFifthLocalAxisProjection : generatedFifthLocalAxisStabilizer →* Co1 :=
  projH.comp generatedFifthLocalAxisStabilizer.subtype

/-- The actual image of the full-axis stabilizer in the Conway quotient. -/
def generatedFifthProjectedAxisStabilizer : Subgroup Co1 :=
  generatedFifthLocalAxisProjection.range

/-- The entire actual Q stabilizer embeds in the full local-axis stabilizer. -/
def generatedFifthAxisPhaseInclusion :
    generatedFifthAxisQStabilizer →* generatedFifthLocalAxisStabilizer :=
  (inclQ.comp generatedFifthAxisQStabilizer.subtype).codRestrict _ (by
    intro q
    exact q.property)

/-- This genuine phase inclusion is injective. -/
theorem generatedFifthAxisPhaseInclusion_injective :
    Function.Injective generatedFifthAxisPhaseInclusion := by
  intro q r h
  apply Subtype.ext
  exact inclQ_injective (congrArg Subtype.val h)

/-- The restricted projection kernel is exactly the image of the full-axis Q stabilizer. -/
theorem generatedFifthAxisPhaseInclusion_range :
    generatedFifthAxisPhaseInclusion.range = generatedFifthLocalAxisProjection.ker := by
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
    have hphase : q ∈ generatedFifthAxisQStabilizer := by
      change inclQ q ∈ generatedFifthLocalAxisStabilizer
      rw [hq]
      exact h.property
    exact ⟨⟨q, hphase⟩, Subtype.ext hq⟩

/-- The actual restricted Conway projection kernel has exactly32 elements. -/
theorem generatedFifthLocalAxisProjection_kernel_card :
    Nat.card generatedFifthLocalAxisProjection.ker = 32 := by
  rw [← generatedFifthAxisPhaseInclusion_range]
  have h := Nat.card_congr
    (MonoidHom.ofInjective generatedFifthAxisPhaseInclusion_injective).toEquiv
  rw [← h]
  exact generatedFifth_axis_Q_stabilizer_card

/-- The full H stabilizer has32 elements for each actual Conway projection value. -/
theorem generatedFifth_local_stabilizer_card_range :
    Nat.card generatedFifthLocalAxisStabilizer =
      32 * Nat.card generatedFifthProjectedAxisStabilizer := by
  have h := generatedFifthLocalAxisProjection.ker.card_mul_index
  rw [Subgroup.index_ker, generatedFifthLocalAxisProjection_kernel_card] at h
  exact h.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
