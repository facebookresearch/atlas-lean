/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthSpatialStabilizer

/-! Actual full-axis projection and its proved spatial containment. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual full local stabilizer of the eighth generated axis. -/
def generatedEighthLocalAxisStabilizer : Subgroup H := MulAction.stabilizer H generatedEighthAxis

/-- The genuine Conway projection restricted to the actual full-axis stabilizer. -/
def generatedEighthLocalAxisProjection : generatedEighthLocalAxisStabilizer →* Co1 :=
  projH.comp generatedEighthLocalAxisStabilizer.subtype

/-- The actual full-axis projection range, with no surjectivity premise. -/
def generatedEighthProjectedAxisStabilizer : Subgroup Co1 :=
  generatedEighthLocalAxisProjection.range

/-- Full actual axis fixation implies actual spatial matrix fixation. -/
theorem generatedEighth_local_fiber_spatial_mem (f : localFiberSubgroup)
    (hf : rhoLocal (localFiberIntoH f) generatedEighthAxis = generatedEighthAxis) :
    f.val.2 ∈ generatedEighthSpatialStabilizer := by
  have hm := congrArg (fun x : GriessSpace => (griessConwayEncode x).1) hf
  rw [generatedFourth_local_matrix] at hm
  exact hm

/-- The actual full-axis projection is contained in the counted actual spatial stabilizer. -/
theorem generatedEighthProjectedAxisStabilizer_le_spatial :
    generatedEighthProjectedAxisStabilizer ≤ generatedEighthCo1SpatialStabilizer := by
  rintro c ⟨h, rfl⟩
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  change localFiberIntoH f = h.val at hf
  have hfix : rhoLocal (localFiberIntoH f) generatedEighthAxis = generatedEighthAxis := by
    rw [hf]
    exact h.property
  refine ⟨f.val.2, generatedEighth_local_fiber_spatial_mem f hfix, ?_⟩
  change QuotientGroup.mk' signsSubgroup f.val.2 = projH h.val
  rw [← hf]
  rfl

/-- The whole actual full-axis projection has at most16220160 elements. -/
theorem generatedEighthProjectedAxisStabilizer_card_le :
    Nat.card generatedEighthProjectedAxisStabilizer ≤ 16220160 := by
  let : Finite generatedEighthCo1SpatialStabilizer := Nat.finite_of_card_ne_zero
    (by rw [generatedEighthCo1SpatialStabilizer_card]; decide)
  rw [← generatedEighthCo1SpatialStabilizer_card]
  exact Subgroup.card_le_of_le generatedEighthProjectedAxisStabilizer_le_spatial

/-- The genuine extraspecial phase stabilizer embeds into the full-axis stabilizer. -/
def generatedEighthAxisPhaseInclusion :
    generatedEighthAxisQStabilizer →* generatedEighthLocalAxisStabilizer :=
  (inclQ.comp generatedEighthAxisQStabilizer.subtype).codRestrict _ (by
    intro q
    exact q.property)

/-- This actual phase inclusion is injective. -/
theorem generatedEighthAxisPhaseInclusion_injective :
    Function.Injective generatedEighthAxisPhaseInclusion := by
  intro q r h
  apply Subtype.ext
  exact inclQ_injective (congrArg Subtype.val h)

/-- The entire full-axis projection kernel is exactly the image of the actual Q stabilizer. -/
theorem generatedEighthAxisPhaseInclusion_range :
    generatedEighthAxisPhaseInclusion.range = generatedEighthLocalAxisProjection.ker := by
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
    have hphase : q ∈ generatedEighthAxisQStabilizer := by
      change inclQ q ∈ generatedEighthLocalAxisStabilizer
      rw [hq]
      exact h.property
    exact ⟨⟨q, hphase⟩, Subtype.ext hq⟩

/-- The actual restricted kernel has exactly the actual extraspecial stabilizer cardinality. -/
theorem generatedEighthLocalAxisProjection_kernel_card :
    Nat.card generatedEighthLocalAxisProjection.ker =
      Nat.card generatedEighthAxisQStabilizer := by
  rw [← generatedEighthAxisPhaseInclusion_range]
  exact (Nat.card_congr
    (MonoidHom.ofInjective generatedEighthAxisPhaseInclusion_injective).toEquiv).symm

/-- The full-axis cardinality factors through its actual kernel and its actual image. -/
theorem generatedEighth_local_stabilizer_card_range :
    Nat.card generatedEighthLocalAxisStabilizer =
      Nat.card generatedEighthAxisQStabilizer *
        Nat.card generatedEighthProjectedAxisStabilizer := by
  have h := generatedEighthLocalAxisProjection.ker.card_mul_index
  rw [Subgroup.index_ker, generatedEighthLocalAxisProjection_kernel_card] at h
  exact h.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
