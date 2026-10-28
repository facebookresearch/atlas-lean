/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisNormEightLineBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddQStabilizer

/-! The actual odd-axis stabilizer projects into the genuine Co1 norm-eight line stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine stabilizer inside actual H of the original odd-image representative. -/
def generatedOddLocalAxisStabilizer : Subgroup H :=
  MulAction.stabilizer H generatedOddAxis

/-- Every axis-fixing local lift preserves the genuine physical norm-eight line. -/
theorem generatedOdd_axis_stabilizer_spatial (f : localFiberSubgroup)
    (hf : rhoLocal (localFiberIntoH f) generatedOddAxis = generatedOddAxis) :
    f.val.2 ∈ generatedNormEightLineStabilizer := by
  apply (generatedNormEightLine_odd_stabilizer_iff f.val.2 0 0).mp
  have h := congrArg (fun x : GriessSpace => (griessConwayEncode x).1) hf
  change (griessConwayEncode (localGriessRepresentation f _)).1 = _ at h
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply] at h
  exact h

/-- The genuine restricted H projection takes values in the actual Co1 line-stabilizer image. -/
def generatedOddLocalAxisProjection :
    generatedOddLocalAxisStabilizer →* generatedNormEightCo1LineStabilizer :=
  (projH.comp generatedOddLocalAxisStabilizer.subtype).codRestrict _ (by
    intro h
    obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
    change localFiberIntoH f = h.val at hf
    have hfix : rhoLocal (localFiberIntoH f) generatedOddAxis = generatedOddAxis := by
      rw [hf]
      exact h.property
    refine ⟨f.val.2, generatedOdd_axis_stabilizer_spatial f hfix, ?_⟩
    change QuotientGroup.mk' signsSubgroup f.val.2 = projH h.val
    rw [← hf]
    rfl)

/-- The genuine Q intersection embeds in the genuine H axis stabilizer. -/
def generatedOddAxisPhaseInclusion :
    generatedOddAxisQStabilizer →* generatedOddLocalAxisStabilizer :=
  (inclQ.comp generatedOddAxisQStabilizer.subtype).codRestrict _ (by
    intro q
    exact q.property)

theorem generatedOddAxisPhaseInclusion_injective :
    Function.Injective generatedOddAxisPhaseInclusion := by
  intro q r h
  apply Subtype.ext
  apply inclQ_injective
  exact congrArg Subtype.val h

/-- The restricted projection kernel is exactly the actual Q axis stabilizer. -/
theorem generatedOddAxisPhaseInclusion_range :
    generatedOddAxisPhaseInclusion.range = generatedOddLocalAxisProjection.ker := by
  ext h
  constructor
  · rintro ⟨q, rfl⟩
    apply Subtype.ext
    change projH (inclQ q.val) = 1
    have hq : inclQ q.val ∈ projH.ker := by
      rw [← inclQ_range_eq_projH_ker]
      exact ⟨q.val, rfl⟩
    exact hq
  · intro hk
    have hker : h.val ∈ projH.ker := congrArg Subtype.val hk
    rw [← inclQ_range_eq_projH_ker] at hker
    obtain ⟨q, hq⟩ := hker
    have hphase : q ∈ generatedOddAxisQStabilizer := by
      change inclQ q ∈ generatedOddLocalAxisStabilizer
      rw [hq]
      exact h.property
    exact ⟨⟨q, hphase⟩, Subtype.ext hq⟩

/-- Precisely 2^12 genuine H-stabilizer elements project to the identity in Co1. -/
theorem generatedOddLocalAxisProjection_kernel_card :
    Nat.card generatedOddLocalAxisProjection.ker = 2 ^ 12 := by
  rw [← generatedOddAxisPhaseInclusion_range]
  have h := Nat.card_congr
    (MonoidHom.ofInjective generatedOddAxisPhaseInclusion_injective).toEquiv
  rw [← h]
  exact generatedOddAxisQStabilizer_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
