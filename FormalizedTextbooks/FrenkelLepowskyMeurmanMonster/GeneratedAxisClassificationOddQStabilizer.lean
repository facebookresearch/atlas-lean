/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddPairPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddShortCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddTensorFixed

/-! The full actual odd-axis Q stabilizer, derived from its original matrix,
short, and tensor coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual extraspecial intersection of the odd-axis local stabilizer. -/
noncomputable def generatedOddAxisQStabilizer : Subgroup Q :=
  (MulAction.stabilizer H generatedOddAxis).comap inclQ

/-- Fixing the actual odd axis forces fixation of its nonzero spin state. -/
theorem generatedOddAxisQStabilizer_le_spin :
    generatedOddAxisQStabilizer ≤ generatedOddSpinStateStabilizer := by
  intro q hq
  change rhoLocal (inclQ q) generatedOddAxis = generatedOddAxis at hq
  have h := congrArg (fun x : GriessSpace => (griessConwayEncode x).2.2) hq
  change (griessConwayEncode
    (localGriessRepresentation (localFiberIncl q) generatedOddAxis)).2.2 = _ at h
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply] at h
  exact (generatedOddAxis_Q_tensor_fixed_iff q).mp h

/-- Fixing the distinguished spin state fixes every original coordinate of the odd axis. -/
theorem generatedOddSpinStateStabilizer_le_axis :
    generatedOddSpinStateStabilizer ≤ generatedOddAxisQStabilizer := by
  intro q hq
  change rhoLocal (inclQ q) generatedOddAxis = generatedOddAxis
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  change griessConwayEncode (localGriessRepresentation (localFiberIncl q) generatedOddAxis) = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  apply Prod.ext
  · change conwayMatrixAction 1 _ = _
    rw [map_one]
    rfl
  · apply Prod.ext
    · ext r
      have hd := localShortOperator_image (localFiberIncl q)
        (griessConwayEncode generatedOddAxis).2.1 r
      change localShortOperator (localFiberIncl q) _ (griessShortPermutation 1 r) = _ at hd
      rw [map_one, Equiv.Perm.one_apply] at hd
      change localShortOperator (localFiberIncl q) _ r = _
      rw [hd]
      rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
      · have hp := generatedOddSpinStateStabilizer_pair_phase q hq s p
        have hz : localShortPhase (localFiberIncl q) (Sum.inl (s, p)) = 0 := by
          rw [localAxisQPhase_eq_short_phase, hp]
          rfl
        rw [hz, qSign_zero, one_mul]
      · rw [generatedOddAxis, generatedAxis_triality_odd_octad_coordinate, mul_zero]
      · rw [generatedOddAxis, generatedAxis_triality_odd_odd_coordinate, mul_zero]
    · exact (generatedOddAxis_Q_tensor_fixed_iff q).mpr hq

/-- The genuine full-axis Q stabilizer equals the genuine spin-state stabilizer. -/
theorem generatedOddAxisQStabilizer_eq_spin :
    generatedOddAxisQStabilizer = generatedOddSpinStateStabilizer :=
  le_antisymm generatedOddAxisQStabilizer_le_spin generatedOddSpinStateStabilizer_le_axis

/-- Exactly 2^12 actual extraspecial elements fix the actual odd-axis representative. -/
theorem generatedOddAxisQStabilizer_card : Nat.card generatedOddAxisQStabilizer = 2 ^ 12 := by
  rw [generatedOddAxisQStabilizer_eq_spin, generatedOddSpinStateStabilizer_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
