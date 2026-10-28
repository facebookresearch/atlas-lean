/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceRootWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalCoverageBinary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisEnumerationLocalCoordinates

/-! The genuine frame root gives actual odd-axis and original signed-short destinations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The frame root word is the literal identity, without any phase substitution. -/
theorem generatedAxisGlobalOddOmega_word : generatedAxisGlobalOddSourceRootLocalWord 5 = 1 := rfl

/-- The original singleton cocode fixes the genuine preferred odd signed-short axis. -/
theorem generatedAxisGlobalOddOmega_short_fixed :
    rhoLocal (inclQ singletonCocodeQ)
      (conwayShortAxis (Sum.inr (Sum.inr (0, 0))) 0) =
      conwayShortAxis (Sum.inr (Sum.inr (0, 0))) 0 := by
  change localGriessRepresentation (localFiberIncl singletonCocodeQ) _ = _
  rw [generatedAxis_localFiber_image]
  have hp : localShortPhase (localFiberIncl singletonCocodeQ)
      (Sum.inr (Sum.inr (0, 0))) = 0 := by
    rw [singletonCocodeQ, cocodeQ_short_phase, griessOdd_translation]
    decide +kernel
  have hl : griessShortPermutation (localFiberIncl singletonCocodeQ).val.2
      (Sum.inr (Sum.inr (0, 0))) = Sum.inr (Sum.inr (0, 0)) := by
    change griessShortPermutation 1 _ = _
    rw [map_one]
    rfl
  rw [hp, zero_add, hl]

/-- The actual triality square is its genuine inverse. -/
theorem generatedAxisGlobalOddOmega_triality_square : sExtra * sExtra = sExtra⁻¹ := by
  have ht : sExtra * sExtra * sExtra = 1 := by
    simpa only [pow_succ, pow_zero, one_mul] using sExtra_pow_three
  calc
    sExtra * sExtra = (sExtra * sExtra * sExtra) * sExtra⁻¹ := by group
    _ = sExtra⁻¹ := by rw [ht, one_mul]

/-- The positive frame-root transition is a genuine full local image of the odd prototype. -/
theorem generatedAxisGlobalOddOmega_positive_orbit :
    ∃ h : H, sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 5) generatedOddAxis) =
      rhoLocal h generatedOddAxis := by
  refine ⟨inclQ singletonCocodeQ, ?_⟩
  rw [generatedAxisGlobalOddOmega_word, map_one, LinearEquiv.coe_one, id_eq]
  have hd : inclQ singletonCocodeQ * inclQ singletonCocodeQ = (1 : H) := by
    rw [← map_mul]
    change inclQ (cocodeQ _ * cocodeQ _) = 1
    rw [cocodeQ_square, map_one]
  let b := conwayShortAxis (Sum.inr (Sum.inr (0, 0))) 0
  have he : sExtra b = rhoLocal (inclQ singletonCocodeQ) (sExtra⁻¹ b) := by
    simpa only [b, generatedAxisGlobalOddOmega_short_fixed] using
      generatedAxisGlobal_singleton_triality_exchange b
  have hc : sExtra⁻¹ b = rhoLocal (inclQ singletonCocodeQ) (sExtra b) := by
    calc
      sExtra⁻¹ b = (rhoLocal (inclQ singletonCocodeQ) *
          rhoLocal (inclQ singletonCocodeQ)) (sExtra⁻¹ b) := by
        rw [← map_mul, hd, map_one]
        rfl
      _ = rhoLocal (inclQ singletonCocodeQ) (sExtra b) := by
        rw [LinearEquiv.mul_apply, ← he]
  change sExtra (sExtra b) = rhoLocal (inclQ singletonCocodeQ) (sExtra b)
  rw [← LinearEquiv.mul_apply, generatedAxisGlobalOddOmega_triality_square]
  exact hc

/-- The inverse frame-root transition is a genuine original signed-short axis. -/
theorem generatedAxisGlobalOddOmega_negative :
    sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 5) generatedOddAxis) =
      conwayShortAxis (Sum.inr (Sum.inr (0, 0))) 0 := by
  rw [generatedAxisGlobalOddOmega_word, map_one, LinearEquiv.coe_one, id_eq]
  change sExtra⁻¹ (sExtra _) = _
  exact sExtra.symm_apply_apply _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
