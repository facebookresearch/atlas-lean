/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual code-twentyone prefix coordinates, including every zero outside its support. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyOneSpinPrefix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The twentyone actual prefix entries as a complete real spin packet. -/
noncomputable def monsterNortonCodeTwentyOneSpinPrefixPacket : SpinSpace :=
  ∑ i : Fin 16, (monsterNortonCodeTwentyOneSpinPrefixCoefficient i : ℝ) •
    Pi.single (golayLabelCoefficients (monsterNortonCodeTwentyOneSpinPrefixLabel i)) 1

private theorem label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeTwentyOneSpinPrefixLabel i)) :=
  golayLabelCoefficients_bijective.injective.comp
    monsterNortonCodeTwentyOneSpinPrefixLabel_injective

private theorem coefficient_sq (i : Fin 16) :
    (monsterNortonCodeTwentyOneSpinPrefixCoefficient i : ℝ) ^ 2 = 4 := by
  exact_mod_cast monsterNortonCodeTwentyOneSpinPrefixCoefficient_sq i

/-- The full sparse prefix packet has its exact squared norm sixty-four. -/
theorem monsterNortonCodeTwentyOneSpinPrefixPacket_norm :
    spinPairing monsterNortonCodeTwentyOneSpinPrefixPacket
      monsterNortonCodeTwentyOneSpinPrefixPacket =
      64 := by
  unfold monsterNortonCodeTwentyOneSpinPrefixPacket
  rw [monsterNortonSpin_sparse_norm _ _ label_injective]
  simp_rw [coefficient_sq]
  norm_num

/-- The full original-coordinate prefix table also has exact squared norm sixty-four. -/
theorem monsterNortonCodeTwentyOneSpinPrefixDense_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeTwentyOneSpinPrefixDense)
      (nortonUIntegerEmbed monsterNortonCodeTwentyOneSpinPrefixDense) = 64 := by
  rw [monsterNortonUIntegerEmbed_spin_norm,
    monsterNortonCodeTwentyOneSpinPrefixDense_norm_integer]
  norm_num

/-- The complete actual monomial prefix equals the sparse packet by maximal pairing. -/
theorem monsterNortonCodeTwentyOneSpinPrefix_sparse :
    nortonUIntegerEmbed monsterNortonCodeTwentyOneSpinPrefix =
      monsterNortonCodeTwentyOneSpinPrefixPacket := by
  have hp : spinPairing (nortonUIntegerEmbed monsterNortonCodeTwentyOneSpinPrefix)
      monsterNortonCodeTwentyOneSpinPrefixPacket = 64 := by
    unfold monsterNortonCodeTwentyOneSpinPrefixPacket
    rw [monsterNortonSpin_sparse_pairing]
    simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
      monsterNortonCodeTwentyOneSpinPrefix_coefficient, ← pow_two]
    simp_rw [coefficient_sq]
    norm_num
  apply monsterNortonSpin_eq_of_pairing
  · rw [monsterNortonCodeTwentyOneSpinPrefix_norm, monsterNortonCodeTwentyOneSpinPrefixPacket_norm]
  · rw [hp, monsterNortonCodeTwentyOneSpinPrefix_norm]

/-- The dense original-coordinate table equals that same complete sparse packet. -/
theorem monsterNortonCodeTwentyOneSpinPrefixDense_sparse :
    nortonUIntegerEmbed monsterNortonCodeTwentyOneSpinPrefixDense =
      monsterNortonCodeTwentyOneSpinPrefixPacket := by
  have hp : spinPairing (nortonUIntegerEmbed monsterNortonCodeTwentyOneSpinPrefixDense)
      monsterNortonCodeTwentyOneSpinPrefixPacket = 64 := by
    unfold monsterNortonCodeTwentyOneSpinPrefixPacket
    rw [monsterNortonSpin_sparse_pairing]
    simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
      monsterNortonCodeTwentyOneSpinPrefixDense_support, ← pow_two]
    simp_rw [coefficient_sq]
    norm_num
  apply monsterNortonSpin_eq_of_pairing
  · rw [monsterNortonCodeTwentyOneSpinPrefixDense_norm,
    monsterNortonCodeTwentyOneSpinPrefixPacket_norm]
  · rw [hp, monsterNortonCodeTwentyOneSpinPrefixDense_norm]

/-- The complete actual integer prefix equals the full table at all original coordinates. -/
theorem monsterNortonCodeTwentyOneSpinPrefix_dense :
    monsterNortonCodeTwentyOneSpinPrefix = monsterNortonCodeTwentyOneSpinPrefixDense := by
  apply monsterNortonUIntegerEmbed_injective
  rw [monsterNortonCodeTwentyOneSpinPrefix_sparse, monsterNortonCodeTwentyOneSpinPrefixDense_sparse]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
