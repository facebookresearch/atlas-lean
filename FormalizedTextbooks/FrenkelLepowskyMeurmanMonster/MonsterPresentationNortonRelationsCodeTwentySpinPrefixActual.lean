/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual code-twenty prefix coordinates, including every zero outside its support. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentySpinPrefix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The twenty actual prefix entries as a complete real spin packet. -/
noncomputable def monsterNortonCodeTwentySpinPrefixPacket : SpinSpace :=
  ∑ i : Fin 16, (monsterNortonCodeTwentySpinPrefixCoefficient i : ℝ) •
    Pi.single (golayLabelCoefficients (monsterNortonCodeTwentySpinPrefixLabel i)) 1

private theorem label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeTwentySpinPrefixLabel i)) :=
  golayLabelCoefficients_bijective.injective.comp monsterNortonCodeTwentySpinPrefixLabel_injective

private theorem coefficient_sq (i : Fin 16) :
    (monsterNortonCodeTwentySpinPrefixCoefficient i : ℝ) ^ 2 = 4 := by
  exact_mod_cast monsterNortonCodeTwentySpinPrefixCoefficient_sq i

/-- The full sparse prefix packet has its exact squared norm sixty-four. -/
theorem monsterNortonCodeTwentySpinPrefixPacket_norm :
    spinPairing monsterNortonCodeTwentySpinPrefixPacket monsterNortonCodeTwentySpinPrefixPacket =
      64 := by
  unfold monsterNortonCodeTwentySpinPrefixPacket
  rw [monsterNortonSpin_sparse_norm _ _ label_injective]
  simp_rw [coefficient_sq]
  norm_num

/-- The full original-coordinate prefix table also has exact squared norm sixty-four. -/
theorem monsterNortonCodeTwentySpinPrefixDense_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeTwentySpinPrefixDense)
      (nortonUIntegerEmbed monsterNortonCodeTwentySpinPrefixDense) = 64 := by
  rw [monsterNortonUIntegerEmbed_spin_norm,
    monsterNortonCodeTwentySpinPrefixDense_norm_integer]
  norm_num

/-- The complete actual monomial prefix equals the sparse packet by maximal pairing. -/
theorem monsterNortonCodeTwentySpinPrefix_sparse :
    nortonUIntegerEmbed monsterNortonCodeTwentySpinPrefix =
      monsterNortonCodeTwentySpinPrefixPacket := by
  have hp : spinPairing (nortonUIntegerEmbed monsterNortonCodeTwentySpinPrefix)
      monsterNortonCodeTwentySpinPrefixPacket = 64 := by
    unfold monsterNortonCodeTwentySpinPrefixPacket
    rw [monsterNortonSpin_sparse_pairing]
    simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
      monsterNortonCodeTwentySpinPrefix_coefficient, ← pow_two]
    simp_rw [coefficient_sq]
    norm_num
  apply monsterNortonSpin_eq_of_pairing
  · rw [monsterNortonCodeTwentySpinPrefix_norm, monsterNortonCodeTwentySpinPrefixPacket_norm]
  · rw [hp, monsterNortonCodeTwentySpinPrefix_norm]

/-- The dense original-coordinate table equals that same complete sparse packet. -/
theorem monsterNortonCodeTwentySpinPrefixDense_sparse :
    nortonUIntegerEmbed monsterNortonCodeTwentySpinPrefixDense =
      monsterNortonCodeTwentySpinPrefixPacket := by
  have hp : spinPairing (nortonUIntegerEmbed monsterNortonCodeTwentySpinPrefixDense)
      monsterNortonCodeTwentySpinPrefixPacket = 64 := by
    unfold monsterNortonCodeTwentySpinPrefixPacket
    rw [monsterNortonSpin_sparse_pairing]
    simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
      monsterNortonCodeTwentySpinPrefixDense_support, ← pow_two]
    simp_rw [coefficient_sq]
    norm_num
  apply monsterNortonSpin_eq_of_pairing
  · rw [monsterNortonCodeTwentySpinPrefixDense_norm, monsterNortonCodeTwentySpinPrefixPacket_norm]
  · rw [hp, monsterNortonCodeTwentySpinPrefixDense_norm]

/-- The complete actual integer prefix equals the full table at all original coordinates. -/
theorem monsterNortonCodeTwentySpinPrefix_dense :
    monsterNortonCodeTwentySpinPrefix = monsterNortonCodeTwentySpinPrefixDense := by
  apply monsterNortonUIntegerEmbed_injective
  rw [monsterNortonCodeTwentySpinPrefix_sparse, monsterNortonCodeTwentySpinPrefixDense_sparse]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
