/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual code-sixteen prefix coordinates, including every zero outside its support. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSixteenSpinPrefix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The sixteen actual prefix entries as a complete real spin packet. -/
noncomputable def monsterNortonCodeSixteenSpinPrefixPacket : SpinSpace :=
  ∑ i : Fin 16, (monsterNortonCodeSixteenSpinPrefixCoefficient i : ℝ) •
    Pi.single (golayLabelCoefficients (monsterNortonCodeSixteenSpinPrefixLabel i)) 1

private theorem label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeSixteenSpinPrefixLabel i)) :=
  golayLabelCoefficients_bijective.injective.comp monsterNortonCodeSixteenSpinPrefixLabel_injective

private theorem coefficient_sq (i : Fin 16) :
    (monsterNortonCodeSixteenSpinPrefixCoefficient i : ℝ) ^ 2 = 4 := by
  exact_mod_cast monsterNortonCodeSixteenSpinPrefixCoefficient_sq i

/-- The full sparse prefix packet has its exact squared norm sixty-four. -/
theorem monsterNortonCodeSixteenSpinPrefixPacket_norm :
    spinPairing monsterNortonCodeSixteenSpinPrefixPacket monsterNortonCodeSixteenSpinPrefixPacket =
      64 := by
  unfold monsterNortonCodeSixteenSpinPrefixPacket
  rw [monsterNortonSpin_sparse_norm _ _ label_injective]
  simp_rw [coefficient_sq]
  norm_num

/-- The full original-coordinate prefix table also has exact squared norm sixty-four. -/
theorem monsterNortonCodeSixteenSpinPrefixDense_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeSixteenSpinPrefixDense)
      (nortonUIntegerEmbed monsterNortonCodeSixteenSpinPrefixDense) = 64 := by
  rw [monsterNortonUIntegerEmbed_spin_norm,
    monsterNortonCodeSixteenSpinPrefixDense_norm_integer]
  norm_num

/-- The complete actual monomial prefix equals the sparse packet by maximal pairing. -/
theorem monsterNortonCodeSixteenSpinPrefix_sparse :
    nortonUIntegerEmbed monsterNortonCodeSixteenSpinPrefix =
      monsterNortonCodeSixteenSpinPrefixPacket := by
  have hp : spinPairing (nortonUIntegerEmbed monsterNortonCodeSixteenSpinPrefix)
      monsterNortonCodeSixteenSpinPrefixPacket = 64 := by
    unfold monsterNortonCodeSixteenSpinPrefixPacket
    rw [monsterNortonSpin_sparse_pairing]
    simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
      monsterNortonCodeSixteenSpinPrefix_coefficient, ← pow_two]
    simp_rw [coefficient_sq]
    norm_num
  apply monsterNortonSpin_eq_of_pairing
  · rw [monsterNortonCodeSixteenSpinPrefix_norm, monsterNortonCodeSixteenSpinPrefixPacket_norm]
  · rw [hp, monsterNortonCodeSixteenSpinPrefix_norm]

/-- The dense original-coordinate table equals that same complete sparse packet. -/
theorem monsterNortonCodeSixteenSpinPrefixDense_sparse :
    nortonUIntegerEmbed monsterNortonCodeSixteenSpinPrefixDense =
      monsterNortonCodeSixteenSpinPrefixPacket := by
  have hp : spinPairing (nortonUIntegerEmbed monsterNortonCodeSixteenSpinPrefixDense)
      monsterNortonCodeSixteenSpinPrefixPacket = 64 := by
    unfold monsterNortonCodeSixteenSpinPrefixPacket
    rw [monsterNortonSpin_sparse_pairing]
    simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
      monsterNortonCodeSixteenSpinPrefixDense_support, ← pow_two]
    simp_rw [coefficient_sq]
    norm_num
  apply monsterNortonSpin_eq_of_pairing
  · rw [monsterNortonCodeSixteenSpinPrefixDense_norm, monsterNortonCodeSixteenSpinPrefixPacket_norm]
  · rw [hp, monsterNortonCodeSixteenSpinPrefixDense_norm]

/-- The complete actual integer prefix equals the full table at all original coordinates. -/
theorem monsterNortonCodeSixteenSpinPrefix_dense :
    monsterNortonCodeSixteenSpinPrefix = monsterNortonCodeSixteenSpinPrefixDense := by
  apply monsterNortonUIntegerEmbed_injective
  rw [monsterNortonCodeSixteenSpinPrefix_sparse, monsterNortonCodeSixteenSpinPrefixDense_sparse]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
