/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual preferred-basis-ten prefix coordinates, including every zero outside its support. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTenSpinPrefix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The sixty-four actual prefix entries as a complete real spin packet. -/
noncomputable def monsterNortonCodeTenSpinPrefixPacket : SpinSpace :=
  ∑ i : Fin 64, (monsterNortonCodeTenSpinPrefixCoefficient i : ℝ) •
    Pi.single (golayLabelCoefficients (monsterNortonCodeTenSpinPrefixLabel i)) 1

private theorem label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeTenSpinPrefixLabel i)) :=
  golayLabelCoefficients_bijective.injective.comp monsterNortonCodeTenSpinPrefixLabel_injective

private theorem coefficient_sq (i : Fin 64) :
    (monsterNortonCodeTenSpinPrefixCoefficient i : ℝ) ^ 2 = 1 := by
  exact_mod_cast monsterNortonCodeTenSpinPrefixCoefficient_sq i

/-- The full sparse prefix packet has its exact squared norm sixty-four. -/
theorem monsterNortonCodeTenSpinPrefixPacket_norm :
    spinPairing monsterNortonCodeTenSpinPrefixPacket monsterNortonCodeTenSpinPrefixPacket =
      64 := by
  unfold monsterNortonCodeTenSpinPrefixPacket
  rw [monsterNortonSpin_sparse_norm _ _ label_injective]
  simp_rw [coefficient_sq]
  norm_num

/-- The full original-coordinate prefix table also has exact squared norm sixty-four. -/
theorem monsterNortonCodeTenSpinPrefixDense_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeTenSpinPrefixDense)
      (nortonUIntegerEmbed monsterNortonCodeTenSpinPrefixDense) = 64 := by
  rw [monsterNortonUIntegerEmbed_spin_norm,
    monsterNortonCodeTenSpinPrefixDense_norm_integer]
  norm_num

/-- The complete actual monomial prefix equals the sparse packet by maximal pairing. -/
theorem monsterNortonCodeTenSpinPrefix_sparse :
    nortonUIntegerEmbed monsterNortonCodeTenSpinPrefix =
      monsterNortonCodeTenSpinPrefixPacket := by
  have hp : spinPairing (nortonUIntegerEmbed monsterNortonCodeTenSpinPrefix)
      monsterNortonCodeTenSpinPrefixPacket = 64 := by
    unfold monsterNortonCodeTenSpinPrefixPacket
    rw [monsterNortonSpin_sparse_pairing]
    simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
      monsterNortonCodeTenSpinPrefix_coefficient, ← pow_two]
    simp_rw [coefficient_sq]
    norm_num
  apply monsterNortonSpin_eq_of_pairing
  · rw [monsterNortonCodeTenSpinPrefix_norm, monsterNortonCodeTenSpinPrefixPacket_norm]
  · rw [hp, monsterNortonCodeTenSpinPrefix_norm]

/-- The dense original-coordinate table equals that same complete sparse packet. -/
theorem monsterNortonCodeTenSpinPrefixDense_sparse :
    nortonUIntegerEmbed monsterNortonCodeTenSpinPrefixDense =
      monsterNortonCodeTenSpinPrefixPacket := by
  have hp : spinPairing (nortonUIntegerEmbed monsterNortonCodeTenSpinPrefixDense)
      monsterNortonCodeTenSpinPrefixPacket = 64 := by
    unfold monsterNortonCodeTenSpinPrefixPacket
    rw [monsterNortonSpin_sparse_pairing]
    simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
      monsterNortonCodeTenSpinPrefixDense_support, ← pow_two]
    simp_rw [coefficient_sq]
    norm_num
  apply monsterNortonSpin_eq_of_pairing
  · rw [monsterNortonCodeTenSpinPrefixDense_norm, monsterNortonCodeTenSpinPrefixPacket_norm]
  · rw [hp, monsterNortonCodeTenSpinPrefixDense_norm]

/-- The complete actual integer prefix equals the full table at all original coordinates. -/
theorem monsterNortonCodeTenSpinPrefix_dense :
    monsterNortonCodeTenSpinPrefix = monsterNortonCodeTenSpinPrefixDense := by
  apply monsterNortonUIntegerEmbed_injective
  rw [monsterNortonCodeTenSpinPrefix_sparse, monsterNortonCodeTenSpinPrefixDense_sparse]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
