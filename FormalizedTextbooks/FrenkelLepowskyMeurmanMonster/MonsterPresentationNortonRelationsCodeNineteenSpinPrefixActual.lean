/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual code-nineteen prefix coordinates, including every zero outside its support. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineteenSpinPrefix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The nineteen actual prefix entries as a complete real spin packet. -/
noncomputable def monsterNortonCodeNineteenSpinPrefixPacket : SpinSpace :=
  ∑ i : Fin 16, (monsterNortonCodeNineteenSpinPrefixCoefficient i : ℝ) •
    Pi.single (golayLabelCoefficients (monsterNortonCodeNineteenSpinPrefixLabel i)) 1

private theorem label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeNineteenSpinPrefixLabel i)) :=
  golayLabelCoefficients_bijective.injective.comp monsterNortonCodeNineteenSpinPrefixLabel_injective

private theorem coefficient_sq (i : Fin 16) :
    (monsterNortonCodeNineteenSpinPrefixCoefficient i : ℝ) ^ 2 = 4 := by
  exact_mod_cast monsterNortonCodeNineteenSpinPrefixCoefficient_sq i

/-- The full sparse prefix packet has its exact squared norm sixty-four. -/
theorem monsterNortonCodeNineteenSpinPrefixPacket_norm :
    spinPairing monsterNortonCodeNineteenSpinPrefixPacket
      monsterNortonCodeNineteenSpinPrefixPacket =
      64 := by
  unfold monsterNortonCodeNineteenSpinPrefixPacket
  rw [monsterNortonSpin_sparse_norm _ _ label_injective]
  simp_rw [coefficient_sq]
  norm_num

/-- The full original-coordinate prefix table also has exact squared norm sixty-four. -/
theorem monsterNortonCodeNineteenSpinPrefixDense_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeNineteenSpinPrefixDense)
      (nortonUIntegerEmbed monsterNortonCodeNineteenSpinPrefixDense) = 64 := by
  rw [monsterNortonUIntegerEmbed_spin_norm,
    monsterNortonCodeNineteenSpinPrefixDense_norm_integer]
  norm_num

/-- The complete actual monomial prefix equals the sparse packet by maximal pairing. -/
theorem monsterNortonCodeNineteenSpinPrefix_sparse :
    nortonUIntegerEmbed monsterNortonCodeNineteenSpinPrefix =
      monsterNortonCodeNineteenSpinPrefixPacket := by
  have hp : spinPairing (nortonUIntegerEmbed monsterNortonCodeNineteenSpinPrefix)
      monsterNortonCodeNineteenSpinPrefixPacket = 64 := by
    unfold monsterNortonCodeNineteenSpinPrefixPacket
    rw [monsterNortonSpin_sparse_pairing]
    simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
      monsterNortonCodeNineteenSpinPrefix_coefficient, ← pow_two]
    simp_rw [coefficient_sq]
    norm_num
  apply monsterNortonSpin_eq_of_pairing
  · rw [monsterNortonCodeNineteenSpinPrefix_norm, monsterNortonCodeNineteenSpinPrefixPacket_norm]
  · rw [hp, monsterNortonCodeNineteenSpinPrefix_norm]

/-- The dense original-coordinate table equals that same complete sparse packet. -/
theorem monsterNortonCodeNineteenSpinPrefixDense_sparse :
    nortonUIntegerEmbed monsterNortonCodeNineteenSpinPrefixDense =
      monsterNortonCodeNineteenSpinPrefixPacket := by
  have hp : spinPairing (nortonUIntegerEmbed monsterNortonCodeNineteenSpinPrefixDense)
      monsterNortonCodeNineteenSpinPrefixPacket = 64 := by
    unfold monsterNortonCodeNineteenSpinPrefixPacket
    rw [monsterNortonSpin_sparse_pairing]
    simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
      monsterNortonCodeNineteenSpinPrefixDense_support, ← pow_two]
    simp_rw [coefficient_sq]
    norm_num
  apply monsterNortonSpin_eq_of_pairing
  · rw [monsterNortonCodeNineteenSpinPrefixDense_norm,
    monsterNortonCodeNineteenSpinPrefixPacket_norm]
  · rw [hp, monsterNortonCodeNineteenSpinPrefixDense_norm]

/-- The complete actual integer prefix equals the full table at all original coordinates. -/
theorem monsterNortonCodeNineteenSpinPrefix_dense :
    monsterNortonCodeNineteenSpinPrefix = monsterNortonCodeNineteenSpinPrefixDense := by
  apply monsterNortonUIntegerEmbed_injective
  rw [monsterNortonCodeNineteenSpinPrefix_sparse, monsterNortonCodeNineteenSpinPrefixDense_sparse]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
