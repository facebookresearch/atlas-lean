/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual code-nine prefix coordinates, including every zero outside its support. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineSpinPrefix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The sixty-four actual prefix entries as a complete real spin packet. -/
noncomputable def monsterNortonCodeNineSpinPrefixPacket : SpinSpace :=
  ∑ i : Fin 64, (monsterNortonCodeNineSpinPrefixCoefficient i : ℝ) •
    Pi.single (golayLabelCoefficients (monsterNortonCodeNineSpinPrefixLabel i)) 1

private theorem label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeNineSpinPrefixLabel i)) :=
  golayLabelCoefficients_bijective.injective.comp monsterNortonCodeNineSpinPrefixLabel_injective

private theorem coefficient_sq (i : Fin 64) :
    (monsterNortonCodeNineSpinPrefixCoefficient i : ℝ) ^ 2 = 1 := by
  exact_mod_cast monsterNortonCodeNineSpinPrefixCoefficient_sq i

/-- The full sparse prefix packet has its exact squared norm sixty-four. -/
theorem monsterNortonCodeNineSpinPrefixPacket_norm :
    spinPairing monsterNortonCodeNineSpinPrefixPacket monsterNortonCodeNineSpinPrefixPacket =
      64 := by
  unfold monsterNortonCodeNineSpinPrefixPacket
  rw [monsterNortonSpin_sparse_norm _ _ label_injective]
  simp_rw [coefficient_sq]
  norm_num

/-- The full original-coordinate prefix table also has exact squared norm sixty-four. -/
theorem monsterNortonCodeNineSpinPrefixDense_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeNineSpinPrefixDense)
      (nortonUIntegerEmbed monsterNortonCodeNineSpinPrefixDense) = 64 := by
  rw [monsterNortonUIntegerEmbed_spin_norm,
    monsterNortonCodeNineSpinPrefixDense_norm_integer]
  norm_num

/-- The complete actual monomial prefix equals the sparse packet by maximal pairing. -/
theorem monsterNortonCodeNineSpinPrefix_sparse :
    nortonUIntegerEmbed monsterNortonCodeNineSpinPrefix =
      monsterNortonCodeNineSpinPrefixPacket := by
  have hp : spinPairing (nortonUIntegerEmbed monsterNortonCodeNineSpinPrefix)
      monsterNortonCodeNineSpinPrefixPacket = 64 := by
    unfold monsterNortonCodeNineSpinPrefixPacket
    rw [monsterNortonSpin_sparse_pairing]
    simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
      monsterNortonCodeNineSpinPrefix_coefficient, ← pow_two]
    simp_rw [coefficient_sq]
    norm_num
  apply monsterNortonSpin_eq_of_pairing
  · rw [monsterNortonCodeNineSpinPrefix_norm, monsterNortonCodeNineSpinPrefixPacket_norm]
  · rw [hp, monsterNortonCodeNineSpinPrefix_norm]

/-- The dense original-coordinate table equals that same complete sparse packet. -/
theorem monsterNortonCodeNineSpinPrefixDense_sparse :
    nortonUIntegerEmbed monsterNortonCodeNineSpinPrefixDense =
      monsterNortonCodeNineSpinPrefixPacket := by
  have hp : spinPairing (nortonUIntegerEmbed monsterNortonCodeNineSpinPrefixDense)
      monsterNortonCodeNineSpinPrefixPacket = 64 := by
    unfold monsterNortonCodeNineSpinPrefixPacket
    rw [monsterNortonSpin_sparse_pairing]
    simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
      monsterNortonCodeNineSpinPrefixDense_support, ← pow_two]
    simp_rw [coefficient_sq]
    norm_num
  apply monsterNortonSpin_eq_of_pairing
  · rw [monsterNortonCodeNineSpinPrefixDense_norm, monsterNortonCodeNineSpinPrefixPacket_norm]
  · rw [hp, monsterNortonCodeNineSpinPrefixDense_norm]

/-- The complete actual integer prefix equals the full table at all original coordinates. -/
theorem monsterNortonCodeNineSpinPrefix_dense :
    monsterNortonCodeNineSpinPrefix = monsterNortonCodeNineSpinPrefixDense := by
  apply monsterNortonUIntegerEmbed_injective
  rw [monsterNortonCodeNineSpinPrefix_sparse, monsterNortonCodeNineSpinPrefixDense_sparse]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
