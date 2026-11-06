/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual code-five prefix coordinates, including every zero outside its support. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeFiveSpinPrefix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The sixty-four actual prefix entries as a complete real spin packet. -/
noncomputable def monsterNortonCodeFiveSpinPrefixPacket : SpinSpace :=
  ∑ i : Fin 64, (monsterNortonCodeFiveSpinPrefixCoefficient i : ℝ) •
    Pi.single (golayLabelCoefficients (monsterNortonCodeFiveSpinPrefixLabel i)) 1

private theorem label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeFiveSpinPrefixLabel i)) :=
  golayLabelCoefficients_bijective.injective.comp monsterNortonCodeFiveSpinPrefixLabel_injective

private theorem coefficient_sq (i : Fin 64) :
    (monsterNortonCodeFiveSpinPrefixCoefficient i : ℝ) ^ 2 = 1 := by
  exact_mod_cast monsterNortonCodeFiveSpinPrefixCoefficient_sq i

/-- The full sparse prefix packet has its exact squared norm sixty-four. -/
theorem monsterNortonCodeFiveSpinPrefixPacket_norm :
    spinPairing monsterNortonCodeFiveSpinPrefixPacket monsterNortonCodeFiveSpinPrefixPacket =
      64 := by
  unfold monsterNortonCodeFiveSpinPrefixPacket
  rw [monsterNortonSpin_sparse_norm _ _ label_injective]
  simp_rw [coefficient_sq]
  norm_num

/-- The full original-coordinate prefix table also has exact squared norm sixty-four. -/
theorem monsterNortonCodeFiveSpinPrefixDense_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeFiveSpinPrefixDense)
      (nortonUIntegerEmbed monsterNortonCodeFiveSpinPrefixDense) = 64 := by
  rw [monsterNortonUIntegerEmbed_spin_norm,
    monsterNortonCodeFiveSpinPrefixDense_norm_integer]
  norm_num

/-- The complete actual monomial prefix equals the sparse packet by maximal pairing. -/
theorem monsterNortonCodeFiveSpinPrefix_sparse :
    nortonUIntegerEmbed monsterNortonCodeFiveSpinPrefix =
      monsterNortonCodeFiveSpinPrefixPacket := by
  have hp : spinPairing (nortonUIntegerEmbed monsterNortonCodeFiveSpinPrefix)
      monsterNortonCodeFiveSpinPrefixPacket = 64 := by
    unfold monsterNortonCodeFiveSpinPrefixPacket
    rw [monsterNortonSpin_sparse_pairing]
    simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
      monsterNortonCodeFiveSpinPrefix_coefficient, ← pow_two]
    simp_rw [coefficient_sq]
    norm_num
  apply monsterNortonSpin_eq_of_pairing
  · rw [monsterNortonCodeFiveSpinPrefix_norm, monsterNortonCodeFiveSpinPrefixPacket_norm]
  · rw [hp, monsterNortonCodeFiveSpinPrefix_norm]

/-- The dense original-coordinate table equals that same complete sparse packet. -/
theorem monsterNortonCodeFiveSpinPrefixDense_sparse :
    nortonUIntegerEmbed monsterNortonCodeFiveSpinPrefixDense =
      monsterNortonCodeFiveSpinPrefixPacket := by
  have hp : spinPairing (nortonUIntegerEmbed monsterNortonCodeFiveSpinPrefixDense)
      monsterNortonCodeFiveSpinPrefixPacket = 64 := by
    unfold monsterNortonCodeFiveSpinPrefixPacket
    rw [monsterNortonSpin_sparse_pairing]
    simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
      monsterNortonCodeFiveSpinPrefixDense_support, ← pow_two]
    simp_rw [coefficient_sq]
    norm_num
  apply monsterNortonSpin_eq_of_pairing
  · rw [monsterNortonCodeFiveSpinPrefixDense_norm, monsterNortonCodeFiveSpinPrefixPacket_norm]
  · rw [hp, monsterNortonCodeFiveSpinPrefixDense_norm]

/-- The complete actual integer prefix equals the full table at all original coordinates. -/
theorem monsterNortonCodeFiveSpinPrefix_dense :
    monsterNortonCodeFiveSpinPrefix = monsterNortonCodeFiveSpinPrefixDense := by
  apply monsterNortonUIntegerEmbed_injective
  rw [monsterNortonCodeFiveSpinPrefix_sparse, monsterNortonCodeFiveSpinPrefixDense_sparse]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
