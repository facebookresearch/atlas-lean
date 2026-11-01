/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual code-seven prefix coordinates, including every zero outside its support. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSevenSpinPrefix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The sixty-four actual prefix entries as a complete real spin packet. -/
noncomputable def monsterNortonCodeSevenSpinPrefixPacket : SpinSpace :=
  ∑ i : Fin 64, (monsterNortonCodeSevenSpinPrefixCoefficient i : ℝ) •
    Pi.single (golayLabelCoefficients (monsterNortonCodeSevenSpinPrefixLabel i)) 1

private theorem label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeSevenSpinPrefixLabel i)) :=
  golayLabelCoefficients_bijective.injective.comp monsterNortonCodeSevenSpinPrefixLabel_injective

private theorem coefficient_sq (i : Fin 64) :
    (monsterNortonCodeSevenSpinPrefixCoefficient i : ℝ) ^ 2 = 1 := by
  exact_mod_cast monsterNortonCodeSevenSpinPrefixCoefficient_sq i

/-- The full sparse prefix packet has its exact squared norm sixty-four. -/
theorem monsterNortonCodeSevenSpinPrefixPacket_norm :
    spinPairing monsterNortonCodeSevenSpinPrefixPacket monsterNortonCodeSevenSpinPrefixPacket =
      64 := by
  unfold monsterNortonCodeSevenSpinPrefixPacket
  rw [monsterNortonSpin_sparse_norm _ _ label_injective]
  simp_rw [coefficient_sq]
  norm_num

/-- The full original-coordinate prefix table also has exact squared norm sixty-four. -/
theorem monsterNortonCodeSevenSpinPrefixDense_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeSevenSpinPrefixDense)
      (nortonUIntegerEmbed monsterNortonCodeSevenSpinPrefixDense) = 64 := by
  rw [monsterNortonUIntegerEmbed_spin_norm,
    monsterNortonCodeSevenSpinPrefixDense_norm_integer]
  norm_num

/-- The complete actual monomial prefix equals the sparse packet by maximal pairing. -/
theorem monsterNortonCodeSevenSpinPrefix_sparse :
    nortonUIntegerEmbed monsterNortonCodeSevenSpinPrefix =
      monsterNortonCodeSevenSpinPrefixPacket := by
  have hp : spinPairing (nortonUIntegerEmbed monsterNortonCodeSevenSpinPrefix)
      monsterNortonCodeSevenSpinPrefixPacket = 64 := by
    unfold monsterNortonCodeSevenSpinPrefixPacket
    rw [monsterNortonSpin_sparse_pairing]
    simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
      monsterNortonCodeSevenSpinPrefix_coefficient, ← pow_two]
    simp_rw [coefficient_sq]
    norm_num
  apply monsterNortonSpin_eq_of_pairing
  · rw [monsterNortonCodeSevenSpinPrefix_norm, monsterNortonCodeSevenSpinPrefixPacket_norm]
  · rw [hp, monsterNortonCodeSevenSpinPrefix_norm]

/-- The dense original-coordinate table equals that same complete sparse packet. -/
theorem monsterNortonCodeSevenSpinPrefixDense_sparse :
    nortonUIntegerEmbed monsterNortonCodeSevenSpinPrefixDense =
      monsterNortonCodeSevenSpinPrefixPacket := by
  have hp : spinPairing (nortonUIntegerEmbed monsterNortonCodeSevenSpinPrefixDense)
      monsterNortonCodeSevenSpinPrefixPacket = 64 := by
    unfold monsterNortonCodeSevenSpinPrefixPacket
    rw [monsterNortonSpin_sparse_pairing]
    simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
      monsterNortonCodeSevenSpinPrefixDense_support, ← pow_two]
    simp_rw [coefficient_sq]
    norm_num
  apply monsterNortonSpin_eq_of_pairing
  · rw [monsterNortonCodeSevenSpinPrefixDense_norm, monsterNortonCodeSevenSpinPrefixPacket_norm]
  · rw [hp, monsterNortonCodeSevenSpinPrefixDense_norm]

/-- The complete actual integer prefix equals the full table at all original coordinates. -/
theorem monsterNortonCodeSevenSpinPrefix_dense :
    monsterNortonCodeSevenSpinPrefix = monsterNortonCodeSevenSpinPrefixDense := by
  apply monsterNortonUIntegerEmbed_injective
  rw [monsterNortonCodeSevenSpinPrefix_sparse, monsterNortonCodeSevenSpinPrefixDense_sparse]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
