/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual code-seventeen prefix coordinates, including every zero outside its support. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSeventeenSpinPrefix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The seventeen actual prefix entries as a complete real spin packet. -/
noncomputable def monsterNortonCodeSeventeenSpinPrefixPacket : SpinSpace :=
  ∑ i : Fin 16, (monsterNortonCodeSeventeenSpinPrefixCoefficient i : ℝ) •
    Pi.single (golayLabelCoefficients (monsterNortonCodeSeventeenSpinPrefixLabel i)) 1

private theorem label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeSeventeenSpinPrefixLabel i)) :=
  golayLabelCoefficients_bijective.injective.comp
    monsterNortonCodeSeventeenSpinPrefixLabel_injective

private theorem coefficient_sq (i : Fin 16) :
    (monsterNortonCodeSeventeenSpinPrefixCoefficient i : ℝ) ^ 2 = 4 := by
  exact_mod_cast monsterNortonCodeSeventeenSpinPrefixCoefficient_sq i

/-- The full sparse prefix packet has its exact squared norm sixty-four. -/
theorem monsterNortonCodeSeventeenSpinPrefixPacket_norm :
    spinPairing monsterNortonCodeSeventeenSpinPrefixPacket
      monsterNortonCodeSeventeenSpinPrefixPacket =
      64 := by
  unfold monsterNortonCodeSeventeenSpinPrefixPacket
  rw [monsterNortonSpin_sparse_norm _ _ label_injective]
  simp_rw [coefficient_sq]
  norm_num

/-- The full original-coordinate prefix table also has exact squared norm sixty-four. -/
theorem monsterNortonCodeSeventeenSpinPrefixDense_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeSeventeenSpinPrefixDense)
      (nortonUIntegerEmbed monsterNortonCodeSeventeenSpinPrefixDense) = 64 := by
  rw [monsterNortonUIntegerEmbed_spin_norm,
    monsterNortonCodeSeventeenSpinPrefixDense_norm_integer]
  norm_num

/-- The complete actual monomial prefix equals the sparse packet by maximal pairing. -/
theorem monsterNortonCodeSeventeenSpinPrefix_sparse :
    nortonUIntegerEmbed monsterNortonCodeSeventeenSpinPrefix =
      monsterNortonCodeSeventeenSpinPrefixPacket := by
  have hp : spinPairing (nortonUIntegerEmbed monsterNortonCodeSeventeenSpinPrefix)
      monsterNortonCodeSeventeenSpinPrefixPacket = 64 := by
    unfold monsterNortonCodeSeventeenSpinPrefixPacket
    rw [monsterNortonSpin_sparse_pairing]
    simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
      monsterNortonCodeSeventeenSpinPrefix_coefficient, ← pow_two]
    simp_rw [coefficient_sq]
    norm_num
  apply monsterNortonSpin_eq_of_pairing
  · rw [monsterNortonCodeSeventeenSpinPrefix_norm, monsterNortonCodeSeventeenSpinPrefixPacket_norm]
  · rw [hp, monsterNortonCodeSeventeenSpinPrefix_norm]

/-- The dense original-coordinate table equals that same complete sparse packet. -/
theorem monsterNortonCodeSeventeenSpinPrefixDense_sparse :
    nortonUIntegerEmbed monsterNortonCodeSeventeenSpinPrefixDense =
      monsterNortonCodeSeventeenSpinPrefixPacket := by
  have hp : spinPairing (nortonUIntegerEmbed monsterNortonCodeSeventeenSpinPrefixDense)
      monsterNortonCodeSeventeenSpinPrefixPacket = 64 := by
    unfold monsterNortonCodeSeventeenSpinPrefixPacket
    rw [monsterNortonSpin_sparse_pairing]
    simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
      monsterNortonCodeSeventeenSpinPrefixDense_support, ← pow_two]
    simp_rw [coefficient_sq]
    norm_num
  apply monsterNortonSpin_eq_of_pairing
  · rw [monsterNortonCodeSeventeenSpinPrefixDense_norm,
    monsterNortonCodeSeventeenSpinPrefixPacket_norm]
  · rw [hp, monsterNortonCodeSeventeenSpinPrefixDense_norm]

/-- The complete actual integer prefix equals the full table at all original coordinates. -/
theorem monsterNortonCodeSeventeenSpinPrefix_dense :
    monsterNortonCodeSeventeenSpinPrefix = monsterNortonCodeSeventeenSpinPrefixDense := by
  apply monsterNortonUIntegerEmbed_injective
  rw [monsterNortonCodeSeventeenSpinPrefix_sparse, monsterNortonCodeSeventeenSpinPrefixDense_sparse]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
