/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual code-eighteen prefix coordinates, including every zero outside its support. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeEighteenSpinPrefix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The sixteen actual prefix entries as a complete real spin packet. -/
noncomputable def monsterNortonCodeEighteenSpinPrefixPacket : SpinSpace :=
  ∑ i : Fin 16, (monsterNortonCodeEighteenSpinPrefixCoefficient i : ℝ) •
    Pi.single (golayLabelCoefficients (monsterNortonCodeEighteenSpinPrefixLabel i)) 1

private theorem label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeEighteenSpinPrefixLabel i)) :=
  golayLabelCoefficients_bijective.injective.comp monsterNortonCodeEighteenSpinPrefixLabel_injective

private theorem coefficient_sq (i : Fin 16) :
    (monsterNortonCodeEighteenSpinPrefixCoefficient i : ℝ) ^ 2 = 4 := by
  exact_mod_cast monsterNortonCodeEighteenSpinPrefixCoefficient_sq i

/-- The full sparse prefix packet has its exact squared norm sixty-four. -/
theorem monsterNortonCodeEighteenSpinPrefixPacket_norm :
    spinPairing monsterNortonCodeEighteenSpinPrefixPacket
      monsterNortonCodeEighteenSpinPrefixPacket =
      64 := by
  unfold monsterNortonCodeEighteenSpinPrefixPacket
  rw [monsterNortonSpin_sparse_norm _ _ label_injective]
  simp_rw [coefficient_sq]
  norm_num

/-- The full original-coordinate prefix table also has exact squared norm sixty-four. -/
theorem monsterNortonCodeEighteenSpinPrefixDense_norm :
    spinPairing (nortonUIntegerEmbed monsterNortonCodeEighteenSpinPrefixDense)
      (nortonUIntegerEmbed monsterNortonCodeEighteenSpinPrefixDense) = 64 := by
  rw [monsterNortonUIntegerEmbed_spin_norm,
    monsterNortonCodeEighteenSpinPrefixDense_norm_integer]
  norm_num

/-- The complete actual monomial prefix equals the sparse packet by maximal pairing. -/
theorem monsterNortonCodeEighteenSpinPrefix_sparse :
    nortonUIntegerEmbed monsterNortonCodeEighteenSpinPrefix =
      monsterNortonCodeEighteenSpinPrefixPacket := by
  have hp : spinPairing (nortonUIntegerEmbed monsterNortonCodeEighteenSpinPrefix)
      monsterNortonCodeEighteenSpinPrefixPacket = 64 := by
    unfold monsterNortonCodeEighteenSpinPrefixPacket
    rw [monsterNortonSpin_sparse_pairing]
    simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
      monsterNortonCodeEighteenSpinPrefix_coefficient, ← pow_two]
    simp_rw [coefficient_sq]
    norm_num
  apply monsterNortonSpin_eq_of_pairing
  · rw [monsterNortonCodeEighteenSpinPrefix_norm, monsterNortonCodeEighteenSpinPrefixPacket_norm]
  · rw [hp, monsterNortonCodeEighteenSpinPrefix_norm]

/-- The dense original-coordinate table equals that same complete sparse packet. -/
theorem monsterNortonCodeEighteenSpinPrefixDense_sparse :
    nortonUIntegerEmbed monsterNortonCodeEighteenSpinPrefixDense =
      monsterNortonCodeEighteenSpinPrefixPacket := by
  have hp : spinPairing (nortonUIntegerEmbed monsterNortonCodeEighteenSpinPrefixDense)
      monsterNortonCodeEighteenSpinPrefixPacket = 64 := by
    unfold monsterNortonCodeEighteenSpinPrefixPacket
    rw [monsterNortonSpin_sparse_pairing]
    simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
      monsterNortonCodeEighteenSpinPrefixDense_support, ← pow_two]
    simp_rw [coefficient_sq]
    norm_num
  apply monsterNortonSpin_eq_of_pairing
  · rw [monsterNortonCodeEighteenSpinPrefixDense_norm,
    monsterNortonCodeEighteenSpinPrefixPacket_norm]
  · rw [hp, monsterNortonCodeEighteenSpinPrefixDense_norm]

/-- The complete actual integer prefix equals the full table at all original coordinates. -/
theorem monsterNortonCodeEighteenSpinPrefix_dense :
    monsterNortonCodeEighteenSpinPrefix = monsterNortonCodeEighteenSpinPrefixDense := by
  apply monsterNortonUIntegerEmbed_injective
  rw [monsterNortonCodeEighteenSpinPrefix_sparse, monsterNortonCodeEighteenSpinPrefixDense_sparse]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
