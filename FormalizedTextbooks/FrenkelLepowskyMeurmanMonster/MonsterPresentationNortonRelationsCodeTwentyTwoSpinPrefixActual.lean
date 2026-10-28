/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual code-twenty-two prefix coordinates, including every zero outside its support. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyTwoSpinPrefix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The sixty-four actual prefix entries as a complete real spin packet. -/
noncomputable def monsterNortonCodeTwentyTwoSpinPrefixPacket (k : Fin 16) : SpinSpace :=
  ∑ i : Fin 64, ((monsterNortonCodeTwentyTwoSpinPrefixCoefficient k) i : ℝ) •
    Pi.single (golayLabelCoefficients (monsterNortonCodeTwentyTwoSpinPrefixLabel i)) 1

private theorem label_injective : Function.Injective
    (fun i => golayLabelCoefficients (monsterNortonCodeTwentyTwoSpinPrefixLabel i)) :=
  golayLabelCoefficients_bijective.injective.comp
    monsterNortonCodeTwentyTwoSpinPrefixLabel_injective

private theorem coefficient_sq (k : Fin 16) (i : Fin 64) :
    ((monsterNortonCodeTwentyTwoSpinPrefixCoefficient k) i : ℝ) ^ 2 = 1 := by
  exact_mod_cast (monsterNortonCodeTwentyTwoSpinPrefixCoefficient_sq k) i

/-- The full sparse prefix packet has its exact squared norm sixty-four. -/
theorem monsterNortonCodeTwentyTwoSpinPrefixPacket_norm (k : Fin 16) :
    spinPairing (monsterNortonCodeTwentyTwoSpinPrefixPacket k)
      (monsterNortonCodeTwentyTwoSpinPrefixPacket k) =
      64 := by
  unfold monsterNortonCodeTwentyTwoSpinPrefixPacket
  rw [monsterNortonSpin_sparse_norm _ _ label_injective]
  simp_rw [(coefficient_sq k)]
  norm_num

/-- The full original-coordinate prefix table also has exact squared norm sixty-four. -/
theorem monsterNortonCodeTwentyTwoSpinPrefixDense_norm (k : Fin 16) :
    spinPairing (nortonUIntegerEmbed (monsterNortonCodeTwentyTwoSpinPrefixDense k))
      (nortonUIntegerEmbed (monsterNortonCodeTwentyTwoSpinPrefixDense k)) = 64 := by
  rw [monsterNortonUIntegerEmbed_spin_norm,
    (monsterNortonCodeTwentyTwoSpinPrefixDense_norm_integer k)]
  norm_num

/-- The complete actual monomial prefix equals the sparse packet by maximal pairing. -/
theorem monsterNortonCodeTwentyTwoSpinPrefix_sparse (k : Fin 16) :
    nortonUIntegerEmbed (monsterNortonCodeTwentyTwoSpinPrefix k) =
      (monsterNortonCodeTwentyTwoSpinPrefixPacket k) := by
  have hp : spinPairing (nortonUIntegerEmbed (monsterNortonCodeTwentyTwoSpinPrefix k))
      (monsterNortonCodeTwentyTwoSpinPrefixPacket k) = 64 := by
    unfold monsterNortonCodeTwentyTwoSpinPrefixPacket
    rw [monsterNortonSpin_sparse_pairing]
    simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
      (monsterNortonCodeTwentyTwoSpinPrefix_coefficient k), ← pow_two]
    simp_rw [(coefficient_sq k)]
    norm_num
  apply monsterNortonSpin_eq_of_pairing
  · rw [(monsterNortonCodeTwentyTwoSpinPrefix_norm k),
    (monsterNortonCodeTwentyTwoSpinPrefixPacket_norm k)]
  · rw [hp, (monsterNortonCodeTwentyTwoSpinPrefix_norm k)]

/-- The dense original-coordinate table equals that same complete sparse packet. -/
theorem monsterNortonCodeTwentyTwoSpinPrefixDense_sparse (k : Fin 16) :
    nortonUIntegerEmbed (monsterNortonCodeTwentyTwoSpinPrefixDense k) =
      (monsterNortonCodeTwentyTwoSpinPrefixPacket k) := by
  have hp : spinPairing (nortonUIntegerEmbed (monsterNortonCodeTwentyTwoSpinPrefixDense k))
      (monsterNortonCodeTwentyTwoSpinPrefixPacket k) = 64 := by
    unfold monsterNortonCodeTwentyTwoSpinPrefixPacket
    rw [monsterNortonSpin_sparse_pairing]
    simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
      (monsterNortonCodeTwentyTwoSpinPrefixDense_support k), ← pow_two]
    simp_rw [(coefficient_sq k)]
    norm_num
  apply monsterNortonSpin_eq_of_pairing
  · rw [(monsterNortonCodeTwentyTwoSpinPrefixDense_norm k),
    (monsterNortonCodeTwentyTwoSpinPrefixPacket_norm k)]
  · rw [hp, (monsterNortonCodeTwentyTwoSpinPrefixDense_norm k)]

/-- The complete actual integer prefix equals the full table at all original coordinates. -/
theorem monsterNortonCodeTwentyTwoSpinPrefix_dense (k : Fin 16) :
    (monsterNortonCodeTwentyTwoSpinPrefix k) = (monsterNortonCodeTwentyTwoSpinPrefixDense k) := by
  apply monsterNortonUIntegerEmbed_injective
  rw [(monsterNortonCodeTwentyTwoSpinPrefix_sparse k),
    (monsterNortonCodeTwentyTwoSpinPrefixDense_sparse k)]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
