/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual sparse spin images determined by orthogonality and supported coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMixedOddSpinData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOddInverseSpinNorm

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine sparse spin packet in the original source basis. -/
noncomputable def monsterNortonMixedOddSpinPacket (k : Fin 5) : SpinSpace :=
  ∑ i : Fin 128, (monsterNortonMixedOddSpinCoefficient k i : ℝ) •
    Pi.single (golayLabelCoefficients (monsterNortonMixedOddSpinLabel k i)) 1

private theorem sourceLabel_injective (k : Fin 5) :
    Function.Injective (fun i => golayLabelCoefficients (monsterNortonMixedOddSpinLabel k i)) :=
  golayLabelCoefficients_bijective.injective.comp (monsterNortonMixedOddSpinLabel_injective k)

private theorem coefficient_sq (k : Fin 5) (i : Fin 128) :
    (monsterNortonMixedOddSpinCoefficient k i : ℝ) ^ 2 = 1 := by
  exact_mod_cast monsterNortonMixedOddSpinCoefficient_sq k i

/-- The whole candidate packet has its exact spin squared norm 128. -/
theorem monsterNortonMixedOddSpinPacket_norm (k : Fin 5) :
    spinPairing (monsterNortonMixedOddSpinPacket k) (monsterNortonMixedOddSpinPacket k) = 128 := by
  rw [monsterNortonMixedOddSpinPacket, monsterNortonSpin_sparse_norm _ _
    (sourceLabel_injective k)]
  simp_rw [coefficient_sq]
  norm_num

/-- Orthogonality gives the full genuine numerator norm, independently of its proposed support. -/
theorem monsterNortonMixedOddSpinNumerator_norm (k : Fin 5) :
    spinPairing (nortonUIntegerEmbed (monsterNortonMixedOddSpinNumerator k))
      (nortonUIntegerEmbed (monsterNortonMixedOddSpinNumerator k)) = 128 :=
  monsterNortonOddInverseSpinNumerator_norm
    (monsterNortonEvenShortFirstUOddCode (monsterNortonMixedOddBasisIndex k))

/-- Every supported actual coefficient gives the exact maximal whole-vector spin pairing. -/
theorem monsterNortonMixedOddSpinPacket_pairing (k : Fin 5) :
    spinPairing (nortonUIntegerEmbed (monsterNortonMixedOddSpinNumerator k))
      (monsterNortonMixedOddSpinPacket k) = 128 := by
  rw [monsterNortonMixedOddSpinPacket, monsterNortonSpin_sparse_pairing]
  simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
    monsterNortonMixedOddSpinNumerator_coefficient, ← pow_two]
  simp_rw [coefficient_sq]
  norm_num

/-- The complete actual spin numerator equals the sparse packet at every spin coordinate. -/
theorem monsterNortonMixedOddSpinNumerator_sparse (k : Fin 5) :
    nortonUIntegerEmbed (monsterNortonMixedOddSpinNumerator k) =
      monsterNortonMixedOddSpinPacket k := by
  apply monsterNortonSpin_eq_of_pairing
  · rw [monsterNortonMixedOddSpinNumerator_norm, monsterNortonMixedOddSpinPacket_norm]
  · rw [monsterNortonMixedOddSpinPacket_pairing, monsterNortonMixedOddSpinNumerator_norm]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
