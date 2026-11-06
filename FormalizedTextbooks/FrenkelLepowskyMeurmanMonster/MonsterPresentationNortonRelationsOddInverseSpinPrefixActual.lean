/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual two-term monomial prefixes determined by norm and supported coordinates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOddInverseSpinPrefixData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOddInverseSpinNorm

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The exact two-term integer candidate before the inverse Gaussian. -/
def monsterNortonOddPrefixCache (k : Fin 5) : NortonUIntegerVector :=
  fun n => ∑ i : Fin 2, monsterNortonOddPrefixCoefficient k i *
    (Pi.single (monsterNortonOddPrefixLabel k i) 1 : NortonUIntegerVector) n

private theorem sourceLabel_injective (k : Fin 5) :
    Function.Injective (fun i => golayLabelCoefficients (monsterNortonOddPrefixLabel k i)) :=
  golayLabelCoefficients_bijective.injective.comp (monsterNortonOddPrefixLabel_injective k)

private theorem coefficient_sq (k : Fin 5) (i : Fin 2) :
    (monsterNortonOddPrefixCoefficient k i : ℝ) ^ 2 = 1 := by
  exact_mod_cast monsterNortonOddPrefixCoefficient_sq k i

/-- The complete two-term candidate has actual squared norm two. -/
theorem monsterNortonOddPrefixCache_norm (k : Fin 5) :
    spinPairing (nortonUIntegerEmbed (monsterNortonOddPrefixCache k))
      (nortonUIntegerEmbed (monsterNortonOddPrefixCache k)) = 2 := by
  unfold monsterNortonOddPrefixCache
  rw [monsterNortonUIntegerEmbed_packet,
    monsterNortonSpin_sparse_norm _ _ (sourceLabel_injective k)]
  simp_rw [coefficient_sq]
  norm_num

/-- Both actual supported prefix values give the maximal whole spin pairing. -/
theorem monsterNortonOddPrefixCache_pairing (k : Fin 5) :
    spinPairing (nortonUIntegerEmbed (monsterNortonOddInverseSpinPrefix
      (monsterNortonEvenShortFirstUOddCode (monsterNortonOddPrefixBasisIndex k))))
      (nortonUIntegerEmbed (monsterNortonOddPrefixCache k)) = 2 := by
  unfold monsterNortonOddPrefixCache
  rw [monsterNortonUIntegerEmbed_packet,
    monsterNortonSpin_sparse_pairing]
  simp only [nortonUIntegerEmbed, nortonUIntegerLabel_coeff,
    monsterNortonOddPrefix_coefficient, ← pow_two]
  simp_rw [coefficient_sq]
  norm_num

/-- The integer prefix equals the two-term function at every original coordinate. -/
theorem monsterNortonOddInverseSpinPrefix_cache (k : Fin 5) :
    monsterNortonOddInverseSpinPrefix
      (monsterNortonEvenShortFirstUOddCode (monsterNortonOddPrefixBasisIndex k)) =
        monsterNortonOddPrefixCache k := by
  apply monsterNortonUIntegerEmbed_injective
  apply monsterNortonSpin_eq_of_pairing
  · rw [monsterNortonOddInverseSpinPrefix_norm, monsterNortonOddPrefixCache_norm]
  · rw [monsterNortonOddPrefixCache_pairing, monsterNortonOddInverseSpinPrefix_norm]

/-- The genuine compact numerator factors through its entire actual monomial prefix. -/
theorem monsterNortonOddInverseSpinNumerator_prefix (d : Fin 2048) :
    monsterNortonOddInverseSpinNumerator d =
      nortonUIntegerQ y555NortonVQ
        (monsterNortonUCompactIntegerDiagonal (monsterNortonUCompactDiagonal 1)
          (monsterNortonUCompactIntegerPermutation (monsterNortonUCompactPermutation 1).symm
            (nortonUIntegerG (monsterNortonOddInverseSpinPrefix d)))) := rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
