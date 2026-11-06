/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual literal first-line square returns on eleven original preferred pair units. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfReturnActualPairing
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfActual

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem v_inverse : y555NortonV⁻¹ = y555NortonV := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_two, y555NortonV_square]

private theorem difference_word :
    y555NortonLine monsterSourceTriality 0 * (y555NortonLine monsterSourceTriality 1)⁻¹ =
      y555NortonV * extraIntoGenerated * y555NortonV * y555NortonActualU⁻¹ *
        y555NortonV * extraIntoGenerated⁻¹ * y555NortonActualU * y555NortonV := by
  unfold y555NortonLine y555NortonConjugate
  change y555NortonV * ((y555NortonActualU ^ (0 : Fin 13).val)⁻¹ *
      (y555NortonV * monsterSourceTriality) * y555NortonActualU ^ (0 : Fin 13).val)⁻¹ *
    (y555NortonV * ((y555NortonActualU ^ (1 : Fin 13).val)⁻¹ *
      (y555NortonV * monsterSourceTriality) * y555NortonActualU ^ (1 : Fin 13).val)⁻¹)⁻¹ = _
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, inv_one, one_mul, mul_one,
    monsterSourceTriality, mul_inv_rev, inv_inv, v_inverse]
  group

private theorem inverse_word :
    (y555NortonLine monsterSourceTriality 0 * (y555NortonLine monsterSourceTriality 1)⁻¹)⁻¹ =
      y555NortonV * y555NortonActualU⁻¹ * extraIntoGenerated * y555NortonV *
        y555NortonActualU * y555NortonV * extraIntoGenerated⁻¹ * y555NortonV := by
  rw [difference_word]
  simp only [mul_inv_rev, inv_inv, v_inverse]
  group

private theorem generated_mul_apply (a b : G) (x : GriessSpace) :
    (a * b).val x = a.val (b.val x) := rfl

private theorem generated_inverse_apply (g : G) (x : GriessSpace) :
    g.val ((g⁻¹).val x) = x :=
  LinearEquiv.apply_symm_apply _ _

private theorem input_pair (q : Fin 11) :
    monsterNortonEvenShortBasis
      (monsterNortonPairHalfBasisIndex (monsterNortonPairReturnCandidate q)) =
      Sum.inl (monsterNortonPairReturnFamily q,
        monsterNortonEvenShortPairIndex (monsterNortonPairReturnOriginal q)) := by
  fin_cases q <;> rfl

/-- Both whole literal line-word halves have maximal pairing on every covered original pair. -/
theorem monsterNortonLineZeroOne_pair_return_halves (q : Fin 11) :
    griessForm ((y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 1)⁻¹).val
        (monsterNortonPureShort (monsterNortonEvenShortBasis
          (monsterNortonPairHalfBasisIndex (monsterNortonPairReturnCandidate q)))))
      (((y555NortonLine monsterSourceTriality 0 *
        (y555NortonLine monsterSourceTriality 1)⁻¹)⁻¹).val
          (monsterNortonPureShort (monsterNortonEvenShortBasis
            (monsterNortonPairHalfBasisIndex (monsterNortonPairReturnCandidate q))))) = 1 := by
  rw [inverse_word, difference_word]
  simp only [generated_mul_apply]
  change griessForm
    (y555NortonV.val (sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val
      (sExtra.symm (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis
          (monsterNortonPairHalfBasisIndex (monsterNortonPairReturnCandidate q))))))))))))
    (y555NortonV.val ((y555NortonActualU⁻¹).val (sExtra (y555NortonV.val
      (y555NortonActualU.val (y555NortonV.val (sExtra.symm (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis
          (monsterNortonPairHalfBasisIndex (monsterNortonPairReturnCandidate q)))))))))))) = 1
  rw [generated_group_preserves_griessForm y555NortonV,
    monsterNortonEvenShortPairHalf_actual, input_pair,
    monsterNortonEvenShortPairsInverseFirstSix_normalized]
  have h := generated_group_preserves_griessForm y555NortonActualU
    (monsterNortonPairHalfPacket (monsterNortonPairReturnCandidate q))
    ((y555NortonActualU⁻¹).val (monsterNortonEvenShortPairsInverseSixthNormalized
      (monsterNortonPairReturnOriginal q) (monsterNortonPairReturnFamily q)))
  rw [generated_inverse_apply] at h
  rw [← h]
  exact monsterNortonPairReturnU_pairing_one q

/-- The actual literal first-line difference square fixes each entire covered pair unit. -/
theorem monsterNortonLineZeroOneSquare_pair_returns (q : Fin 11) :
    ((y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 1)⁻¹) ^ 2).val
        (monsterNortonPureShort (monsterNortonEvenShortBasis
          (monsterNortonPairHalfBasisIndex (monsterNortonPairReturnCandidate q)))) =
      monsterNortonPureShort (monsterNortonEvenShortBasis
        (monsterNortonPairHalfBasisIndex (monsterNortonPairReturnCandidate q))) :=
  monsterNortonGenerated_square_short_fixed_of_halves _ _
    (monsterNortonLineZeroOne_pair_return_halves q)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
