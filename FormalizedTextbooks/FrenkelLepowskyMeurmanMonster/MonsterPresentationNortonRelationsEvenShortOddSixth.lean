/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Whole actual fifth and sixth line-word states for the five odd-output basis inputs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortFourth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSourceZQInverseInteger
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQScaledCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- Exact real coefficient multiplying the actual inverse integer spin numerator. -/
noncomputable def monsterNortonEvenShortOddFifthCoefficient (k : Fin 23) : ℝ :=
  (qSign (golayMaskWeight (golayEncodedMask (monsterNortonEvenShortFirstUOddCode k).val) / 4 : ℕ) /
    Real.sqrt 2) * (-1 / 8)

/-- The fifth tensor packet retains the genuine Gaussian spin numerator and inverse Leech column. -/
noncomputable def monsterNortonEvenShortOddFifthPacket (k : Fin 23) : GriessSpace :=
  monsterNortonEvenShortOddFifthCoefficient k •
    monsterNortonTensorLift (conwayTensorCoordinates
      (nortonUIntegerEmbed (monsterNortonUCompactInverseNumerator
        (nortonUIntegerQ y555NortonVQ
          (monsterNortonSourceZInteger (monsterNortonEvenShortFirstUOddCode k)))) ⊗ₜ[ℝ]
            (monsterNortonUFiber.val.2⁻¹).val
              (Pi.single (monsterNortonEvenShortFirstUOddPosition k) 1)))

/-- Inverse literal U gives the entire stated tensor packet on each reached odd branch. -/
theorem monsterNortonEvenShortOddFifthPacket_actual (k : Fin 23)
    (hk : monsterNortonEvenShortFirstUIsOdd k = true) :
    (y555NortonActualU⁻¹).val (monsterNortonEvenShortFourthPacket k) =
      monsterNortonEvenShortOddFifthPacket k := by
  unfold monsterNortonEvenShortFourthPacket
  rw [ite_eq_left hk, ← monsterNortonQ_source_Z_explicit,
    monsterNortonU_inverse_Q_source_Z]
  rfl

/-- Next V applies its exact integer Q action to the complete fifth spin numerator. -/
noncomputable def monsterNortonEvenShortOddSixthPacket (k : Fin 23) : GriessSpace :=
  monsterNortonEvenShortOddFifthCoefficient k •
    monsterNortonTensorLift (conwayTensorCoordinates
      (nortonUIntegerEmbed (nortonUIntegerQ y555NortonVQ
        (monsterNortonUCompactInverseNumerator (nortonUIntegerQ y555NortonVQ
          (monsterNortonSourceZInteger (monsterNortonEvenShortFirstUOddCode k))))) ⊗ₜ[ℝ]
            (monsterNortonUFiber.val.2⁻¹).val
              (Pi.single (monsterNortonEvenShortFirstUOddPosition k) 1)))

/-- Literal V transports the entire fifth tensor packet to the stated sixth packet. -/
theorem monsterNortonEvenShortOddSixthPacket_actual (k : Fin 23) :
    y555NortonV.val (monsterNortonEvenShortOddFifthPacket k) =
      monsterNortonEvenShortOddSixthPacket k := by
  rw [monsterNortonEvenShortOddFifthPacket, y555NortonV, map_smul,
    monsterNortonQ_integer_rank_one]
  rfl

/-- Six literal operators give the complete original-coordinate image on every odd branch. -/
theorem monsterNortonEvenShortOddFirstSix_actual (k : Fin 23)
    (hk : monsterNortonEvenShortFirstUIsOdd k = true) :
    y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis k))))))) =
      qSign (monsterNortonEvenShortInitialVPhase k) • monsterNortonEvenShortOddSixthPacket k := by
  rw [monsterNortonEvenShortFirstFour_actual, map_smul,
    monsterNortonEvenShortOddFifthPacket_actual k hk, map_smul,
    monsterNortonEvenShortOddSixthPacket_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
