/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete seventh literal line-word state for every actual odd-output basis input. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortOddSixth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorPositiveTrialityPacket

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- The complete matrix-zero, odd-short, and tensor packet after the seventh literal operator. -/
noncomputable def monsterNortonEvenShortOddSeventhPacket (k : Fin 23) : GriessSpace :=
  monsterNortonEvenShortOddFifthCoefficient k •
    monsterNortonTensorPositivePacket (conwayTensorCoordinates
      (nortonUIntegerEmbed (nortonUIntegerQ y555NortonVQ
        (monsterNortonUCompactInverseNumerator (nortonUIntegerQ y555NortonVQ
          (monsterNortonSourceZInteger (monsterNortonEvenShortFirstUOddCode k))))) ⊗ₜ[ℝ]
            (monsterNortonUFiber.val.2⁻¹).val
              (Pi.single (monsterNortonEvenShortFirstUOddPosition k) 1)))

/-- Actual positive triality gives the complete seventh packet on each reached odd branch. -/
theorem monsterNortonEvenShortOddSeventhPacket_actual (k : Fin 23) :
    sExtra (monsterNortonEvenShortOddSixthPacket k) =
      monsterNortonEvenShortOddSeventhPacket k := by
  rw [monsterNortonEvenShortOddSixthPacket, map_smul,
    monsterNortonTensorLift_apply, monsterNortonTensorPositivePacket_actual]
  rfl

/-- Seven literal operators give this entire physical packet on all five odd-output inputs. -/
theorem monsterNortonEvenShortOddFirstSeven_actual (k : Fin 23)
    (hk : monsterNortonEvenShortFirstUIsOdd k = true) :
    sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis k)))))))) =
      qSign (monsterNortonEvenShortInitialVPhase k) • monsterNortonEvenShortOddSeventhPacket k := by
  rw [monsterNortonEvenShortOddFirstSix_actual k hk, map_smul,
    monsterNortonEvenShortOddSeventhPacket_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
