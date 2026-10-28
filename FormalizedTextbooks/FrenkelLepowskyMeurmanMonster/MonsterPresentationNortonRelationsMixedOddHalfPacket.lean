/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete literal forward-half packets for the five odd inverse-spin branches. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMixedOddSpinActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ReturnFromPackets

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The full matrix-zero mixed packet with the actual phase and sparse spin numerator. -/
noncomputable def monsterNortonMixedOddHalfPacket (k : Fin 5) : GriessSpace :=
  qSign (monsterNortonEvenShortInitialVPhase (monsterNortonMixedOddBasisIndex k)) •
    (monsterNortonEvenShortOddFifthCoefficient (monsterNortonMixedOddBasisIndex k) •
      monsterNortonTensorPositivePacket (conwayTensorCoordinates
        (monsterNortonMixedOddSpinPacket k ⊗ₜ[ℝ]
          (monsterNortonUFiber.val.2⁻¹).val
            (Pi.single (monsterNortonEvenShortFirstUOddPosition
              (monsterNortonMixedOddBasisIndex k)) 1))))

/-- All seven actual literal operators give the complete sparse mixed packet. -/
theorem monsterNortonMixedOddHalfPacket_actual (k : Fin 5) :
    sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis
          (monsterNortonMixedOddBasisIndex k))))))))) =
      monsterNortonMixedOddHalfPacket k := by
  rw [monsterNortonEvenShortOddFirstSeven_actual _ (monsterNortonMixedOdd_firstU_odd k)]
  change qSign (monsterNortonEvenShortInitialVPhase (monsterNortonMixedOddBasisIndex k)) •
    (monsterNortonEvenShortOddFifthCoefficient (monsterNortonMixedOddBasisIndex k) •
      monsterNortonTensorPositivePacket (conwayTensorCoordinates
        (nortonUIntegerEmbed (monsterNortonMixedOddSpinNumerator k) ⊗ₜ[ℝ]
          (monsterNortonUFiber.val.2⁻¹).val
            (Pi.single (monsterNortonEvenShortFirstUOddPosition
              (monsterNortonMixedOddBasisIndex k)) 1)))) = _
  rw [monsterNortonMixedOddSpinNumerator_sparse]
  rfl

/-- The whole actual mixed packet has norm one in the original Griess form. -/
theorem monsterNortonMixedOddHalfPacket_norm (k : Fin 5) :
    griessForm (monsterNortonMixedOddHalfPacket k) (monsterNortonMixedOddHalfPacket k) = 1 := by
  let x := monsterNortonPureShort (monsterNortonEvenShortBasis (monsterNortonMixedOddBasisIndex k))
  have h := generated_group_preserves_griessForm monsterNortonSecondForwardHalf x x
  change griessForm
    (sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val x)))))))
    (sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
      (y555NortonActualU.val (y555NortonV.val x))))))) = griessForm x x at h
  dsimp only [x] at h
  rw [monsterNortonMixedOddHalfPacket_actual, monsterNortonPureShort_form] at h
  simpa only [ite_true] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
