/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete fifth literal step of the actual first Norton line-pair word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ShortInverse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01TensorVSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQSourceInteger

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- The exact signed short vector and single integer tensor numerator reached by inverse u. -/
noncomputable def monsterNortonLine01SourcePairAfterVInverseU (a : Fin 64) (i : Fin 24) :
    GriessSpace :=
  ((qSign (golayLabelCoefficients (monsterNortonLine01InitialSpinIndices a) 11) *
      (if (golayEncodedMask (monsterNortonLine01ShortInputCode a).val).testBit i.val then -1
        else 1)) *
      qSign (monsterNortonSourceXQFinitePhase y555NortonVQ
        (monsterNortonLine01ShortInputCode a) i)) •
    griessConwayDecode (0,
      (qSign (monsterNortonLine01ShortInversePhase a (monsterNortonLine01ShortPhysicalSlot i)) •
        Pi.single (monsterNortonLine01ShortInverseOutput a
          (monsterNortonLine01ShortPhysicalSlot i)) 1, 0)) +
    qSign (golayMaskWeight (golayEncodedMask (monsterNortonLine01ShortInputCode a).val) / 4 : ℕ) •
      ((((if (golayEncodedMask (monsterNortonLine01ShortInputCode a).val).testBit i.val then
        (-1 : ℝ) else 1) / Real.sqrt 2) * (-1 / 8 : ℝ)) •
        monsterNortonTensorLift (conwayTensorCoordinates
          (nortonUIntegerEmbed (monsterNortonUCompactInverseNumerator
            (nortonUIntegerQ y555NortonVQ
              (monsterNortonSourceYInteger (monsterNortonLine01ShortInputCode a)))) ⊗ₜ[ℝ]
                (monsterNortonUFiber.val.2⁻¹).val (Pi.single i 1))))

/-- On every supported column the fifth word step has the full displayed actual image. -/
theorem monsterNortonLine01SourcePairAfterVInverseU_actual (a : Fin 64) (i : Fin 24)
    (hi : monsterNortonUNumerator1 i 0 ≠ 0) :
    (y555NortonActualU⁻¹).val (monsterNortonLine01SourcePairAfterV
      (golayLabelCoefficients (monsterNortonLine01InitialSpinIndices a)) i) =
        monsterNortonLine01SourcePairAfterVInverseU a i := by
  rw [monsterNortonLine01SourcePairAfterV, monsterNortonLine01ShortInputCode_actual,
    monsterNortonSourceXQFinitePhase_actual, map_add, map_smul, map_smul,
    monsterNortonLine01ShortInverse_supported a i hi,
    ← monsterNortonQ_source_Y_explicit, monsterNortonU_inverse_Q_source_Y]
  rfl

/-- The complete finite rational state after v,u,extra inverse,v,u inverse. -/
noncomputable def monsterNortonLine01TensorAfterVUExtraInverseVInverseU : GriessSpace :=
  (1 / 64 : ℝ) • ∑ a : Fin 64,
    (monsterNortonLine01InitialSpinSigns a : ℝ) • ∑ i : Fin 24,
      (monsterNortonUNumerator1 i 0 : ℝ) • monsterNortonLine01SourcePairAfterVInverseU a i

/-- The fifth literal word step is an equality of complete actual Griess vectors. -/
theorem monsterNortonLine01TensorInverseU_actual :
    (y555NortonActualU⁻¹).val monsterNortonLine01TensorAfterVUExtraInverseV =
      monsterNortonLine01TensorAfterVUExtraInverseVInverseU := by
  simp only [monsterNortonLine01TensorAfterVUExtraInverseV,
    monsterNortonLine01TensorAfterVUExtraInverseVInverseU, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : monsterNortonUNumerator1 i 0 = 0
  · simp only [hi, Int.cast_zero, zero_smul]
  · rw [monsterNortonLine01SourcePairAfterVInverseU_actual a i hi]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
