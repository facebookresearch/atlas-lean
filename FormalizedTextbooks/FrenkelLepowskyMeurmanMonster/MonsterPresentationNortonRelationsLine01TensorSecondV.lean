/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete sixth literal step of the actual first Norton line-pair word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01TensorInverseU
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQScaledCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- The finite actual polar phase on the short label reached by inverse Norton u. -/
def monsterNortonLine01ShortInverseVPhase (a : Fin 64) (i : Fin 24) : ZMod 2 :=
  qBeta (toAdd y555NortonVQ.base)
      (toAdd (monsterNortonLine01ShortInverseOutputQ a
        (monsterNortonLine01ShortPhysicalSlot i)).base) +
    qBeta (toAdd (monsterNortonLine01ShortInverseOutputQ a
      (monsterNortonLine01ShortPhysicalSlot i)).base) (toAdd y555NortonVQ.base)

/-- The full signed short and integer rank-one tensor state after the next literal v. -/
noncomputable def monsterNortonLine01SourcePairAfterVInverseUV (a : Fin 64) (i : Fin 24) :
    GriessSpace :=
  ((qSign (golayLabelCoefficients (monsterNortonLine01InitialSpinIndices a) 11) *
      (if (golayEncodedMask (monsterNortonLine01ShortInputCode a).val).testBit i.val then -1
        else 1)) *
      qSign (monsterNortonSourceXQFinitePhase y555NortonVQ
        (monsterNortonLine01ShortInputCode a) i)) •
    griessConwayDecode (0,
      ((qSign (monsterNortonLine01ShortInversePhase a (monsterNortonLine01ShortPhysicalSlot i)) *
        qSign (monsterNortonLine01ShortInverseVPhase a i)) •
          Pi.single (monsterNortonLine01ShortInverseOutput a
            (monsterNortonLine01ShortPhysicalSlot i)) 1, 0)) +
    qSign (golayMaskWeight (golayEncodedMask (monsterNortonLine01ShortInputCode a).val) / 4 : ℕ) •
      ((((if (golayEncodedMask (monsterNortonLine01ShortInputCode a).val).testBit i.val then
        (-1 : ℝ) else 1) / Real.sqrt 2) * (-1 / 8 : ℝ)) •
        monsterNortonTensorLift (conwayTensorCoordinates
          (nortonUIntegerEmbed (nortonUIntegerQ y555NortonVQ
            (monsterNortonUCompactInverseNumerator (nortonUIntegerQ y555NortonVQ
              (monsterNortonSourceYInteger (monsterNortonLine01ShortInputCode a))))) ⊗ₜ[ℝ]
                (monsterNortonUFiber.val.2⁻¹).val (Pi.single i 1))))

/-- Literal v has the displayed complete actual action on every reached source summand. -/
theorem monsterNortonLine01SourcePairAfterVInverseUV_actual (a : Fin 64) (i : Fin 24) :
    y555NortonV.val (monsterNortonLine01SourcePairAfterVInverseU a i) =
      monsterNortonLine01SourcePairAfterVInverseUV a i := by
  rw [y555NortonV, monsterNortonLine01SourcePairAfterVInverseU, map_add,
    map_smul, map_smul, map_smul, monsterNortonQ_scaled_short,
    monsterNortonQ_integer_rank_one, ← monsterNortonShortQSource_eq,
    monsterNortonLine01ShortInverseOutputQ_actual]
  rfl

/-- The complete finite rational state after the sixth literal first-line word step. -/
noncomputable def monsterNortonLine01TensorAfterVUExtraInverseVInverseUV : GriessSpace :=
  (1 / 64 : ℝ) • ∑ a : Fin 64,
    (monsterNortonLine01InitialSpinSigns a : ℝ) • ∑ i : Fin 24,
      (monsterNortonUNumerator1 i 0 : ℝ) • monsterNortonLine01SourcePairAfterVInverseUV a i

/-- The sixth literal word step is an equality of entire actual Griess vectors. -/
theorem monsterNortonLine01TensorSecondV_actual :
    y555NortonV.val monsterNortonLine01TensorAfterVUExtraInverseVInverseU =
      monsterNortonLine01TensorAfterVUExtraInverseVInverseUV := by
  rw [monsterNortonLine01TensorAfterVUExtraInverseVInverseU, map_smul, map_sum]
  simp only [map_smul, map_sum, monsterNortonLine01SourcePairAfterVInverseUV_actual]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
