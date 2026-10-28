/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- An exact integer numerator for the sixth actual first-line short state. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ShortSixthCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ColumnEnumeration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQIntegerSparse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The exact integer scalar on a reached short basis vector, including all four actual phases. -/
def monsterNortonLine01ShortSixthIntegerCoefficient (a : Fin 64) (i : Fin 24) : ℤ :=
  nortonUIntegerSign (golayLabelCoefficients (monsterNortonLine01InitialSpinIndices a) 11) *
    (if (golayEncodedMask (monsterNortonLine01ShortInputCode a).val).testBit i.val then -1
      else 1) *
    nortonUIntegerSign (monsterNortonSourceXQFinitePhase y555NortonVQ
      (monsterNortonLine01ShortInputCode a) i) *
    (nortonUIntegerSign (monsterNortonLine01ShortInversePhase a
        (monsterNortonLine01ShortPhysicalSlot i)) *
      nortonUIntegerSign (monsterNortonLine01ShortInverseVPhase a i))

/-- Real casting retains the actual complete short scalar. -/
theorem monsterNortonLine01ShortSixthIntegerCoefficient_real (a : Fin 64) (i : Fin 24) :
    (monsterNortonLine01ShortSixthIntegerCoefficient a i : ℝ) =
      monsterNortonLine01ShortSixthCoefficient a i := by
  unfold monsterNortonLine01ShortSixthIntegerCoefficient monsterNortonLine01ShortSixthCoefficient
  simp only [Int.cast_mul, nortonUIntegerSign_real, Int.cast_ite, Int.cast_neg,
    Int.cast_one]

/-- The actual short numerator uses only the sixteen nonzero physical columns. -/
noncomputable def monsterNortonLine01ShortSixthIntegerNumerator : GriessShortIndex → ℤ :=
  ∑ a : Fin 64, ∑ k : Fin 16,
    (monsterNortonLine01InitialSpinSigns a *
      monsterNortonUNumerator1 (monsterNortonLine01ShortPhysicalColumn k) 0 *
      monsterNortonLine01ShortSixthIntegerCoefficient a
        (monsterNortonLine01ShortPhysicalColumn k)) •
      Pi.single (monsterNortonLine01ShortInverseOutput a
        (monsterNortonLine01ShortPhysicalSlot (monsterNortonLine01ShortPhysicalColumn k))) 1

/-- The entire sixth short state is exactly one sixty-fourth of this genuine integer numerator. -/
theorem monsterNortonLine01ShortSixthInteger_actual :
    monsterNortonShortProjection monsterNortonLine01TensorAfterVUExtraInverseVInverseUV =
      (1 / 64 : ℝ) • fun r => (monsterNortonLine01ShortSixthIntegerNumerator r : ℝ) := by
  rw [monsterNortonLine01ShortSixth_coordinates]
  simp_rw [monsterNortonLine01_supported_columns]
  apply congrArg (fun X : GriessShortIndex → ℝ => (1 / 64 : ℝ) • X)
  funext r
  simp only [monsterNortonLine01ShortSixthIntegerNumerator, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul,
    monsterNortonLine01ShortSixthIntegerCoefficient_real]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [show ((Pi.single (monsterNortonLine01ShortInverseOutput a
      (monsterNortonLine01ShortPhysicalSlot (monsterNortonLine01ShortPhysicalColumn k)))
        1 : GriessShortIndex → ℤ) r : ℝ) =
      (Pi.single (monsterNortonLine01ShortInverseOutput a
        (monsterNortonLine01ShortPhysicalSlot (monsterNortonLine01ShortPhysicalColumn k)))
          1 : GriessShortIndex → ℝ) r by
    simp only [Pi.single_apply, Int.cast_ite, Int.cast_one, Int.cast_zero]]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
