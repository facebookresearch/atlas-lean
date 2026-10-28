/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Computable coordinates for the actual sixteen octad blocks at the sixth first-line step. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ShortSixthInteger
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadTriality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual octad index for each of the sixteen reached source octads. -/
noncomputable def monsterNortonLine01OctadIndex (j : Fin 16) : Fin 759 :=
  monsterNortonOctadIndex (monsterNortonLine01ShortInverseOctadCode j)
    (monsterNortonLine01ShortInverseOctad_weight j)

private theorem octad_code_injective :
    Function.Injective monsterNortonLine01ShortInverseOctadCode := by
  decide +kernel

/-- The sixteen reached actual octad blocks are distinct. -/
theorem monsterNortonLine01OctadIndex_injective :
    Function.Injective monsterNortonLine01OctadIndex := by
  intro a b h
  apply octad_code_injective
  have he := congrArg golayOctadLabel h
  simpa only [monsterNortonLine01OctadIndex, monsterNortonOctadIndex_label] using he

private theorem octad_index_eq_iff (a b : Fin 16) :
    monsterNortonLine01OctadIndex a = monsterNortonLine01OctadIndex b ↔ a = b :=
  monsterNortonLine01OctadIndex_injective.eq_iff

private theorem physical_slot_column (k : Fin 16) :
    monsterNortonLine01ShortPhysicalSlot (monsterNortonLine01ShortPhysicalColumn k) = k := by
  revert k
  decide +kernel

private theorem short_single_octad (a : Fin 64) (k j : Fin 16) (e : Fin 64) :
    (Pi.single (monsterNortonLine01ShortInverseOutput a k) 1 : GriessShortIndex → ℤ)
      (Sum.inr (Sum.inl (monsterNortonLine01OctadIndex j, e))) =
        if monsterNortonLine01ShortInverseIsOctad a = true ∧
            monsterNortonLine01ShortInverseOctadId a k = j ∧
            monsterNortonLine01ShortInverseOctadSigns a k = e then 1 else 0 := by
  by_cases h : monsterNortonLine01ShortInverseIsOctad a = true
  · rw [monsterNortonLine01ShortInverseOutput, ite_eq_left h]
    change (Pi.single (Sum.inr (Sum.inl
      (monsterNortonLine01OctadIndex (monsterNortonLine01ShortInverseOctadId a k),
        monsterNortonLine01ShortInverseOctadSigns a k))) 1 : GriessShortIndex → ℤ)
      (Sum.inr (Sum.inl (monsterNortonLine01OctadIndex j, e))) = _
    simp [Pi.single_apply, octad_index_eq_iff, h, eq_comm]
  · rw [monsterNortonLine01ShortInverseOutput, ite_eq_right h]
    simp [h]

/-- The computable full integer scalar on each of the 1024 transported short summands. -/
def monsterNortonLine01ShortSixthSourceCoefficient (a : Fin 64) (k : Fin 16) : ℤ :=
  monsterNortonLine01InitialSpinSigns a *
    monsterNortonUNumerator1 (monsterNortonLine01ShortPhysicalColumn k) 0 *
    monsterNortonLine01ShortSixthIntegerCoefficient a (monsterNortonLine01ShortPhysicalColumn k)

/-- A computable integer coordinate in one of the actual sixteen reached octad blocks. -/
def monsterNortonLine01OctadSixthNumerator (j : Fin 16) (e : Fin 64) : ℤ :=
  ∑ a : Fin 64, ∑ k : Fin 16,
    if monsterNortonLine01ShortInverseIsOctad a = true ∧
        monsterNortonLine01ShortInverseOctadId a k = j ∧
        monsterNortonLine01ShortInverseOctadSigns a k = e then
      monsterNortonLine01ShortSixthSourceCoefficient a k else 0

/-- The computable octad numerator is exactly the actual short coordinate numerator. -/
theorem monsterNortonLine01OctadSixthNumerator_actual (j : Fin 16) (e : Fin 64) :
    monsterNortonLine01ShortSixthIntegerNumerator
        (Sum.inr (Sum.inl (monsterNortonLine01OctadIndex j, e))) =
      monsterNortonLine01OctadSixthNumerator j e := by
  simp only [monsterNortonLine01ShortSixthIntegerNumerator, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, physical_slot_column, short_single_octad, mul_ite,
    mul_one, mul_zero, monsterNortonLine01OctadSixthNumerator,
    monsterNortonLine01ShortSixthSourceCoefficient]

/-- Every reached octad coordinate has its exact actual real value. -/
theorem monsterNortonLine01OctadSixth_coordinates (j : Fin 16) (e : Fin 64) :
    (griessConwayEncode monsterNortonLine01TensorAfterVUExtraInverseVInverseUV).2.1
        (Sum.inr (Sum.inl (monsterNortonLine01OctadIndex j, e))) =
      (1 / 64 : ℝ) * (monsterNortonLine01OctadSixthNumerator j e : ℝ) := by
  change monsterNortonShortProjection monsterNortonLine01TensorAfterVUExtraInverseVInverseUV
    (Sum.inr (Sum.inl (monsterNortonLine01OctadIndex j, e))) = _
  rw [monsterNortonLine01ShortSixthInteger_actual]
  simp only [Pi.smul_apply, smul_eq_mul, monsterNortonLine01OctadSixthNumerator_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
