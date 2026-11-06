/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Whole preferred-short Gram entries of the actual positive-triality source packets. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortPositiveTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfGram

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem form_symm (x y : GriessSpace) : griessForm x y = griessForm y x := by
  rw [griessForm_apply, griessForm_apply]
  unfold griessFormFun
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A whole pair extra packet has the exact signed one-half short coordinate on its pair. -/
theorem monsterNortonPairExtra_pair_form (s t : Fin 2) (p q : Fin 276) :
    griessForm (monsterNortonShortExtraPacket (Sum.inl (s, p)))
      (monsterNortonPureShort (Sum.inl (t, q))) =
        if p = q then (if s = 0 then (1 / 2 : ℝ) else -1 / 2) else 0 := by
  rw [monsterNortonShortExtraPacket, monsterNortonPairShort_ABC]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  fin_cases s <;> fin_cases t <;> by_cases hp : p = q <;>
    simp [monsterNortonForm_ABC_ABC, hp] <;> norm_num

private theorem ABC_octad (s : Fin 3) (p : Fin 276) (d : Fin 759) (e : Fin 64) :
    griessForm (trialityABCBasis s p)
      (monsterNortonPureShort (Sum.inr (Sum.inl (d, e)))) = 0 := by
  rw [form_symm]
  unfold monsterNortonPureShort
  rw [← monsterNortonOctadShortVector_single d e 1, monsterNortonForm_octad_ABC]

/-- Every whole pair extra packet is orthogonal to all preferred octad units. -/
theorem monsterNortonPairExtra_octad_form (s : Fin 2) (p : Fin 276)
    (d : Fin 759) (e : Fin 64) :
    griessForm (monsterNortonShortExtraPacket (Sum.inl (s, p)))
      (monsterNortonPureShort (Sum.inr (Sum.inl (d, e)))) = 0 := by
  simp only [monsterNortonShortExtraPacket, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, ABC_octad, mul_zero, add_zero]

/-- Every whole octad extra packet is orthogonal to both preferred pair families. -/
theorem monsterNortonOctadExtra_pair_form (d : Fin 759) (e : Fin 64)
    (s : Fin 2) (p : Fin 276) :
    griessForm (monsterNortonShortExtraPacket (Sum.inr (Sum.inl (d, e))))
      (monsterNortonPureShort (Sum.inl (s, p))) = 0 := by
  rw [monsterNortonShortExtraPacket, monsterNortonPairShort_ABC]
  simp only [map_add, map_smul, smul_eq_mul, monsterNortonForm_octad_ABC,
    mul_zero, add_zero]

/-- Complete octad extra pairings retain the exact positive Fourier row sign. -/
theorem monsterNortonOctadExtra_octad_form (a b : Fin 4096)
    (ha : golayMaskWeight (golayEncodedMask a.val) = 8)
    (hb : golayMaskWeight (golayEncodedMask b.val) = 8) (e f : Fin 64) :
    griessForm (monsterNortonShortExtraPacket
      (Sum.inr (Sum.inl (monsterNortonOctadIndex a ha, e))))
      (monsterNortonPureShort (Sum.inr (Sum.inl (monsterNortonOctadIndex b hb, f)))) =
        if a = b then (monsterNortonOctadPositiveInteger f e : ℝ) / 8 else 0 := by
  rw [monsterNortonShortExtraPacket, monsterNortonForm_octad_unit_code,
    monsterNortonOctadTriality_single, monsterNortonOctadPositiveInteger_actual]
  simp only [mul_one]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
