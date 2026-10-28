/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Cubic relation for genuine even source codes of quarter parity zero. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenCodeCubeTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationY82SourceBinding
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
variable (a : Fin 2048)

/-- The genuine cube is a product of three actual local code conjugates. -/
theorem monsterNortonEvenStep_cube_word :
    (monsterNortonEvenStep a) ^ 3 =
      sourceGeneratedCode ⟨a.val, by omega⟩ 0 * sourceGeneratedY ⟨a.val, by omega⟩ 0 *
        y555NortonActualY ⟨a.val, by omega⟩ 0 := by
  have hp : extraIntoGenerated * extraIntoGenerated = extraIntoGenerated⁻¹ := by
    have h := congrArg Inv.inv extraIntoGenerated_inv_mul_inv
    simpa only [mul_inv_rev, inv_inv] using h
  unfold monsterNortonEvenStep
  rw [monsterSourceTriality, y555NortonActualY_word]
  change (sourceGeneratedCode ⟨a.val, by omega⟩ 0 * extraIntoGenerated⁻¹) ^ 3 =
    sourceGeneratedCode ⟨a.val, by omega⟩ 0 *
      (extraIntoGenerated⁻¹ * sourceGeneratedCode ⟨a.val, by omega⟩ 0 * extraIntoGenerated) *
      (extraIntoGenerated * sourceGeneratedCode ⟨a.val, by omega⟩ 0 * extraIntoGenerated⁻¹)
  symm
  calc
    _ = sourceGeneratedCode ⟨a.val, by omega⟩ 0 * extraIntoGenerated⁻¹ *
      sourceGeneratedCode ⟨a.val, by omega⟩ 0 * (extraIntoGenerated * extraIntoGenerated) *
      sourceGeneratedCode ⟨a.val, by omega⟩ 0 * extraIntoGenerated⁻¹ := by group
    _ = _ := by rw [hp, pow_succ, pow_two]; group

/-- The actual cube lies in the genuine local image, using the proved full centralizer. -/
theorem monsterNortonEvenStep_cube_mem_local :
    (monsterNortonEvenStep a) ^ 3 ∈ localIntoGenerated.range := by
  have ha : sourceGeneratedCode ⟨a.val, by omega⟩ 0 ∈ localIntoGenerated.range :=
    ⟨inclQ (sourceQCode ⟨a.val, by omega⟩ 0), rfl⟩
  have hb : sourceGeneratedY ⟨a.val, by omega⟩ 0 ∈ localIntoGenerated.range := by
    rw [← generatedCentralizer_eq_local_range]
    exact sourceGeneratedY_mem_centralizer ⟨a.val, by omega⟩ 0
  rw [(monsterNortonEvenStep_cube_word a)]
  exact localIntoGenerated.range.mul_mem (localIntoGenerated.range.mul_mem ha hb)
    (monsterSourceY_word_mem_local ⟨a.val, by omega⟩ 0)

/-- The actual point-times-triality cubic is identity by the faithful local tensor constituent. -/
theorem monsterNortonEvenStep_cube
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) :
      (monsterNortonEvenStep a) ^ 3 = 1 := by
  obtain ⟨h, hh⟩ := (monsterNortonEvenStep_cube_mem_local a)
  have hρ : rhoLocal h = ((monsterNortonEvenStep a) ^ 3).val := congrArg Subtype.val hh
  have he : h = 1 := by
    apply monsterLocalTensor_identifies
    intro x
    rw [hρ, map_one]
    exact (monsterNortonEvenStep_cube_tensor a ha) x
  rw [he, map_one] at hh
  exact hh.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
