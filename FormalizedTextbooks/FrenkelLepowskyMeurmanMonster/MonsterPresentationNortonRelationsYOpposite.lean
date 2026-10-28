/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact conversion between the two triality orientations of low-code source y. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsYConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenCodeCube

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- For quarter-weight parity zero the opposite triality y is the product of x and literal y. -/
theorem monsterNortonYOpposite_word (a : Fin 2048)
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) :
    sourceGeneratedY ⟨a.val, by omega⟩ 0 =
      sourceGeneratedCode ⟨a.val, by omega⟩ 0 * y555NortonActualY ⟨a.val, by omega⟩ 0 := by
  have hx : sourceGeneratedCode ⟨a.val, by omega⟩ 0 ^ 2 = 1 := by
    rw [sourceGeneratedCode_square, ha]
    change qIntoGenerated 1 = 1
    exact map_one _
  have hxi : (sourceGeneratedCode ⟨a.val, by omega⟩ 0)⁻¹ =
      sourceGeneratedCode ⟨a.val, by omega⟩ 0 := by
    symm
    exact eq_inv_iff_mul_eq_one.mpr (by simpa only [pow_two] using hx)
  have hy : y555NortonActualY ⟨a.val, by omega⟩ 0 ^ 2 = 1 := by
    rw [y555NortonActualY_word]
    calc
      _ = extraIntoGenerated * (sourceGeneratedCode ⟨a.val, by omega⟩ 0 ^ 2) *
        extraIntoGenerated⁻¹ := by simp only [pow_two]; group
      _ = 1 := by rw [hx]; group
  have hyi : (y555NortonActualY ⟨a.val, by omega⟩ 0)⁻¹ =
      y555NortonActualY ⟨a.val, by omega⟩ 0 := by
    symm
    exact eq_inv_iff_mul_eq_one.mpr (by simpa only [pow_two] using hy)
  have hc := monsterNortonEvenStep_cube a ha
  rw [monsterNortonEvenStep_cube_word] at hc
  calc
    _ = (sourceGeneratedCode ⟨a.val, by omega⟩ 0)⁻¹ *
      (sourceGeneratedCode ⟨a.val, by omega⟩ 0 * sourceGeneratedY ⟨a.val, by omega⟩ 0 *
        y555NortonActualY ⟨a.val, by omega⟩ 0) *
          (y555NortonActualY ⟨a.val, by omega⟩ 0)⁻¹ := by group
    _ = _ := by rw [hc, mul_one, hxi, hyi]

/-- The opposite source y has the phase-correct Q conjugation obtained by its actual x factor. -/
theorem monsterNortonYOpposite_conjugation (a : Fin 2048)
    (ha : ((golayMaskWeight (golayEncodedMask a.val) / 4 : ℕ) : ZMod 2) = 0) (q : Q) :
    sourceGeneratedY ⟨a.val, by omega⟩ 0 * qIntoGenerated q *
      (sourceGeneratedY ⟨a.val, by omega⟩ 0)⁻¹ =
    qIntoGenerated (sourceQCode ⟨a.val, by omega⟩ 0 * monsterNortonYImage a q *
      (sourceQCode ⟨a.val, by omega⟩ 0)⁻¹) := by
  rw [monsterNortonYOpposite_word a ha, mul_inv_rev]
  calc
    _ = sourceGeneratedCode ⟨a.val, by omega⟩ 0 *
      (y555NortonActualY ⟨a.val, by omega⟩ 0 * qIntoGenerated q *
        (y555NortonActualY ⟨a.val, by omega⟩ 0)⁻¹) *
          (sourceGeneratedCode ⟨a.val, by omega⟩ 0)⁻¹ := by group
    _ = _ := by
      rw [monsterNortonYWord_conjugation a ha]
      rw [show sourceGeneratedCode ⟨a.val, by omega⟩ 0 =
        qIntoGenerated (sourceQCode ⟨a.val, by omega⟩ 0) from rfl]
      rw [map_mul, map_mul, map_inv]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
