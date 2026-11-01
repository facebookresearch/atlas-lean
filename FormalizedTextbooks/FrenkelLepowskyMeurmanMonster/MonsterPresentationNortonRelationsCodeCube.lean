/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual adjacent Norton first-line Coxeter cubic, proved by faithful local tensor action. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeCubeTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationY82SourceBinding

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The initial positive point is exactly the literal source x400 lift. -/
theorem monsterNortonPoint_zero_sourceCode : y555NortonPointQ 0 = sourceQCode 1024 0 := by
  apply NormalizedCocycleExtension.Extension.ext
  · rfl
  · apply Multiplicative.toAdd.injective
    decide +kernel

/-- The initial point also commutes with the actual Norton v. -/
theorem monsterNortonVQ_commute_point_zero :
    y555NortonVQ * y555NortonPointQ 0 = y555NortonPointQ 0 * y555NortonVQ := by
  rw [q_mul_comm_iff]
  decide +kernel

/-- The genuine cube is a product of three actual local code conjugates. -/
theorem monsterNortonInitialStep_cube_word :
    monsterNortonInitialStep ^ 3 =
      sourceGeneratedCode 1024 0 * sourceGeneratedY 1024 0 * y555NortonActualY 1024 0 := by
  have hp : extraIntoGenerated * extraIntoGenerated = extraIntoGenerated⁻¹ := by
    have h := congrArg Inv.inv extraIntoGenerated_inv_mul_inv
    simpa only [mul_inv_rev, inv_inv] using h
  unfold monsterNortonInitialStep
  rw [monsterSourceTriality, y555NortonActualY_word]
  change (sourceGeneratedCode 1024 0 * extraIntoGenerated⁻¹) ^ 3 =
    sourceGeneratedCode 1024 0 *
      (extraIntoGenerated⁻¹ * sourceGeneratedCode 1024 0 * extraIntoGenerated) *
      (extraIntoGenerated * sourceGeneratedCode 1024 0 * extraIntoGenerated⁻¹)
  symm
  calc
    _ = sourceGeneratedCode 1024 0 * extraIntoGenerated⁻¹ *
      sourceGeneratedCode 1024 0 * (extraIntoGenerated * extraIntoGenerated) *
      sourceGeneratedCode 1024 0 * extraIntoGenerated⁻¹ := by group
    _ = _ := by rw [hp, pow_succ, pow_two]; group

/-- The actual cube lies in the genuine local image, using the proved full centralizer. -/
theorem monsterNortonInitialStep_cube_mem_local :
    monsterNortonInitialStep ^ 3 ∈ localIntoGenerated.range := by
  have ha : sourceGeneratedCode 1024 0 ∈ localIntoGenerated.range :=
    ⟨inclQ (sourceQCode 1024 0), rfl⟩
  have hb : sourceGeneratedY 1024 0 ∈ localIntoGenerated.range := by
    rw [← generatedCentralizer_eq_local_range]
    exact sourceGeneratedY_mem_centralizer 1024 0
  rw [monsterNortonInitialStep_cube_word]
  exact localIntoGenerated.range.mul_mem (localIntoGenerated.range.mul_mem ha hb)
    (monsterSourceY_word_mem_local 1024 0)

/-- The actual point-times-triality cubic is identity by the faithful local tensor constituent. -/
theorem monsterNortonInitialStep_cube : monsterNortonInitialStep ^ 3 = 1 := by
  obtain ⟨h, hh⟩ := monsterNortonInitialStep_cube_mem_local
  have hρ : rhoLocal h = (monsterNortonInitialStep ^ 3).val := congrArg Subtype.val hh
  have he : h = 1 := by
    apply monsterLocalTensor_identifies
    intro x
    rw [hρ, map_one]
    exact monsterNortonInitialStep_cube_tensor x
  rw [he, map_one] at hh
  exact hh.symm

/-- The initial point-times-first-line parameter word has cube one in actual G. -/
theorem monsterNortonPoint_zero_first_line_cube :
    (y555NortonPoint 0 * (y555NortonLine monsterSourceTriality 0)⁻¹) ^ 3 = 1 := by
  have hc : y555NortonV * y555NortonPoint 0 = y555NortonPoint 0 * y555NortonV := by
    change qIntoGenerated y555NortonVQ * qIntoGenerated (y555NortonPointQ 0) = _
    rw [← map_mul, monsterNortonVQ_commute_point_zero, map_mul]
    rfl
  have hpoint : y555NortonPoint 0 = sourceGeneratedCode 1024 0 := by
    change qIntoGenerated (y555NortonPointQ 0) = qIntoGenerated (sourceQCode 1024 0)
    rw [monsterNortonPoint_zero_sourceCode]
  rw [y555NortonActualLine_zero]
  have hw : y555NortonPoint 0 *
      (y555NortonV * monsterSourceTriality⁻¹ * y555NortonV⁻¹)⁻¹ =
      y555NortonV * monsterNortonInitialStep * y555NortonV⁻¹ := by
    unfold monsterNortonInitialStep
    rw [← hpoint, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv]
    calc
      _ = (y555NortonPoint 0 * y555NortonV) *
        monsterSourceTriality * y555NortonV⁻¹ := by group
      _ = _ := by rw [← hc]; group
  rw [hw, conj_pow, monsterNortonInitialStep_cube]
  simp

/-- The adjacent initial-point/first-line Coxeter relation holds in the actual wreath. -/
theorem monsterNortonCandidate_point_zero_first_line_cube :
    (y555NortonActualCandidate (y555NortonPointVertex 0) *
      y555NortonActualCandidate (some (0, 0))) ^ 3 = 1 := by
  apply (y555NortonCandidate_coxeter_iff _ _ _ _).mpr
  rw [y555NortonParameter_point]
  exact monsterNortonPoint_zero_first_line_cube

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
