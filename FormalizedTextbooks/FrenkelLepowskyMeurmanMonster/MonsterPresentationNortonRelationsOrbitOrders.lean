/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual squares and cubes for every entry of the checked Norton Q cycle. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOrbitData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOddWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOmegaCube
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The Coxeter exponent attached to each actual normal-form coefficient. -/
def monsterNortonNormalExponent : Fin 13 → ℕ := ![3,3,2,3,2,2,2,2,2,3,2,2,2]

/-- The second cycle coefficient is the initial source code lift. -/
theorem monsterNortonNormalQData_one : monsterNortonNormalQData 1 = sourceQCode 1024 0 := by
  apply NormalizedCocycleExtension.Extension.ext
  all_goals apply Multiplicative.toAdd.injective
  all_goals decide +kernel

/-- The fourth cycle coefficient factors into the actual all-one and low source code lifts. -/
theorem monsterNortonNormalQData_three :
    monsterNortonNormalQData 3 = sourceOmegaQ * sourceQCode 1039 0 := by
  apply NormalizedCocycleExtension.Extension.ext
  all_goals apply Multiplicative.toAdd.injective
  all_goals decide +kernel

/-- The tenth cycle coefficient has the analogous genuine low-code factorization. -/
theorem monsterNortonNormalQData_nine :
    monsterNortonNormalQData 9 = sourceOmegaQ * sourceQCode 1025 0 := by
  apply NormalizedCocycleExtension.Extension.ext
  all_goals apply Multiplicative.toAdd.injective
  all_goals decide +kernel

private theorem generated_source_code (d : Fin 4096) :
    qIntoGenerated (sourceQCode d 0) = sourceGeneratedCode d 0 := rfl

private def oddIndex : Fin 9 → Fin 13 := ![2,4,5,6,7,8,10,11,12]
private def oddLabel : Fin 9 → Fin 4096 := ![2733,2775,2487,2539,2919,2397,2683,2971,3069]

private theorem oddData (k : Fin 9) :
    monsterNortonNormalQData (oddIndex k) = cocodeQ (golayLabelCoefficients (oddLabel k)) := by
  fin_cases k <;> apply NormalizedCocycleExtension.Extension.ext
  all_goals apply Multiplicative.toAdd.injective
  all_goals decide +kernel

set_option maxHeartbeats 1000000 in
-- Normalize the concrete local/triality word coercions for the thirteen finite branches.
/-- Every normal-form entry satisfies its assigned square or cube in actual G. -/
theorem monsterNortonNormalQData_order (i : Fin 13) :
    (qIntoGenerated (monsterNortonNormalQData i) * monsterSourceTriality) ^
      monsterNortonNormalExponent i = 1 := by
  fin_cases i
  · have hz : monsterNortonNormalQData 0 = 1 := by
      apply NormalizedCocycleExtension.Extension.ext
      all_goals apply Multiplicative.toAdd.injective
      all_goals decide +kernel
    change (qIntoGenerated (monsterNortonNormalQData 0) * monsterSourceTriality) ^ 3 = 1
    rw [hz, map_one, one_mul]
    exact monsterSourceTriality_cube
  · change (qIntoGenerated (monsterNortonNormalQData 1) * monsterSourceTriality) ^ 3 = 1
    rw [monsterNortonNormalQData_one]
    exact monsterNortonInitialStep_cube
  · change (qIntoGenerated (monsterNortonNormalQData 2) * monsterSourceTriality) ^ 2 = 1
    rw [show monsterNortonNormalQData 2 = cocodeQ (golayLabelCoefficients 2733) from oddData 0]
    exact monsterNortonOddCocode_triality_square _ (by decide +kernel)
  · change (qIntoGenerated (monsterNortonNormalQData 3) * monsterSourceTriality) ^ 3 = 1
    rw [monsterNortonNormalQData_three, map_mul, mul_assoc]
    rw [generated_source_code]
    have h := monsterNortonOmegaEvenStep_cube 1039 (by decide +kernel)
    rw [monsterNortonEvenStep] at h
    rw [show (⟨(1039 : Fin 2048).val, by omega⟩ : Fin 4096) = 1039 by decide +kernel] at h
    exact h
  · change (qIntoGenerated (monsterNortonNormalQData 4) * monsterSourceTriality) ^ 2 = 1
    rw [show monsterNortonNormalQData 4 = cocodeQ (golayLabelCoefficients 2775) from oddData 1]
    exact monsterNortonOddCocode_triality_square _ (by decide +kernel)
  · change (qIntoGenerated (monsterNortonNormalQData 5) * monsterSourceTriality) ^ 2 = 1
    rw [show monsterNortonNormalQData 5 = cocodeQ (golayLabelCoefficients 2487) from oddData 2]
    exact monsterNortonOddCocode_triality_square _ (by decide +kernel)
  · change (qIntoGenerated (monsterNortonNormalQData 6) * monsterSourceTriality) ^ 2 = 1
    rw [show monsterNortonNormalQData 6 = cocodeQ (golayLabelCoefficients 2539) from oddData 3]
    exact monsterNortonOddCocode_triality_square _ (by decide +kernel)
  · change (qIntoGenerated (monsterNortonNormalQData 7) * monsterSourceTriality) ^ 2 = 1
    rw [show monsterNortonNormalQData 7 = cocodeQ (golayLabelCoefficients 2919) from oddData 4]
    exact monsterNortonOddCocode_triality_square _ (by decide +kernel)
  · change (qIntoGenerated (monsterNortonNormalQData 8) * monsterSourceTriality) ^ 2 = 1
    rw [show monsterNortonNormalQData 8 = cocodeQ (golayLabelCoefficients 2397) from oddData 5]
    exact monsterNortonOddCocode_triality_square _ (by decide +kernel)
  · change (qIntoGenerated (monsterNortonNormalQData 9) * monsterSourceTriality) ^ 3 = 1
    rw [monsterNortonNormalQData_nine, map_mul, mul_assoc]
    rw [generated_source_code]
    have h := monsterNortonOmegaEvenStep_cube 1025 (by decide +kernel)
    rw [monsterNortonEvenStep] at h
    rw [show (⟨(1025 : Fin 2048).val, by omega⟩ : Fin 4096) = 1025 by decide +kernel] at h
    exact h
  · change (qIntoGenerated (monsterNortonNormalQData 10) * monsterSourceTriality) ^ 2 = 1
    rw [show monsterNortonNormalQData 10 = cocodeQ (golayLabelCoefficients 2683) from oddData 6]
    exact monsterNortonOddCocode_triality_square _ (by decide +kernel)
  · change (qIntoGenerated (monsterNortonNormalQData 11) * monsterSourceTriality) ^ 2 = 1
    rw [show monsterNortonNormalQData 11 = cocodeQ (golayLabelCoefficients 2971) from oddData 7]
    exact monsterNortonOddCocode_triality_square _ (by decide +kernel)
  · change (qIntoGenerated (monsterNortonNormalQData 12) * monsterSourceTriality) ^ 2 = 1
    rw [show monsterNortonNormalQData 12 = cocodeQ (golayLabelCoefficients 3069) from oddData 8]
    exact monsterNortonOddCocode_triality_square _ (by decide +kernel)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
