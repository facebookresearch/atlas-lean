/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact outer monomial values for the four code-ten forward-spin coefficient checks. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTenSpinPrefixActual

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The original Gaussian input after the actual outer Q translation and permutation. -/
def monsterNortonCodeTenSpinOuterInput (n : Fin 4096) : Fin 4096 :=
  nortonUIntegerLabel ((monsterNortonUCompactPermutation 0).symm
    (golayLabelCoefficients n + spinTranslation monsterNortonUCompactCorrection))

/-- The full outer Q and quadratic signs, including the genuine central phase. -/
def monsterNortonCodeTenSpinOuterSign (n : Fin 4096) : ℤ :=
  nortonUIntegerSign (spinPhase monsterNortonUCompactCorrection (golayLabelCoefficients n)) *
    nortonUIntegerSign (monsterMonomialQuadratic (monsterNortonUCompactDiagonal 0)
      (golayLabelCoefficients n + spinTranslation monsterNortonUCompactCorrection))

/-- The complete numerator evaluated by its actual outer factors and Gaussian input. -/
theorem monsterNortonCodeTenSpinNumerator_outer (n : Fin 4096) :
    monsterNortonUCompactNumerator monsterNortonCodeTenForwardSpinInteger n =
      monsterNortonCodeTenSpinOuterSign n *
        nortonUIntegerG monsterNortonCodeTenSpinPrefix
          (monsterNortonCodeTenSpinOuterInput n) := by
  have hn : monsterNortonUCompactNumerator monsterNortonCodeTenForwardSpinInteger =
      nortonUIntegerQ monsterNortonUCompactCorrection
        (monsterNortonUCompactIntegerDiagonal (monsterNortonUCompactDiagonal 0)
          (monsterNortonUCompactIntegerPermutation (monsterNortonUCompactPermutation 0)
            (nortonUIntegerG monsterNortonCodeTenSpinPrefix))) := rfl
  rw [hn]
  simp only [nortonUIntegerQ, monsterNortonUCompactIntegerDiagonal,
    monsterNortonUCompactIntegerPermutation, nortonUIntegerLabel_inverse,
    monsterNortonCodeTenSpinOuterSign, monsterNortonCodeTenSpinOuterInput]
  rw [mul_assoc]

/-- Cached original Gaussian inputs for all four supported output entries. -/
def monsterNortonCodeTenSpinOuterInputCache : Fin 4 → Fin 4096 :=
  ![1037, 2720, 679, 3082]

/-- Cached full outer signs for all four supported output entries. -/
def monsterNortonCodeTenSpinOuterSignCache : Fin 4 → ℤ :=
  ![1, 1, 1, 1]

set_option maxHeartbeats 8000000 in
-- Check each complete actual outer input before evaluating its sixty-four Gaussian terms.
/-- The cached Gaussian inputs are the actual translated and permuted original labels. -/
theorem monsterNortonCodeTenSpinOuterInput_actual (i : Fin 4) :
    monsterNortonCodeTenSpinOuterInput (monsterNortonCodeTenInverseSpinLabel i) =
      monsterNortonCodeTenSpinOuterInputCache i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 8000000 in
-- Every outer sign includes both its actual Q phase and diagonal quadratic phase.
/-- The cached signs are exactly the full genuine outer monomial scalars. -/
theorem monsterNortonCodeTenSpinOuterSign_actual (i : Fin 4) :
    monsterNortonCodeTenSpinOuterSign (monsterNortonCodeTenInverseSpinLabel i) =
      monsterNortonCodeTenSpinOuterSignCache i := by
  fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
