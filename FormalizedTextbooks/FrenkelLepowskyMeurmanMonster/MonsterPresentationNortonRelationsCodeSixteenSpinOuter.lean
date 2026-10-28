/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact outer monomial values for the sixteen code-sixteen forward-spin coefficient checks. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSixteenSpinPrefixActual

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The original Gaussian input after the actual outer Q translation and permutation. -/
def monsterNortonCodeSixteenSpinOuterInput (n : Fin 4096) : Fin 4096 :=
  nortonUIntegerLabel ((monsterNortonUCompactPermutation 0).symm
    (golayLabelCoefficients n + spinTranslation monsterNortonUCompactCorrection))

/-- The full outer Q and quadratic signs, including the genuine central phase. -/
def monsterNortonCodeSixteenSpinOuterSign (n : Fin 4096) : ℤ :=
  nortonUIntegerSign (spinPhase monsterNortonUCompactCorrection (golayLabelCoefficients n)) *
    nortonUIntegerSign (monsterMonomialQuadratic (monsterNortonUCompactDiagonal 0)
      (golayLabelCoefficients n + spinTranslation monsterNortonUCompactCorrection))

/-- The complete numerator evaluated by its actual outer factors and Gaussian input. -/
theorem monsterNortonCodeSixteenSpinNumerator_outer (n : Fin 4096) :
    monsterNortonUCompactNumerator monsterNortonCodeSixteenForwardSpinInteger n =
      monsterNortonCodeSixteenSpinOuterSign n *
        nortonUIntegerG monsterNortonCodeSixteenSpinPrefix
          (monsterNortonCodeSixteenSpinOuterInput n) := by
  have hn : monsterNortonUCompactNumerator monsterNortonCodeSixteenForwardSpinInteger =
      nortonUIntegerQ monsterNortonUCompactCorrection
        (monsterNortonUCompactIntegerDiagonal (monsterNortonUCompactDiagonal 0)
          (monsterNortonUCompactIntegerPermutation (monsterNortonUCompactPermutation 0)
            (nortonUIntegerG monsterNortonCodeSixteenSpinPrefix))) := rfl
  rw [hn]
  simp only [nortonUIntegerQ, monsterNortonUCompactIntegerDiagonal,
    monsterNortonUCompactIntegerPermutation, nortonUIntegerLabel_inverse,
    monsterNortonCodeSixteenSpinOuterSign, monsterNortonCodeSixteenSpinOuterInput]
  rw [mul_assoc]

/-- Cached original Gaussian inputs for all sixteen supported output entries. -/
def monsterNortonCodeSixteenSpinOuterInputCache : Fin 16 → Fin 4096 :=
  ![2377, 333, 2020, 4064, 4065, 2021, 332, 2376,
    4067, 2023, 334, 2378, 2379, 335, 2022, 4066]

/-- Cached full outer signs for all sixteen supported output entries. -/
def monsterNortonCodeSixteenSpinOuterSignCache : Fin 16 → ℤ :=
  ![-1, 1, 1, 1, -1, 1, 1, 1,
    -1, -1, 1, -1, -1, -1, 1, -1]

set_option maxHeartbeats 8000000 in
-- Check each complete actual outer input before evaluating its sixty-four Gaussian terms.
/-- The cached Gaussian inputs are the actual translated and permuted original labels. -/
theorem monsterNortonCodeSixteenSpinOuterInput_actual (i : Fin 16) :
    monsterNortonCodeSixteenSpinOuterInput (monsterNortonCodeSixteenInverseSpinLabel i) =
      monsterNortonCodeSixteenSpinOuterInputCache i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 8000000 in
-- Every outer sign includes both its actual Q phase and diagonal quadratic phase.
/-- The cached signs are exactly the full genuine outer monomial scalars. -/
theorem monsterNortonCodeSixteenSpinOuterSign_actual (i : Fin 16) :
    monsterNortonCodeSixteenSpinOuterSign (monsterNortonCodeSixteenInverseSpinLabel i) =
      monsterNortonCodeSixteenSpinOuterSignCache i := by
  fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
