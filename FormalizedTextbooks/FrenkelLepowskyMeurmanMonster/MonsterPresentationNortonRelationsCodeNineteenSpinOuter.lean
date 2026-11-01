/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact outer monomial values for the nineteen code-nineteen forward-spin coefficient checks. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineteenSpinPrefixActual

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The original Gaussian input after the actual outer Q translation and permutation. -/
def monsterNortonCodeNineteenSpinOuterInput (n : Fin 4096) : Fin 4096 :=
  nortonUIntegerLabel ((monsterNortonUCompactPermutation 0).symm
    (golayLabelCoefficients n + spinTranslation monsterNortonUCompactCorrection))

/-- The full outer Q and quadratic signs, including the genuine central phase. -/
def monsterNortonCodeNineteenSpinOuterSign (n : Fin 4096) : ℤ :=
  nortonUIntegerSign (spinPhase monsterNortonUCompactCorrection (golayLabelCoefficients n)) *
    nortonUIntegerSign (monsterMonomialQuadratic (monsterNortonUCompactDiagonal 0)
      (golayLabelCoefficients n + spinTranslation monsterNortonUCompactCorrection))

/-- The complete numerator evaluated by its actual outer factors and Gaussian input. -/
theorem monsterNortonCodeNineteenSpinNumerator_outer (n : Fin 4096) :
    monsterNortonUCompactNumerator monsterNortonCodeNineteenForwardSpinInteger n =
      monsterNortonCodeNineteenSpinOuterSign n *
        nortonUIntegerG monsterNortonCodeNineteenSpinPrefix
          (monsterNortonCodeNineteenSpinOuterInput n) := by
  have hn : monsterNortonUCompactNumerator monsterNortonCodeNineteenForwardSpinInteger =
      nortonUIntegerQ monsterNortonUCompactCorrection
        (monsterNortonUCompactIntegerDiagonal (monsterNortonUCompactDiagonal 0)
          (monsterNortonUCompactIntegerPermutation (monsterNortonUCompactPermutation 0)
            (nortonUIntegerG monsterNortonCodeNineteenSpinPrefix))) := rfl
  rw [hn]
  simp only [nortonUIntegerQ, monsterNortonUCompactIntegerDiagonal,
    monsterNortonUCompactIntegerPermutation, nortonUIntegerLabel_inverse,
    monsterNortonCodeNineteenSpinOuterSign, monsterNortonCodeNineteenSpinOuterInput]
  rw [mul_assoc]

/-- Cached original Gaussian inputs for all nineteen supported output entries. -/
def monsterNortonCodeNineteenSpinOuterInputCache : Fin 16 → Fin 4096 :=
  ![2592, 554, 1165, 3207, 3214, 1156, 547, 2601,
    3210, 1152, 551, 2605, 2596, 558, 1161, 3203]

/-- Cached full outer signs for all nineteen supported output entries. -/
def monsterNortonCodeNineteenSpinOuterSignCache : Fin 16 → ℤ :=
  ![-1, -1, 1, 1, 1, -1, -1, 1,
    1, -1, -1, 1, -1, -1, 1, 1]

set_option maxHeartbeats 8000000 in
-- Check each complete actual outer input before evaluating its sixty-four Gaussian terms.
/-- The cached Gaussian inputs are the actual translated and permuted original labels. -/
theorem monsterNortonCodeNineteenSpinOuterInput_actual (i : Fin 16) :
    monsterNortonCodeNineteenSpinOuterInput (monsterNortonCodeNineteenInverseSpinLabel i) =
      monsterNortonCodeNineteenSpinOuterInputCache i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 8000000 in
-- Every outer sign includes both its actual Q phase and diagonal quadratic phase.
/-- The cached signs are exactly the full genuine outer monomial scalars. -/
theorem monsterNortonCodeNineteenSpinOuterSign_actual (i : Fin 16) :
    monsterNortonCodeNineteenSpinOuterSign (monsterNortonCodeNineteenInverseSpinLabel i) =
      monsterNortonCodeNineteenSpinOuterSignCache i := by
  fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
