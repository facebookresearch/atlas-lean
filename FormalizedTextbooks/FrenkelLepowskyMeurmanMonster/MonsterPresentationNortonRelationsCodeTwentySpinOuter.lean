/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact outer monomial values for the twenty code-twenty forward-spin coefficient checks. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentySpinPrefixActual

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The original Gaussian input after the actual outer Q translation and permutation. -/
def monsterNortonCodeTwentySpinOuterInput (n : Fin 4096) : Fin 4096 :=
  nortonUIntegerLabel ((monsterNortonUCompactPermutation 0).symm
    (golayLabelCoefficients n + spinTranslation monsterNortonUCompactCorrection))

/-- The full outer Q and quadratic signs, including the genuine central phase. -/
def monsterNortonCodeTwentySpinOuterSign (n : Fin 4096) : ℤ :=
  nortonUIntegerSign (spinPhase monsterNortonUCompactCorrection (golayLabelCoefficients n)) *
    nortonUIntegerSign (monsterMonomialQuadratic (monsterNortonUCompactDiagonal 0)
      (golayLabelCoefficients n + spinTranslation monsterNortonUCompactCorrection))

/-- The complete numerator evaluated by its actual outer factors and Gaussian input. -/
theorem monsterNortonCodeTwentySpinNumerator_outer (n : Fin 4096) :
    monsterNortonUCompactNumerator monsterNortonCodeTwentyForwardSpinInteger n =
      monsterNortonCodeTwentySpinOuterSign n *
        nortonUIntegerG monsterNortonCodeTwentySpinPrefix
          (monsterNortonCodeTwentySpinOuterInput n) := by
  have hn : monsterNortonUCompactNumerator monsterNortonCodeTwentyForwardSpinInteger =
      nortonUIntegerQ monsterNortonUCompactCorrection
        (monsterNortonUCompactIntegerDiagonal (monsterNortonUCompactDiagonal 0)
          (monsterNortonUCompactIntegerPermutation (monsterNortonUCompactPermutation 0)
            (nortonUIntegerG monsterNortonCodeTwentySpinPrefix))) := rfl
  rw [hn]
  simp only [nortonUIntegerQ, monsterNortonUCompactIntegerDiagonal,
    monsterNortonUCompactIntegerPermutation, nortonUIntegerLabel_inverse,
    monsterNortonCodeTwentySpinOuterSign, monsterNortonCodeTwentySpinOuterInput]
  rw [mul_assoc]

/-- Cached original Gaussian inputs for all twenty supported output entries. -/
def monsterNortonCodeTwentySpinOuterInputCache : Fin 16 → Fin 4096 :=
  ![4001, 4015, 268, 258, 2313, 2311, 1956, 1962,
    2315, 2309, 1958, 1960, 4003, 4013, 270, 256]

/-- Cached full outer signs for all twenty supported output entries. -/
def monsterNortonCodeTwentySpinOuterSignCache : Fin 16 → ℤ :=
  ![-1, -1, 1, -1, -1, -1, 1, -1,
    -1, -1, 1, -1, -1, -1, 1, -1]

set_option maxHeartbeats 8000000 in
-- Check each complete actual outer input before evaluating its sixty-four Gaussian terms.
/-- The cached Gaussian inputs are the actual translated and permuted original labels. -/
theorem monsterNortonCodeTwentySpinOuterInput_actual (i : Fin 16) :
    monsterNortonCodeTwentySpinOuterInput (monsterNortonCodeTwentyInverseSpinLabel i) =
      monsterNortonCodeTwentySpinOuterInputCache i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 8000000 in
-- Every outer sign includes both its actual Q phase and diagonal quadratic phase.
/-- The cached signs are exactly the full genuine outer monomial scalars. -/
theorem monsterNortonCodeTwentySpinOuterSign_actual (i : Fin 16) :
    monsterNortonCodeTwentySpinOuterSign (monsterNortonCodeTwentyInverseSpinLabel i) =
      monsterNortonCodeTwentySpinOuterSignCache i := by
  fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
