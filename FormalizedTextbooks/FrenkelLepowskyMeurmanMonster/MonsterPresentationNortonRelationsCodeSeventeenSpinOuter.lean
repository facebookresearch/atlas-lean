/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact outer monomial values for the seventeen code-seventeen forward-spin coefficient checks. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSeventeenSpinPrefixActual

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The original Gaussian input after the actual outer Q translation and permutation. -/
def monsterNortonCodeSeventeenSpinOuterInput (n : Fin 4096) : Fin 4096 :=
  nortonUIntegerLabel ((monsterNortonUCompactPermutation 0).symm
    (golayLabelCoefficients n + spinTranslation monsterNortonUCompactCorrection))

/-- The full outer Q and quadratic signs, including the genuine central phase. -/
def monsterNortonCodeSeventeenSpinOuterSign (n : Fin 4096) : ℤ :=
  nortonUIntegerSign (spinPhase monsterNortonUCompactCorrection (golayLabelCoefficients n)) *
    nortonUIntegerSign (monsterMonomialQuadratic (monsterNortonUCompactDiagonal 0)
      (golayLabelCoefficients n + spinTranslation monsterNortonUCompactCorrection))

/-- The complete numerator evaluated by its actual outer factors and Gaussian input. -/
theorem monsterNortonCodeSeventeenSpinNumerator_outer (n : Fin 4096) :
    monsterNortonUCompactNumerator monsterNortonCodeSeventeenForwardSpinInteger n =
      monsterNortonCodeSeventeenSpinOuterSign n *
        nortonUIntegerG monsterNortonCodeSeventeenSpinPrefix
          (monsterNortonCodeSeventeenSpinOuterInput n) := by
  have hn : monsterNortonUCompactNumerator monsterNortonCodeSeventeenForwardSpinInteger =
      nortonUIntegerQ monsterNortonUCompactCorrection
        (monsterNortonUCompactIntegerDiagonal (monsterNortonUCompactDiagonal 0)
          (monsterNortonUCompactIntegerPermutation (monsterNortonUCompactPermutation 0)
            (nortonUIntegerG monsterNortonCodeSeventeenSpinPrefix))) := rfl
  rw [hn]
  simp only [nortonUIntegerQ, monsterNortonUCompactIntegerDiagonal,
    monsterNortonUCompactIntegerPermutation, nortonUIntegerLabel_inverse,
    monsterNortonCodeSeventeenSpinOuterSign, monsterNortonCodeSeventeenSpinOuterInput]
  rw [mul_assoc]

/-- Cached original Gaussian inputs for all seventeen supported output entries. -/
def monsterNortonCodeSeventeenSpinOuterInputCache : Fin 16 → Fin 4096 :=
  ![1673, 3725, 2084, 32, 39, 2083, 3722, 1678,
    35, 2087, 3726, 1674, 1677, 3721, 2080, 36]

/-- Cached full outer signs for all seventeen supported output entries. -/
def monsterNortonCodeSeventeenSpinOuterSignCache : Fin 16 → ℤ :=
  ![-1, -1, 1, -1, 1, -1, -1, -1,
    1, -1, -1, -1, -1, -1, 1, -1]

set_option maxHeartbeats 8000000 in
-- Check each complete actual outer input before evaluating its sixty-four Gaussian terms.
/-- The cached Gaussian inputs are the actual translated and permuted original labels. -/
theorem monsterNortonCodeSeventeenSpinOuterInput_actual (i : Fin 16) :
    monsterNortonCodeSeventeenSpinOuterInput (monsterNortonCodeSeventeenInverseSpinLabel i) =
      monsterNortonCodeSeventeenSpinOuterInputCache i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 8000000 in
-- Every outer sign includes both its actual Q phase and diagonal quadratic phase.
/-- The cached signs are exactly the full genuine outer monomial scalars. -/
theorem monsterNortonCodeSeventeenSpinOuterSign_actual (i : Fin 16) :
    monsterNortonCodeSeventeenSpinOuterSign (monsterNortonCodeSeventeenInverseSpinLabel i) =
      monsterNortonCodeSeventeenSpinOuterSignCache i := by
  fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
