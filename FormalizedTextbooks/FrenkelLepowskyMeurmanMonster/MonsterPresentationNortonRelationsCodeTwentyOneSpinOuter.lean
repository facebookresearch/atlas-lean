/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact outer monomial values for the twentyone code-twentyone forward-spin coefficient checks. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyOneSpinPrefixActual

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The original Gaussian input after the actual outer Q translation and permutation. -/
def monsterNortonCodeTwentyOneSpinOuterInput (n : Fin 4096) : Fin 4096 :=
  nortonUIntegerLabel ((monsterNortonUCompactPermutation 0).symm
    (golayLabelCoefficients n + spinTranslation monsterNortonUCompactCorrection))

/-- The full outer Q and quadratic signs, including the genuine central phase. -/
def monsterNortonCodeTwentyOneSpinOuterSign (n : Fin 4096) : ℤ :=
  nortonUIntegerSign (spinPhase monsterNortonUCompactCorrection (golayLabelCoefficients n)) *
    nortonUIntegerSign (monsterMonomialQuadratic (monsterNortonUCompactDiagonal 0)
      (golayLabelCoefficients n + spinTranslation monsterNortonUCompactCorrection))

/-- The complete numerator evaluated by its actual outer factors and Gaussian input. -/
theorem monsterNortonCodeTwentyOneSpinNumerator_outer (n : Fin 4096) :
    monsterNortonUCompactNumerator monsterNortonCodeTwentyOneForwardSpinInteger n =
      monsterNortonCodeTwentyOneSpinOuterSign n *
        nortonUIntegerG monsterNortonCodeTwentyOneSpinPrefix
          (monsterNortonCodeTwentyOneSpinOuterInput n) := by
  have hn : monsterNortonUCompactNumerator monsterNortonCodeTwentyOneForwardSpinInteger =
      nortonUIntegerQ monsterNortonUCompactCorrection
        (monsterNortonUCompactIntegerDiagonal (monsterNortonUCompactDiagonal 0)
          (monsterNortonUCompactIntegerPermutation (monsterNortonUCompactPermutation 0)
            (nortonUIntegerG monsterNortonCodeTwentyOneSpinPrefix))) := rfl
  rw [hn]
  simp only [nortonUIntegerQ, monsterNortonUCompactIntegerDiagonal,
    monsterNortonUCompactIntegerPermutation, nortonUIntegerLabel_inverse,
    monsterNortonCodeTwentyOneSpinOuterSign, monsterNortonCodeTwentyOneSpinOuterInput]
  rw [mul_assoc]

/-- Cached original Gaussian inputs for all twentyone supported output entries. -/
def monsterNortonCodeTwentyOneSpinOuterInputCache : Fin 16 → Fin 4096 :=
  ![2220, 2210, 1537, 1551, 3586, 3596, 175, 161,
    3590, 3592, 171, 165, 2216, 2214, 1541, 1547]

/-- Cached full outer signs for all twentyone supported output entries. -/
def monsterNortonCodeTwentyOneSpinOuterSignCache : Fin 16 → ℤ :=
  ![1, -1, -1, -1, -1, 1, 1, 1,
    1, -1, -1, -1, -1, 1, 1, 1]

set_option maxHeartbeats 8000000 in
-- Check each complete actual outer input before evaluating its sixty-four Gaussian terms.
/-- The cached Gaussian inputs are the actual translated and permuted original labels. -/
theorem monsterNortonCodeTwentyOneSpinOuterInput_actual (i : Fin 16) :
    monsterNortonCodeTwentyOneSpinOuterInput (monsterNortonCodeTwentyOneInverseSpinLabel i) =
      monsterNortonCodeTwentyOneSpinOuterInputCache i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 8000000 in
-- Every outer sign includes both its actual Q phase and diagonal quadratic phase.
/-- The cached signs are exactly the full genuine outer monomial scalars. -/
theorem monsterNortonCodeTwentyOneSpinOuterSign_actual (i : Fin 16) :
    monsterNortonCodeTwentyOneSpinOuterSign (monsterNortonCodeTwentyOneInverseSpinLabel i) =
      monsterNortonCodeTwentyOneSpinOuterSignCache i := by
  fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
