/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact outer monomial values for the sixteen code-eighteen forward-spin coefficient checks. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeEighteenSpinPrefixActual

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The original Gaussian input after the actual outer Q translation and permutation. -/
def monsterNortonCodeEighteenSpinOuterInput (n : Fin 4096) : Fin 4096 :=
  nortonUIntegerLabel ((monsterNortonUCompactPermutation 0).symm
    (golayLabelCoefficients n + spinTranslation monsterNortonUCompactCorrection))

/-- The full outer Q and quadratic signs, including the genuine central phase. -/
def monsterNortonCodeEighteenSpinOuterSign (n : Fin 4096) : ℤ :=
  nortonUIntegerSign (spinPhase monsterNortonUCompactCorrection (golayLabelCoefficients n)) *
    nortonUIntegerSign (monsterMonomialQuadratic (monsterNortonUCompactDiagonal 0)
      (golayLabelCoefficients n + spinTranslation monsterNortonUCompactCorrection))

/-- The complete numerator evaluated by its actual outer factors and Gaussian input. -/
theorem monsterNortonCodeEighteenSpinNumerator_outer (n : Fin 4096) :
    monsterNortonUCompactNumerator monsterNortonCodeEighteenForwardSpinInteger n =
      monsterNortonCodeEighteenSpinOuterSign n *
        nortonUIntegerG monsterNortonCodeEighteenSpinPrefix
          (monsterNortonCodeEighteenSpinOuterInput n) := by
  have hn : monsterNortonUCompactNumerator monsterNortonCodeEighteenForwardSpinInteger =
      nortonUIntegerQ monsterNortonUCompactCorrection
        (monsterNortonUCompactIntegerDiagonal (monsterNortonUCompactDiagonal 0)
          (monsterNortonUCompactIntegerPermutation (monsterNortonUCompactPermutation 0)
            (nortonUIntegerG monsterNortonCodeEighteenSpinPrefix))) := rfl
  rw [hn]
  simp only [nortonUIntegerQ, monsterNortonUCompactIntegerDiagonal,
    monsterNortonUCompactIntegerPermutation, nortonUIntegerLabel_inverse,
    monsterNortonCodeEighteenSpinOuterSign, monsterNortonCodeEighteenSpinOuterInput]
  rw [mul_assoc]

/-- Cached original Gaussian inputs for all sixteen supported output entries. -/
def monsterNortonCodeEighteenSpinOuterInputCache : Fin 16 → Fin 4096 :=
  ![749, 2791, 3136, 1098, 1093, 3151, 2792, 738,
    1095, 3149, 2794, 736, 751, 2789, 3138, 1096]

/-- Cached full outer signs for all sixteen supported output entries. -/
def monsterNortonCodeEighteenSpinOuterSignCache : Fin 16 → ℤ :=
  ![1, -1, -1, 1, 1, -1, -1, 1,
    1, 1, -1, -1, 1, 1, -1, -1]

set_option maxHeartbeats 8000000 in
-- Check each complete actual outer input before evaluating its sixty-four Gaussian terms.
/-- The cached Gaussian inputs are the actual translated and permuted original labels. -/
theorem monsterNortonCodeEighteenSpinOuterInput_actual (i : Fin 16) :
    monsterNortonCodeEighteenSpinOuterInput (monsterNortonCodeEighteenInverseSpinLabel i) =
      monsterNortonCodeEighteenSpinOuterInputCache i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 8000000 in
-- Every outer sign includes both its actual Q phase and diagonal quadratic phase.
/-- The cached signs are exactly the full genuine outer monomial scalars. -/
theorem monsterNortonCodeEighteenSpinOuterSign_actual (i : Fin 16) :
    monsterNortonCodeEighteenSpinOuterSign (monsterNortonCodeEighteenInverseSpinLabel i) =
      monsterNortonCodeEighteenSpinOuterSignCache i := by
  fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
