/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact outer monomial values for the sixteen code-seven forward-spin coefficient checks. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSevenSpinPrefixActual

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The original Gaussian input after the actual outer Q translation and permutation. -/
def monsterNortonCodeSevenSpinOuterInput (n : Fin 4096) : Fin 4096 :=
  nortonUIntegerLabel ((monsterNortonUCompactPermutation 0).symm
    (golayLabelCoefficients n + spinTranslation monsterNortonUCompactCorrection))

/-- The full outer Q and quadratic signs, including the genuine central phase. -/
def monsterNortonCodeSevenSpinOuterSign (n : Fin 4096) : ℤ :=
  nortonUIntegerSign (spinPhase monsterNortonUCompactCorrection (golayLabelCoefficients n)) *
    nortonUIntegerSign (monsterMonomialQuadratic (monsterNortonUCompactDiagonal 0)
      (golayLabelCoefficients n + spinTranslation monsterNortonUCompactCorrection))

/-- The complete numerator evaluated by its actual outer factors and Gaussian input. -/
theorem monsterNortonCodeSevenSpinNumerator_outer (n : Fin 4096) :
    monsterNortonUCompactNumerator monsterNortonCodeSevenForwardSpinInteger n =
      monsterNortonCodeSevenSpinOuterSign n *
        nortonUIntegerG monsterNortonCodeSevenSpinPrefix
          (monsterNortonCodeSevenSpinOuterInput n) := by
  have hn : monsterNortonUCompactNumerator monsterNortonCodeSevenForwardSpinInteger =
      nortonUIntegerQ monsterNortonUCompactCorrection
        (monsterNortonUCompactIntegerDiagonal (monsterNortonUCompactDiagonal 0)
          (monsterNortonUCompactIntegerPermutation (monsterNortonUCompactPermutation 0)
            (nortonUIntegerG monsterNortonCodeSevenSpinPrefix))) := rfl
  rw [hn]
  simp only [nortonUIntegerQ, monsterNortonUCompactIntegerDiagonal,
    monsterNortonUCompactIntegerPermutation, nortonUIntegerLabel_inverse,
    monsterNortonCodeSevenSpinOuterSign, monsterNortonCodeSevenSpinOuterInput]
  rw [mul_assoc]

/-- Cached original Gaussian inputs for all sixteen supported output entries. -/
def monsterNortonCodeSevenSpinOuterInputCache : Fin 16 → Fin 4096 :=
  ![1727, 1721, 2066, 2068, 23, 17, 3770, 3772,
    21, 19, 3768, 3774, 1725, 1723, 2064, 2070]

/-- Cached full outer signs for all sixteen supported output entries. -/
def monsterNortonCodeSevenSpinOuterSignCache : Fin 16 → ℤ :=
  ![-1, -1, -1, -1, -1, 1, -1, 1,
    -1, -1, -1, -1, -1, 1, -1, 1]

set_option maxHeartbeats 8000000 in
-- Check each complete actual outer input before evaluating its sixty-four Gaussian terms.
/-- The cached Gaussian inputs are the actual translated and permuted original labels. -/
theorem monsterNortonCodeSevenSpinOuterInput_actual (i : Fin 16) :
    monsterNortonCodeSevenSpinOuterInput (monsterNortonCodeSevenInverseSpinLabel i) =
      monsterNortonCodeSevenSpinOuterInputCache i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 8000000 in
-- Every outer sign includes both its actual Q phase and diagonal quadratic phase.
/-- The cached signs are exactly the full genuine outer monomial scalars. -/
theorem monsterNortonCodeSevenSpinOuterSign_actual (i : Fin 16) :
    monsterNortonCodeSevenSpinOuterSign (monsterNortonCodeSevenInverseSpinLabel i) =
      monsterNortonCodeSevenSpinOuterSignCache i := by
  fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
