/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact outer monomial values for the sixteen code-nine forward-spin coefficient checks. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineSpinPrefixActual

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The original Gaussian input after the actual outer Q translation and permutation. -/
def monsterNortonCodeNineSpinOuterInput (n : Fin 4096) : Fin 4096 :=
  nortonUIntegerLabel ((monsterNortonUCompactPermutation 0).symm
    (golayLabelCoefficients n + spinTranslation monsterNortonUCompactCorrection))

/-- The full outer Q and quadratic signs, including the genuine central phase. -/
def monsterNortonCodeNineSpinOuterSign (n : Fin 4096) : ℤ :=
  nortonUIntegerSign (spinPhase monsterNortonUCompactCorrection (golayLabelCoefficients n)) *
    nortonUIntegerSign (monsterMonomialQuadratic (monsterNortonUCompactDiagonal 0)
      (golayLabelCoefficients n + spinTranslation monsterNortonUCompactCorrection))

/-- The complete numerator evaluated by its actual outer factors and Gaussian input. -/
theorem monsterNortonCodeNineSpinNumerator_outer (n : Fin 4096) :
    monsterNortonUCompactNumerator monsterNortonCodeNineForwardSpinInteger n =
      monsterNortonCodeNineSpinOuterSign n *
        nortonUIntegerG monsterNortonCodeNineSpinPrefix
          (monsterNortonCodeNineSpinOuterInput n) := by
  have hn : monsterNortonUCompactNumerator monsterNortonCodeNineForwardSpinInteger =
      nortonUIntegerQ monsterNortonUCompactCorrection
        (monsterNortonUCompactIntegerDiagonal (monsterNortonUCompactDiagonal 0)
          (monsterNortonUCompactIntegerPermutation (monsterNortonUCompactPermutation 0)
            (nortonUIntegerG monsterNortonCodeNineSpinPrefix))) := rfl
  rw [hn]
  simp only [nortonUIntegerQ, monsterNortonUCompactIntegerDiagonal,
    monsterNortonUCompactIntegerPermutation, nortonUIntegerLabel_inverse,
    monsterNortonCodeNineSpinOuterSign, monsterNortonCodeNineSpinOuterInput]
  rw [mul_assoc]

/-- Cached original Gaussian inputs for all sixteen supported output entries. -/
def monsterNortonCodeNineSpinOuterInputCache : Fin 16 → Fin 4096 :=
  ![1719, 1713, 2074, 2076, 31, 25, 3762, 3764,
    29, 27, 3760, 3766, 1717, 1715, 2072, 2078]

/-- Cached full outer signs for all sixteen supported output entries. -/
def monsterNortonCodeNineSpinOuterSignCache : Fin 16 → ℤ :=
  ![-1, -1, 1, 1, 1, -1, -1, 1,
    -1, -1, 1, 1, 1, -1, -1, 1]

set_option maxHeartbeats 8000000 in
-- Check each complete actual outer input before evaluating its sixty-four Gaussian terms.
/-- The cached Gaussian inputs are the actual translated and permuted original labels. -/
theorem monsterNortonCodeNineSpinOuterInput_actual (i : Fin 16) :
    monsterNortonCodeNineSpinOuterInput (monsterNortonCodeNineInverseSpinLabel i) =
      monsterNortonCodeNineSpinOuterInputCache i := by
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 8000000 in
-- Every outer sign includes both its actual Q phase and diagonal quadratic phase.
/-- The cached signs are exactly the full genuine outer monomial scalars. -/
theorem monsterNortonCodeNineSpinOuterSign_actual (i : Fin 16) :
    monsterNortonCodeNineSpinOuterSign (monsterNortonCodeNineInverseSpinLabel i) =
      monsterNortonCodeNineSpinOuterSignCache i := by
  fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
