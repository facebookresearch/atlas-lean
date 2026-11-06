/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact outer monomial values for the four code-twenty-two forward-spin coefficient checks. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyTwoSpinPrefixActual

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The original Gaussian input after the actual outer Q translation and permutation. -/
def monsterNortonCodeTwentyTwoSpinOuterInput (n : Fin 4096) : Fin 4096 :=
  nortonUIntegerLabel ((monsterNortonUCompactPermutation 0).symm
    (golayLabelCoefficients n + spinTranslation monsterNortonUCompactCorrection))

/-- The full outer Q and quadratic signs, including the genuine central phase. -/
def monsterNortonCodeTwentyTwoSpinOuterSign (n : Fin 4096) : ℤ :=
  nortonUIntegerSign (spinPhase monsterNortonUCompactCorrection (golayLabelCoefficients n)) *
    nortonUIntegerSign (monsterMonomialQuadratic (monsterNortonUCompactDiagonal 0)
      (golayLabelCoefficients n + spinTranslation monsterNortonUCompactCorrection))

/-- The complete numerator evaluated by its actual outer factors and Gaussian input. -/
theorem monsterNortonCodeTwentyTwoSpinNumerator_outer (k : Fin 16) (n : Fin 4096) :
    monsterNortonUCompactNumerator (monsterNortonCodeTwentyTwoForwardSpinInteger k) n =
      monsterNortonCodeTwentyTwoSpinOuterSign n *
        nortonUIntegerG (monsterNortonCodeTwentyTwoSpinPrefix k)
          (monsterNortonCodeTwentyTwoSpinOuterInput n) := by
  have hn : monsterNortonUCompactNumerator (monsterNortonCodeTwentyTwoForwardSpinInteger k) =
      nortonUIntegerQ monsterNortonUCompactCorrection
        (monsterNortonUCompactIntegerDiagonal (monsterNortonUCompactDiagonal 0)
          (monsterNortonUCompactIntegerPermutation (monsterNortonUCompactPermutation 0)
            (nortonUIntegerG (monsterNortonCodeTwentyTwoSpinPrefix k)))) := rfl
  rw [hn]
  simp only [nortonUIntegerQ, monsterNortonUCompactIntegerDiagonal,
    monsterNortonUCompactIntegerPermutation, nortonUIntegerLabel_inverse,
    monsterNortonCodeTwentyTwoSpinOuterSign, monsterNortonCodeTwentyTwoSpinOuterInput]
  rw [mul_assoc]

/-- Cached original Gaussian inputs for all four supported output entries. -/
def monsterNortonCodeTwentyTwoSpinOuterInputCache : Fin 16 → Fin 4 → Fin 4096 :=
  ![![8, 3749, 1698, 2063],
    ![14, 3747, 1700, 2057],
    ![1696, 2061, 10, 3751],
    ![1704, 2053, 2, 3759],
    ![3746, 15, 2056, 1701],
    ![3756, 1, 2054, 1707],
    ![1702, 2059, 12, 3745],
    ![1710, 2051, 4, 3753],
    ![3754, 7, 2048, 1709],
    ![3748, 9, 2062, 1699],
    ![6, 3755, 1708, 2049],
    ![0, 3757, 1706, 2055],
    ![2060, 1697, 3750, 11],
    ![2058, 1703, 3744, 13],
    ![2050, 1711, 3752, 5],
    ![2052, 1705, 3758, 3]]

/-- Cached full outer signs for all four supported output entries. -/
def monsterNortonCodeTwentyTwoSpinOuterSignCache : Fin 16 → Fin 4 → ℤ :=
  ![![-1, -1, 1, 1],
    ![1, 1, -1, -1],
    ![-1, -1, 1, 1],
    ![1, -1, -1, 1],
    ![1, -1, 1, -1],
    ![-1, -1, -1, -1],
    ![-1, -1, 1, 1],
    ![1, -1, -1, 1],
    ![1, 1, 1, 1],
    ![-1, 1, -1, 1],
    ![1, -1, -1, 1],
    ![-1, 1, 1, -1],
    ![-1, 1, -1, 1],
    ![-1, 1, -1, 1],
    ![1, 1, 1, 1],
    ![1, 1, 1, 1]]

set_option maxHeartbeats 8000000 in
-- Check each complete actual outer input before evaluating its sixty-four Gaussian terms.
/-- The cached Gaussian inputs are the actual translated and permuted original labels. -/
theorem monsterNortonCodeTwentyTwoSpinOuterInput_actual (k : Fin 16) (i : Fin 4) :
    monsterNortonCodeTwentyTwoSpinOuterInput ((monsterNortonCodeTwentyTwoInverseSpinLabel k) i) =
      (monsterNortonCodeTwentyTwoSpinOuterInputCache k) i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

set_option maxHeartbeats 8000000 in
-- Every outer sign includes both its actual Q phase and diagonal quadratic phase.
/-- The cached signs are exactly the full genuine outer monomial scalars. -/
theorem monsterNortonCodeTwentyTwoSpinOuterSign_actual (k : Fin 16) (i : Fin 4) :
    monsterNortonCodeTwentyTwoSpinOuterSign ((monsterNortonCodeTwentyTwoInverseSpinLabel k) i) =
      (monsterNortonCodeTwentyTwoSpinOuterSignCache k) i := by
  fin_cases k <;> fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
