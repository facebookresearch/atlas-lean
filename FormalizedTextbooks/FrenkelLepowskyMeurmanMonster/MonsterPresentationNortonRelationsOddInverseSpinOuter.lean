/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact outer monomial evaluation of the actual inverse odd-spin numerator. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOddInverseSpinPrefixActual

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The genuine Gaussian input after the post-V and outer binary permutation. -/
def monsterNortonOddInverseSpinOuterInput (n : Fin 4096) : Fin 4096 :=
  nortonUIntegerLabel (monsterNortonUCompactPermutation 1
    (golayLabelCoefficients n + spinTranslation y555NortonVQ))

/-- The exact post-V and outer diagonal scalar, retaining the full central phase. -/
def monsterNortonOddInverseSpinOuterSign (n : Fin 4096) : ℤ :=
  nortonUIntegerSign (spinPhase y555NortonVQ (golayLabelCoefficients n)) *
    nortonUIntegerSign (monsterMonomialQuadratic (monsterNortonUCompactDiagonal 1)
      (golayLabelCoefficients n + spinTranslation y555NortonVQ))

/-- Outer monomial factors are evaluated once before the complete actual Gaussian sum. -/
theorem monsterNortonOddInverseSpinNumerator_outer (d : Fin 2048) (n : Fin 4096) :
    monsterNortonOddInverseSpinNumerator d n =
      monsterNortonOddInverseSpinOuterSign n *
        nortonUIntegerG (monsterNortonOddInverseSpinPrefix d)
          (monsterNortonOddInverseSpinOuterInput n) := by
  rw [monsterNortonOddInverseSpinNumerator_prefix]
  simp only [nortonUIntegerQ, monsterNortonUCompactIntegerDiagonal,
    monsterNortonUCompactIntegerPermutation, nortonUIntegerLabel_inverse,
    LinearEquiv.symm_symm, monsterNortonOddInverseSpinOuterSign,
    monsterNortonOddInverseSpinOuterInput]
  rw [mul_assoc]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
