/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Sixteen complete actual Gaussian coefficients identify the code-five spin transport. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeFiveSpinOuter

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 16000000 in
-- Each output checks the whole sixty-four-term Gaussian on the proved full input table.
/-- The complete actual integer numerator has all sixteen required signed output coefficients. -/
theorem monsterNortonCodeFiveSpinNumerator_coefficient (i : Fin 16) :
    monsterNortonUCompactNumerator monsterNortonCodeFiveForwardSpinInteger
      (monsterNortonCodeFiveInverseSpinLabel i) =
        -8 * monsterNortonCodeFiveInverseSpinCoefficient i := by
  rw [monsterNortonCodeFiveSpinNumerator_outer, monsterNortonCodeFiveSpinPrefix_dense,
    monsterNortonCodeFiveSpinOuterSign_actual, monsterNortonCodeFiveSpinOuterInput_actual]
  fin_cases i <;> decide +kernel

/-- The actual Norton spin operator transports the whole forward factor to the inverse factor. -/
theorem monsterNortonCodeFiveSpin_transport :
    monsterNortonUFiber.val.1.val (nortonUIntegerEmbed monsterNortonCodeFiveForwardSpinInteger) =
      nortonUIntegerEmbed monsterNortonCodeFiveInverseSpinInteger := by
  apply monsterNortonCodeFiveSpin_transport_of_coefficients
  intro i
  rw [monsterNortonUCompactSpin_actual_embed]
  simp only [Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed,
    nortonUIntegerLabel_coeff, monsterNortonCodeFiveSpinNumerator_coefficient, Int.cast_mul,
    Int.cast_neg, Int.cast_ofNat]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
