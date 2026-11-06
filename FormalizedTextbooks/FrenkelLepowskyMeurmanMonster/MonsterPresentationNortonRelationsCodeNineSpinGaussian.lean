/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Sixteen complete actual Gaussian coefficients identify the code-nine spin transport. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeNineSpinOuter

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 16000000 in
-- Each output checks the whole sixty-four-term Gaussian on the proved full input table.
/-- The complete actual integer numerator has all sixteen required signed output coefficients. -/
theorem monsterNortonCodeNineSpinNumerator_coefficient (i : Fin 16) :
    monsterNortonUCompactNumerator monsterNortonCodeNineForwardSpinInteger
      (monsterNortonCodeNineInverseSpinLabel i) =
        -8 * monsterNortonCodeNineInverseSpinCoefficient i := by
  rw [monsterNortonCodeNineSpinNumerator_outer, monsterNortonCodeNineSpinPrefix_dense,
    monsterNortonCodeNineSpinOuterSign_actual, monsterNortonCodeNineSpinOuterInput_actual]
  fin_cases i <;> decide +kernel

/-- The actual Norton spin operator transports the whole forward factor to the inverse factor. -/
theorem monsterNortonCodeNineSpin_transport :
    monsterNortonUFiber.val.1.val (nortonUIntegerEmbed monsterNortonCodeNineForwardSpinInteger) =
      nortonUIntegerEmbed monsterNortonCodeNineInverseSpinInteger := by
  apply monsterNortonCodeNineSpin_transport_of_coefficients
  intro i
  rw [monsterNortonUCompactSpin_actual_embed]
  simp only [Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed,
    nortonUIntegerLabel_coeff, monsterNortonCodeNineSpinNumerator_coefficient, Int.cast_mul,
    Int.cast_neg, Int.cast_ofNat]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
