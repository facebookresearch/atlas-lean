/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Four complete actual Gaussian coefficients identify the preferred-basis-ten spin transport. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTenSpinOuter

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 16000000 in
-- Each output checks the whole sixty-four-term Gaussian on the proved full input table.
/-- The complete actual integer numerator has all four required signed output coefficients. -/
theorem monsterNortonCodeTenSpinNumerator_coefficient (i : Fin 4) :
    monsterNortonUCompactNumerator monsterNortonCodeTenForwardSpinInteger
      (monsterNortonCodeTenInverseSpinLabel i) =
        -8 * monsterNortonCodeTenInverseSpinCoefficient i := by
  rw [monsterNortonCodeTenSpinNumerator_outer, monsterNortonCodeTenSpinPrefix_dense,
    monsterNortonCodeTenSpinOuterSign_actual, monsterNortonCodeTenSpinOuterInput_actual]
  fin_cases i <;> decide +kernel

/-- The actual Norton spin operator transports the whole forward factor to the inverse factor. -/
theorem monsterNortonCodeTenSpin_transport :
    monsterNortonUFiber.val.1.val (nortonUIntegerEmbed monsterNortonCodeTenForwardSpinInteger) =
      nortonUIntegerEmbed monsterNortonCodeTenInverseSpinInteger := by
  apply monsterNortonCodeTenSpin_transport_of_coefficients
  intro i
  rw [monsterNortonUCompactSpin_actual_embed]
  simp only [Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed,
    nortonUIntegerLabel_coeff, monsterNortonCodeTenSpinNumerator_coefficient, Int.cast_mul,
    Int.cast_neg, Int.cast_ofNat]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
