/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Four complete actual Gaussian coefficients identify the code-twenty-two spin transport. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyTwoSpinOuter

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 16000000 in
-- Each output checks the whole sixty-four-term Gaussian on the proved full input table.
/-- The complete actual integer numerator has all four required signed output coefficients. -/
theorem monsterNortonCodeTwentyTwoSpinNumerator_coefficient (k : Fin 16) (i : Fin 4) :
    monsterNortonUCompactNumerator (monsterNortonCodeTwentyTwoForwardSpinInteger k)
      ((monsterNortonCodeTwentyTwoInverseSpinLabel k) i) =
        -8 * (monsterNortonCodeTwentyTwoInverseTensorTable k) i := by
  rw [(monsterNortonCodeTwentyTwoSpinNumerator_outer k),
    (monsterNortonCodeTwentyTwoSpinPrefix_dense k),
    (monsterNortonCodeTwentyTwoSpinOuterSign_actual k),
      (monsterNortonCodeTwentyTwoSpinOuterInput_actual k)]
  fin_cases k <;> fin_cases i <;> decide +kernel

/-- The actual Norton spin operator transports the whole forward factor to the inverse factor. -/
theorem monsterNortonCodeTwentyTwoSpin_transport (k : Fin 16) :
    monsterNortonUFiber.val.1.val (nortonUIntegerEmbed
      (monsterNortonCodeTwentyTwoForwardSpinInteger k)) =
      nortonUIntegerEmbed (monsterNortonCodeTwentyTwoInverseSpinInteger k) := by
  apply (monsterNortonCodeTwentyTwoSpin_transport_of_coefficients k)
  intro i
  rw [monsterNortonUCompactSpin_actual_embed]
  simp only [Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed,
    nortonUIntegerLabel_coeff, (monsterNortonCodeTwentyTwoSpinNumerator_coefficient k),
      Int.cast_mul,
    Int.cast_neg, Int.cast_ofNat]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
