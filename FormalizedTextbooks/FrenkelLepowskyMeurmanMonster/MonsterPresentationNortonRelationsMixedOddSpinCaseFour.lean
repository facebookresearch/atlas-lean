/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Supported actual inverse-spin coefficient certificate for mixed case 4. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsMixedOddOuterCache

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 48000000 in
-- Specialize the 128 source entries before checking each complete 64-term Gaussian sum.
/-- Every supported entry in mixed case 4 is the coefficient of the complete actual spin word. -/
theorem monsterNortonMixedOddSpinNumerator_coefficient_4 (i : Fin 128) :
    monsterNortonMixedOddSpinNumerator 4 (monsterNortonMixedOddSpinLabel 4 i) =
      monsterNortonMixedOddSpinCoefficient 4 i := by
  have hn : monsterNortonMixedOddSpinNumerator (4 : Fin 5) =
      monsterNortonOddInverseSpinNumerator
        (monsterNortonEvenShortFirstUOddCode (monsterNortonMixedOddBasisIndex 4)) := rfl
  have hb : monsterNortonMixedOddBasisIndex (4 : Fin 5) =
      monsterNortonOddPrefixBasisIndex 4 := rfl
  rw [hn, monsterNortonOddInverseSpinNumerator_outer, hb,
    monsterNortonOddInverseSpinPrefix_cache, monsterNortonMixedOddOuterSign_actual,
    monsterNortonMixedOddOuterInput_actual]
  fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
