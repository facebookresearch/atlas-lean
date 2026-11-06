/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete actual inverse compact image of the first-line tensor column input. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CompactInverseCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CompactInput
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CompactSupportZero

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All coordinates outside the verified inverse-output catalogue vanish in the actual numerator. -/
theorem monsterNortonLine01CompactInverse_zero (k : Fin 16) (n : Fin 4096)
    (hn : ¬ monsterNortonLine01CompactOutputSupport n) :
    monsterNortonUCompactInverseNumerator (monsterNortonLine01CompactInputVector k) n = 0 :=
  monsterNortonLine01CompactInverse_bit_zero k n hn

/-- The output lookup is exactly the entire actual inverse compact numerator. -/
theorem monsterNortonLine01CompactInverse_actual (k : Fin 16) :
    monsterNortonUCompactInverseNumerator (monsterNortonLine01CompactInputVector k) =
      monsterNortonLine01CompactOutputVector k := by
  funext n
  by_cases hn : monsterNortonLine01CompactOutputSupport n
  · change _ = if monsterNortonLine01CompactOutputSupport n then _ else _
    rw [ite_eq_left hn]
    have he : monsterNortonLine01CompactOutputLabel
        (monsterNortonLine01CompactOutputLookup n) = n := hn
    conv_lhs => rw [← he]
    exact monsterNortonLine01CompactInverse_coefficient k
      (monsterNortonLine01CompactOutputLookup n)
  · change _ = if monsterNortonLine01CompactOutputSupport n then _ else _
    rw [ite_eq_right hn]
    exact monsterNortonLine01CompactInverse_zero k n hn

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
