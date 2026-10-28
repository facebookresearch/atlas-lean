/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Kernel-checked physical U transport of every distinct short input in twelve sparse packets. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortPairHalfUPoolCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 128000000 in
-- Check every one of the 37248 original integer physical coordinate equations.
/-- The displayed signed output is exactly the genuine integer physical U image. -/
theorem monsterNortonPairHalfUPoolPhysical_certificate (i : Fin 1552) (j : Fin 24) :
    (monsterNortonUNumerator1 *ᵥ monsterNortonPairHalfUPoolInputIntegral i) j =
      4 * monsterNortonPairHalfUPoolPhysicalSign i *
        monsterNortonPairHalfUPoolOutputIntegral i j := by
  revert i j
  decide +kernel

/-- The finite physical certificate gives the complete real-vector transport in actual Co0. -/
theorem monsterNortonPairHalfUPoolPhysical_actual (i : Fin 1552) :
    monsterNortonUFiber.val.2.val (griessShortVector (monsterNortonPairHalfUPoolInput i)) =
      (monsterNortonPairHalfUPoolPhysicalSign i : ℝ) •
        griessShortVector (monsterNortonPairHalfUPoolOutput i) := by
  apply monsterNortonUPhysical_of_certificate
  intro j
  rw [monsterNortonPairHalfUPoolInputIntegral_actual,
    monsterNortonPairHalfUPoolOutputIntegral_actual]
  exact monsterNortonPairHalfUPoolPhysical_certificate i j

/-- Every stored physical representative scalar is exactly plus or minus one. -/
theorem monsterNortonPairHalfUPoolPhysicalSign_unit (i : Fin 1552) :
    monsterNortonPairHalfUPoolPhysicalSign i = 1 ∨
      monsterNortonPairHalfUPoolPhysicalSign i = -1 := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
