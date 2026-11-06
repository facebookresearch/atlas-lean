/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact actual physical U action on all short units of the sparse second-input half packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfUCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUInversePhysicalCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 64000000 in
-- Check all 5760 physical output coordinates in exact integer arithmetic.
/-- The genuine source U numerator takes each original input to the stated signed output. -/
theorem monsterNortonSecondHalfUPhysical_certificate
    (i : NortonSecondHalfShortIndex) (j : Fin 24) :
    (monsterNortonUNumerator1 *ᵥ monsterNortonSecondHalfInputIntegral i) j =
      4 * monsterNortonSecondHalfUPhysicalSign (monsterNortonSecondHalfShortStorage i) *
        monsterNortonSecondHalfOutputIntegral i j := by
  revert i j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
