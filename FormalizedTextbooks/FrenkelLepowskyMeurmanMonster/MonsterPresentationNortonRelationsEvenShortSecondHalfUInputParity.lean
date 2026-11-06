/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Certified integral-basis parity of the actual sparse second-half short inputs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfUCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 10000 in
set_option maxHeartbeats 64000000 in
-- Check each of the 5760 actual integral-basis parity coordinates before hyperbolic conversion.
/-- The stored parity mask is the true original lattice-coordinate parity of each short input. -/
theorem monsterNortonSecondHalfUInputParity_actual
    (i : NortonSecondHalfShortIndex) (j : Fin 24) :
    integerParity (monsterNortonLeechCoordinates (monsterNortonSecondHalfInputIntegral i)) j =
      if (monsterNortonSecondHalfShortParity (monsterNortonSecondHalfShortStorage i)).testBit
        j.val then 1 else 0 := by
  revert i j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
