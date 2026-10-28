/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete actual Q and Griess short transport of the sparse second-input half packet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfUPhysical
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfUInputQ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortVectorQTransport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 32000000 in
-- Check every complete central coefficient through the actual forward generator cache.
/-- All 240 actual transported preferred lifts have their genuine positive central phase. -/
theorem monsterNortonSecondHalfUPhase_actual (i : NortonSecondHalfShortIndex) :
    toAdd (spinConjugation monsterNortonUFiber.val.1
      (monsterNortonShortQ (monsterNortonSecondHalfShortInput i))).coeff = 0 := by
  rw [monsterNortonUQImage_eq, monsterNortonUQFastImage_eq,
    monsterNortonSecondHalfUInputQ_actual, monsterNortonUQFastImage_selected_phase]
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
