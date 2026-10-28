/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The genuine Norton v translation preserves the specific reached spin catalogue. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SpinSupportData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The reached output catalogue is unchanged by the actual Norton v translation. -/
theorem monsterNortonLine01SpinSupport_output (n : Fin 4096) :
    monsterNortonLine01SpinSupport n ↔ monsterNortonLine01CompactOutputSupport n := by
  revert n
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
