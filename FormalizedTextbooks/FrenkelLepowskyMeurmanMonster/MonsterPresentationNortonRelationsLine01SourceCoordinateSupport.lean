/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact agreement of the source-code and actual compact spin support catalogues. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SourceCoordinateLookup
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CompactColumnData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Membership in the exact catalogue of actual source codes. -/
def monsterNortonLine01SourceCodeSupport (d : Fin 2048) : Prop :=
  monsterNortonLine01ShortInputCode (monsterNortonLine01SourceCodeLookup d) = d

instance (d : Fin 2048) : Decidable (monsterNortonLine01SourceCodeSupport d) :=
  inferInstanceAs (Decidable (_ = _))

/-- Every actual source code belongs to its exact catalogue. -/
theorem monsterNortonLine01SourceCodeSupport_label (a : Fin 64) :
    monsterNortonLine01SourceCodeSupport (monsterNortonLine01ShortInputCode a) := by
  unfold monsterNortonLine01SourceCodeSupport
  rw [monsterNortonLine01SourceCodeLookup_label]

/-- Low and high actual spin labels are supported exactly when their source code is supported. -/
theorem monsterNortonLine01SourceCodeSupport_spin (n : Fin 4096) :
    monsterNortonLine01CompactInputSupport n ↔
      monsterNortonLine01SourceCodeSupport ⟨n.val % 2048, by omega⟩ := by
  revert n
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
