/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortPackedData

/-! Complete finite genuine binary and central metadata of all twelve candidates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 20000000 in
-- Check all twenty-four original columns, 576 cocycle entries and central bits of each candidate.
/-- Every genuine compact candidate has its exact whole original extraspecial metadata. -/
theorem generatedTwelfth_complete_short_packed_metadata : ∀ g : Fin 12,
    generatedTwelfthCompleteShortPackedMetadata g := by
  unfold generatedTwelfthCompleteShortPackedMetadata
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
