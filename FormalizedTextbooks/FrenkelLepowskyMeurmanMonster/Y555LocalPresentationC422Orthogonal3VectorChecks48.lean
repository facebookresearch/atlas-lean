/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact bounded coordinate checks for actual source-path recurrence. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorRecurrence

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- This finite source interval is checked by exact field arithmetic in the kernel.
/-- All 128 original reflection recurrences in interval 48 hold. -/
theorem y422Orthogonal3VectorChecks48 :
    ∀ j : Fin 128, y422Orthogonal3VectorRecurrence ⟨6144 + j.val, by omega⟩ := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
