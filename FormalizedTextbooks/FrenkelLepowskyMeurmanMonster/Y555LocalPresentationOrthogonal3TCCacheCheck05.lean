/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Kernel checks for exact original-source matrix prefix recurrences. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCCacheCheck

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Actual source definitions and every finite matrix entry are checked simultaneously.
/-- Every actual source prefix in cache block 5 has its exact declared recurrence. -/
theorem y322Orthogonal3TCCacheCheck05 (i : Fin 128) :
    y322Orthogonal3TCCacheCheckAt (640 + i.val) := by
  fin_cases i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
