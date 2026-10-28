/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual finite source A5 matrix prefix and exact encoding certificates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3A5Check

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every source generator, matrix entry, and sorted encoding is checked by the kernel.
/-- Every actual source candidate in A5 block 5 has its exact matrix recurrence and encoding. -/
theorem y322Orthogonal3A5Check05 (i : Fin 128) :
    y322Orthogonal3A5CheckAt (640 + i.val) := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
