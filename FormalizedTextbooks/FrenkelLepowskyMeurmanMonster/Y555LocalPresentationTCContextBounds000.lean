/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact alphabet, source and chronological reference bounds of literal TC derivation data. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCContextData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Every actual letter and source is checked, and every proof reference is strictly earlier.
/-- Literal TC records in block 000 name only actual letters, sources and earlier proofs. -/
theorem y322TCContextAllowed000 (i : Fin 256) :
    y322TCContextAllowedAt (0 + i.val) := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
