/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact literal bindings of chronological claims to the original source transitions. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422CosetTransitionWords

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Exact finite indices and source-word boundaries are verified without runtime assumptions.
/-- Every target is literally its actual path/source-letter transition on both sides. -/
theorem y422CosetTargets36 (j : Fin 128) :
    y422CosetTargetWords ⟨4608 + j.val, by omega⟩ := by
  revert j
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
