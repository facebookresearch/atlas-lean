/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact signed-letter, source, and strictly earlier reference bounds for this proof interval. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422CosetData178

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- All bounds of at most 128 complete literal coset certificates are verified in the kernel.
/-- Every source, signed letter, and prior coset reference has its exact actual bound. -/
theorem y422CosetData178_allowed (i : Fin 128) :
    (y422CosetData178 i).Allowed 9042 9079 8 (22784 + i.val) := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
