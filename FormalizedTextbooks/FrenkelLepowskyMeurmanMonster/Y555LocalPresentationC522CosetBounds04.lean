/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact signed-letter, source, and strictly earlier reference bounds for this proof interval. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522CosetData04

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- All bounds of at most 128 complete literal coset certificates are verified in the kernel.
/-- Every source, signed letter, and prior coset reference has its exact actual bound. -/
theorem y522CosetData04_allowed (i : Fin 128) :
    (y522CosetData04 i).Allowed 1806 1863 10 (512 + i.val) := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
