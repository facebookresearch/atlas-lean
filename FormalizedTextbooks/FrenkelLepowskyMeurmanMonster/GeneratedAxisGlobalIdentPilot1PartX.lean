/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPilot1Vec

/-! # Pilot identification: the packed odd cross terms of the pairing -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The odd terms of `g v₅` against the triality image of `h₁ v₅`. -/
theorem pilot1_partXW : oddXP 64 true (!true) pilot1W.sh.odd pilot1LX = 262144 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The odd terms of `h₁ v₅` against the tensor of `g v₅`. -/
theorem pilot1_partXL : oddXP 64 (!true) true pilot1Lg.sh.odd pilot1WX = 524288 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
