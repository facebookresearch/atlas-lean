/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPilot1Vec

/-! # Pilot identification: the packed tensor part of the pairing -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The tensor part: the multiplicative packed pairing of the triality tensor part of `h₁ v₅`
with the tensor of `g v₅`. -/
theorem pilot1_partT : tdotM 64 (trialityTensorT 64 (!true) pilot1LX) pilot1WX = 16777216 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
