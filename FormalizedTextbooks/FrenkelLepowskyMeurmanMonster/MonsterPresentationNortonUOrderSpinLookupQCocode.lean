/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- An exact finite certificate for one actual Norton source factor. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderSpinLookup

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Verify every one of the 4096 displayed source signs against its actual binary formula.
/-- Exact finite sign certificate for the qcocode factor. -/
theorem monsterNortonSpinSign_qcocode : ∀ n : Fin 4096,
    monsterNortonSpinSign 5 n = nortonUIntegerSign
      (spinPhase (sourceQCocode (golayLabelCoefficients 1807)) (golayLabelCoefficients n)) := by
  decide +kernel


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
