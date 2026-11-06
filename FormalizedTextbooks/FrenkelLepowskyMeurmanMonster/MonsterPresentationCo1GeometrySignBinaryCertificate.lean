/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Checked exact source sign actions, rather than independently assumed binary operators. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometrySignData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 60000000 in
-- Check twelve complete actual lattice change-of-basis identities by exact arithmetic.
/-- Every displayed binary matrix is the reduction of the actual integral basis action. -/
theorem monsterCo1GeometrySignBinary_certificate : ∀ k : Fin 12,
    monsterCo1GeometrySignBinary k = leechHyperbolicInverse *
      (monsterCo1GeometrySignIntegral k).map (Int.castRingHom (ZMod 2)) *
        leechHyperbolicMatrix := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
