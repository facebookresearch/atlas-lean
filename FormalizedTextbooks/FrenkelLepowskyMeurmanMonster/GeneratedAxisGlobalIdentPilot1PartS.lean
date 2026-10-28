/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPilot1Vec

/-! # Pilot identification: matrix, pair and octad parts of the pairing

Each part of the packed pairing `pairTriPO` is evaluated in its own kernel check (bounded kernel
memory per declaration). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part. -/
theorem pilot1_partM : triMatF true pilot1Lg pilot1W = 3 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part. -/
theorem pilot1_partP :
    (pilot1W.sh.pairs.map (fun q => (q.2 : ℚ) * triPairF true pilot1Lg q.1)).sum = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part, through the packed octad transform. -/
theorem pilot1_partO : (pilot1W.sh.oct.map (fun b => (b.2.map (fun q =>
    q.2 * octZ 32 true (octPackX 32 true pilot1Lg) b.1 q.1)).sum)).sum = 59392 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
