/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPilot1mChecks

/-! # Pilot identification (Fifth root 1, inverse triality): matrix, pair and octad parts of the pairing -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part. -/
theorem pilot1m_partM : triMatF false pilot1Lg pilot1mW = 3 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part. -/
theorem pilot1m_partP : (pilot1mW.sh.pairs.map (fun q => (q.2 : ℚ) * triPairF false pilot1Lg q.1)).sum = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The octad part, through the packed octad transform. -/
theorem pilot1m_partO : (pilot1mW.sh.oct.map (fun b => (b.2.map (fun q =>
    q.2 * octZ 32 false (octPackX 32 false pilot1Lg) b.1 q.1)).sum)).sum = 59392 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
