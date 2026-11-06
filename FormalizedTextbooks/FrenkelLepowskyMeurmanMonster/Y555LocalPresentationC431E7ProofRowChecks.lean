/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Kernel checks of every original-source E7 elementary proof in the exact C431 alphabet. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431E7ProofProgram

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
-- These checks replay all 5562 literal moves from the actual 171 source-equation seeds.
/-- Every square and commutator candidate row is checked against exact earlier source equations. -/
theorem y431E7ProofRow_checked (row : Fin 185) : y431E7ProofRowChecked row := by
  fin_cases row <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
