/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact bounded block of the original-source C522 auxiliary path definitions. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522WordPrograms

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Exact earlier path and source letter for this bounded auxiliary path interval. -/
def y522TPathData14 : Fin 3 → ℕ × Fin 11 :=
  ![
    (1179, 4),
    (1792, 3),
    (1793, 4)]

set_option maxRecDepth 100000 in
-- At most 128 literal path definitions are checked here, with their exact global positions.
/-- Every nonempty path in this block refers strictly to an earlier actual path. -/
theorem y522TPathData14_prior (i : Fin 3) (hi : 0 < 1792 + i.val) :
    (y522TPathData14 i).1 < 1792 + i.val := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
