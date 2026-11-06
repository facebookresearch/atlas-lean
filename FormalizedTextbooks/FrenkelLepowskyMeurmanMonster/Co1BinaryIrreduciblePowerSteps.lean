/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1BinaryIrreducibleData

/-! Actual finite matrix power certificates for the binary rank-one construction. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 200000000 in
-- The finite matrix certificate checks every recorded coordinate.
/-- Every recorded power is obtained from the same original twelve-letter word matrix. -/
theorem co1Irreducible_power_steps : ∀ n : Fin 13, ∀ i j : Fin 24,
    (co1IrreducibleStage 12 * co1IrreducibleStage ⟨n.val + 12, by omega⟩) i j =
      co1IrreducibleStage ⟨n.val + 13, by omega⟩ i j := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
