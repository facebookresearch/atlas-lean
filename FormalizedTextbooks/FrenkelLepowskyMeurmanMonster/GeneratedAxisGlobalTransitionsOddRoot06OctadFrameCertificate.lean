/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadFrameData

/-! A complete original rational matrix certificate for the genuine root-six octad projection frame. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
/-- Every transformed original matrix entry is the exact physical projection onto the displayed octad. -/
theorem generatedAxisGlobalOddRoot06OctadMatrix_certificate : ∀ i j : Fin 24,
    generatedAxisGlobalOddRoot06OctadMatrixQ i j =
      if i = j ∧ (0x714281 : ℕ).testBit i.val then (1 : ℚ) else 0 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
