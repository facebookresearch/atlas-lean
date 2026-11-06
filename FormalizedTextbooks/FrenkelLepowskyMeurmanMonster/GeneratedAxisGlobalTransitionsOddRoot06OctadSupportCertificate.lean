/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadSupportData

/-! Complete original preferred-vector certificates for the root-six positive octad destination frame. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
/-- All 120 actual physical source vectors reach the stated original standard-octad labels. -/
theorem generatedAxisGlobalOddRoot06OctadShortFrame_certificate : ∀ p : Fin 120, ∀ i : Fin 24,
    generatedAxisGlobalOddRoot06OctadFrameShortQ p i =
      (generatedAxisGlobalOddRoot06OctadVectorSign p : ℚ) *
        (generatedAxisGlobalShortIntegral (generatedAxisGlobalOddRoot06OctadTargetLabel p) i : ℚ) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
