/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadOutgoingData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalOddZeroGuard

/-! Complete original finite outgoing short-coordinate certificates for the root-six positive transition. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 80000000

/-- Both original preferred pair families have exactly the complete candidate outgoing coefficient. -/
theorem generatedAxisGlobalOddRoot06OctadPair_certificate : ∀ s : Fin 2, ∀ p : Fin 276,
    generatedAxisGlobalOddRoot06PositiveShortQ (Sum.inl (s, p)) =
      generatedAxisGlobalOddRoot06OctadSparseShortQ (Sum.inl (s, p)) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
