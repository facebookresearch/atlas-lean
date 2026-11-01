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

/-- All original odd labels have exactly the complete candidate outgoing coefficient. -/
theorem generatedAxisGlobalOddRoot06OctadOdd_certificate (d : Fin 2048) (j : Fin 24) :
    generatedAxisGlobalOddRoot06PositiveShortQ (Sum.inr (Sum.inr (d, j))) =
      generatedAxisGlobalOddRoot06OctadSparseShortQ (Sum.inr (Sum.inr (d, j))) := by
  have h : ∀ d : Fin 2048, ∀ j : Fin 24,
      generatedAxisGlobalRationalOddShortZeroGuard (generatedAxisGlobalOddSparseRootPacket 1) d j =
        generatedAxisGlobalOddRoot06OctadSparseShortQ (Sum.inr (Sum.inr (d, j))) := by
    decide +kernel
  exact (generatedAxisGlobalRationalOddShortZeroGuard_actual
    (generatedAxisGlobalOddSparseRootPacket 1) d j).symm.trans (h d j)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
