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

/-- Every original Fourier output on active octad 14 has exactly the full candidate coefficient. -/
theorem generatedAxisGlobalOddRoot06OctadFourier14_certificate : ∀ e : Fin 64,
    generatedAxisGlobalOddRoot06PositiveShortQ
      (Sum.inr (Sum.inl (generatedAxisGlobalOddRoot06ActiveOctad 14, e))) =
        generatedAxisGlobalOddRoot06OctadSparseShortQ
          (Sum.inr (Sum.inl (generatedAxisGlobalOddRoot06ActiveOctad 14, e))) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
