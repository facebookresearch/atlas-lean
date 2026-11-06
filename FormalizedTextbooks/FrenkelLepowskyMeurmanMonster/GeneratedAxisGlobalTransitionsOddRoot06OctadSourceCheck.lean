/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadOutgoingData

/-! Complete finite family and spin-symmetry certificates for the original root-six source packet. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

/-- All 552 original input labels have exactly the permitted pair and active-octad families. -/
theorem generatedAxisGlobalOddRoot06InitialAllowed_certificate :
    ∀ p : GeneratedAxisGlobalOddShortPacketIndex,
      generatedAxisGlobalOddRoot06InitialAllowed (generatedAxisGlobalOddSparseLabel 1 p) := by
  decide +kernel

/-- Every retained original output octad belongs to the complete list of original active octads. -/
theorem generatedAxisGlobalOddRoot06OutgoingAllowed_certificate : ∀ p : Fin 120,
    generatedAxisGlobalOddRoot06OctadAllowed (generatedAxisGlobalOddRoot06OctadSourceLabel p) := by
  decide +kernel

/-- All original low and high spin coefficients agree in this complete source state. -/
theorem generatedAxisGlobalOddRoot06Spin_low_high : ∀ d : Fin 2048,
    generatedAxisGlobalOddRoot06Spin08 ⟨d.val, by omega⟩ =
      generatedAxisGlobalOddRoot06Spin08 ⟨d.val + 2048, by omega⟩ := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
