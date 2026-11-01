/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOperatorSourceSupport

/-! Original signed Pauli operator values on sixteen complete common-support addresses. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check all128 original signed operators at only sixteen common-support addresses.
/-- Each candidate state value is the complete original signed Pauli operator value. -/
theorem generatedNinth_pauli_operator_supported_packet_00 : ∀ q : Fin 128, ∀ v : Fin 16,
    let m : Fin 256 := ⟨0 + v.val, by omega⟩
    generatedNinthPauliStateInteger ⟨q.val, by omega⟩ (generatedNinthPauliSupportLabel m) =
      generatedNinthPauliSparse (generatedNinthPauliWitnessLabels q 0)
        (generatedNinthPauliWitnessLabels q 1) (generatedNinthColumnSpinPacked 0)
        (generatedNinthPauliSupportLabel m) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
