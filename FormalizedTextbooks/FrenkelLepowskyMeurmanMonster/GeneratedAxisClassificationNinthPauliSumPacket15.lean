/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliBasisData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSumFast

/-! Exact integer input reconstruction on chronological common-support block15. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- Check only128 equations, retaining every one of the original128 signed source states.
/-- The exact integer reconstruction holds on all eight inputs and sixteen support addresses. -/
theorem generatedNinth_pauli_sum_packet_15 : ∀ b : Fin 8, ∀ m : Fin 16,
    let h : Fin 256 := ⟨240 + m.val, by omega⟩
    generatedNinthPauliInputDenominator b *
      generatedNinthPauliStateInteger ⟨128 + b.val, by omega⟩
        (generatedNinthPauliSupportLabel h) =
      ∑ q : Fin 128, generatedNinthPauliInputCoefficients b q *
        generatedNinthPauliStateInteger ⟨q.val, by omega⟩
          (generatedNinthPauliSupportLabel h) := by
  simp_rw [← generatedNinth_pauli_reconstruction_fast]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
