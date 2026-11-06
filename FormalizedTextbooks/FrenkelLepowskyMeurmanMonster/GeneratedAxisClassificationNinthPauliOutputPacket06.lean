/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliOutputData

/-! Exact full-phase output sums on chronological spin-address block6. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- Check eight integer source sums on only256 original addresses.
/-- Every candidate numerator in this block matches its specified exact signed Q sum. -/
theorem generatedNinth_pauli_output_packet_06 : ∀ b : Fin 8, ∀ m : Fin 256,
    let n : Fin 4096 := ⟨1536 + m.val, by omega⟩
    generatedNinthPauliOutputFast b n =
      generatedNinthPauliInputDenominator b * generatedNinthPauliMiddleInteger b n := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
