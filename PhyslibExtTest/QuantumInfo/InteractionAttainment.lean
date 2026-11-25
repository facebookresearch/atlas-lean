/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.QuantumInfo.InteractionAttainment

/-!
# Tests: attainment of the interaction value
-/

@[expose] public section

namespace PhyslibExtTest.QuantumInfo.InteractionAttainment

set_option autoImplicit false

open PhyslibExt.QuantumInfo.Interaction

#print axioms exists_acceptProb_eq_value
#print axioms continuous_acceptProb

/-- Attainment instantiates at one round on qubits with a qubit workspace:
every such verifier has an optimal prover. -/
theorem attainment_one_round_qubits :
    ∀ V : Verifier 1 (Fin 2) (Fin 2),
      ∃ P : Prover 1 (Fin 2) (Fin 2), acceptProb V P = value V (Fin 2) := by
  intro V
  exact exists_acceptProb_eq_value V

end PhyslibExtTest.QuantumInfo.InteractionAttainment
