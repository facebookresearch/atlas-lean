/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.QuantumInfo.ChannelTopology

/-!
# Tests: topology of the space of quantum channels
-/

@[expose] public section

namespace PhyslibExtTest.QuantumInfo.ChannelTopology

set_option autoImplicit false

open PhyslibExt.QuantumInfo.ChannelTopology

#print axioms instCompactSpaceCPTPMap
#print axioms continuous_channel_apply
#print axioms continuous_compose
#print axioms continuous_tensor
#print axioms continuous_state_prod
#print axioms continuous_measure

/-- The compactness instance resolves at concrete qubit dimensions in both
arguments, and the joint continuity lemmas specialize to the constant
identity channel pairing. -/
theorem compact_and_continuous_qubits :
    CompactSpace (CPTPMap (Fin 2) (Fin 2)) ∧
      Continuous fun ρ : MState (Fin 2) => (CPTPMap.id : CPTPMap (Fin 2) (Fin 2)) ρ := by
  constructor
  · infer_instance
  · have h : Continuous fun ρ : MState (Fin 2) =>
        ((CPTPMap.id : CPTPMap (Fin 2) (Fin 2)), ρ) :=
      continuous_const.prodMk continuous_id
    exact continuous_channel_apply.comp h

end PhyslibExtTest.QuantumInfo.ChannelTopology
