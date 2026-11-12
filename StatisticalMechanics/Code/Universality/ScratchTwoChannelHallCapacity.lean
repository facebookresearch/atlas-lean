/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.ScratchTwoChannelCanonicalRoute









open Finset SimpleGraph Set

namespace StatMech.Universality

noncomputable section



noncomputable def rlc_twoChannelPIMSFixedPayloadEmbeddingOfPacking
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (packing : RlcTwoChannelPIMSDiscardedPayloadPacking hclosure)
    (eta : RlcTwoChannelEdgeSuccess gamma gamma') :
    RlcTwoChannelTargetFibre
        (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure) eta ↪
      ConfigSpace (RlcTwoChannelPIMSFixedPayloadSlot
        (rlc_twoChannelCanonicalRoute eta)) where
  toFun rho e := packing.packConfig rho.1 e.1.1
  inj' := by
    intro rho sigma hpayload
    apply Subtype.ext
    apply packing.injective_on_fibre rho.1 sigma.1
    · exact rho.2.trans sigma.2.symm
    · funext e
      by_cases hvariable : rlc_pimsEdgeEquiv (e.1.map Subtype.val) ∈
          rlc_connectorCentralFaceEdges gamma gamma'
      · let vtarget : RlcTwoChannelPIMSVariableTargetEdge gamma gamma' :=
          ⟨e, hvariable⟩
        rw [packing.variable_eq rho.1 vtarget,
          packing.variable_eq sigma.1 vtarget, rho.2, sigma.2]
      · let ftarget : RlcTwoChannelPIMSFixedTargetEdge gamma gamma' :=
          ⟨e, hvariable⟩
        by_cases hroute : e ∈ rlc_twoChannelOpenEdgeSet
            (rlc_twoChannelCanonicalRoute eta).1
        · rw [packing.reserved_open rho.1 e (by simpa [rho.2] using hroute),
            packing.reserved_open sigma.1 e (by simpa [sigma.2] using hroute)]
        · let payload : RlcTwoChannelPIMSFixedPayloadSlot
              (rlc_twoChannelCanonicalRoute eta) := ⟨ftarget, hroute⟩
          exact congrFun hpayload payload



theorem rlc_twoChannelPIMSFixedPayloadCapacity_iff_nonempty_packing
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma') :
    RlcTwoChannelPIMSFixedPayloadCapacity hclosure ↔
      Nonempty (RlcTwoChannelPIMSDiscardedPayloadPacking hclosure) := by
  constructor
  · intro hcapacity
    exact ⟨rlc_twoChannelPIMSDiscardedPayloadPackingOfCapacity
      hclosure hcapacity⟩
  · rintro ⟨packing⟩ eta
    letI := Fintype.ofFinite (RlcTwoChannelTargetFibre
      (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure) eta)
    letI := Fintype.ofFinite (ConfigSpace
      (RlcTwoChannelPIMSFixedPayloadSlot
        (rlc_twoChannelCanonicalRoute eta)))
    simpa only [Nat.card_eq_fintype_card] using
      Fintype.card_le_of_embedding
        (rlc_twoChannelPIMSFixedPayloadEmbeddingOfPacking packing eta)

end

end StatMech.Universality
