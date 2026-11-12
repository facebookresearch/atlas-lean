/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch
import Code.FrontierD.SixVertexAlignedFirstReturn









namespace StatMech.FrontierD

noncomputable section



theorem localCIndicator_exchange_complementary_boundary_aligned_masks_exact
    (p q : SixVertexLocalIncomingPattern)
    (pairingP pairingQ vertexParity select0 select1 : Bool) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice)
    (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
    (hcompatibleP : compatible pairingP p)
    (hcompatibleQ : compatible pairingQ q)
    (hd : p d != q d)
    (hpartner : p (localMate pairingQ (localMate pairingP d)) !=
      q (localMate pairingQ (localMate pairingP d))) :
    exchangedLocalAlignedMaskCIndicator select0 select1
          (strandSlot pairingP d)
          (boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d) p q +
        exchangedLocalAlignedMaskCIndicator (!select0) (!select1)
          (strandSlot pairingP d)
          (boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d) p q =
      2 * (localCIndicator p + localCIndicator q) +
        2 * (if (select0 != select1) && (pairingP != pairingQ) &&
          (vertexParity != sideVertical d) then 2 else 0) := by
  rw [localCIndicator_exchange_boundary_aligned_mask_exact p q pairingP
      pairingQ vertexParity select0 select1 d hp hq hdegree hcompatibleP
      hcompatibleQ hd hpartner,
    localCIndicator_exchange_boundary_aligned_mask_exact p q pairingP
      pairingQ vertexParity (!select0) (!select1) d hp hq hdegree hcompatibleP
      hcompatibleQ hd hpartner]
  cases select0 <;> cases select1 <;> simp <;> try split_ifs <;> omega
  all_goals omega



theorem alignedMaskedComplementaryTargets_aggregateTotalC
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (select0 select1 : T.Vertex -> Bool)
    (hbond : AlignedMaskedBondConsistent
      homega heta hdegree select0 select1)
    (hbondComplement : AlignedMaskedBondConsistent homega heta hdegree
      (fun v => !select0 v) (fun v => !select1 v)) :
    2 * (sixVertexTorusCTypeCount omega + sixVertexTorusCTypeCount eta) <=
      (sixVertexTorusCTypeCount
          (alignedMaskedTarget homega heta hdegree select0 select1 false) +
        sixVertexTorusCTypeCount
          (alignedMaskedTarget homega heta hdegree select0 select1 true)) +
      (sixVertexTorusCTypeCount
          (alignedMaskedTarget homega heta hdegree
            (fun v => !select0 v) (fun v => !select1 v) false) +
        sixVertexTorusCTypeCount
          (alignedMaskedTarget homega heta hdegree
            (fun v => !select0 v) (fun v => !select1 v) true)) := by
  have hfirst := alignedMaskedTarget_totalC_mono homega heta hdegree
    select0 select1 hbond
  have hsecond := alignedMaskedTarget_totalC_mono homega heta hdegree
    (fun v => !select0 v) (fun v => !select1 v) hbondComplement
  omega

end

end StatMech.FrontierD
