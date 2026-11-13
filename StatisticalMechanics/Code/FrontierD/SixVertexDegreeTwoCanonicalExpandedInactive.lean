/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant

namespace StatMech.FrontierD

noncomputable section

local instance canonicalExpandedInactiveActiveDecidable
    {T : EvenTorus} {omega eta : SixVertexArrows T} :
    DecidablePred (activeBlackDart (omega := omega) (eta := eta)) :=
  Classical.decPred _

@[simp] theorem sixVertexDegreeTwoCanonicalExpandedRetieMask_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (dart : FKMedialBlackDart T)
    (hinactive : Not (activeBlackDart (omega := omega) (eta := eta) dart)) :
    sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree middle
      homegaSector hetaSector hmiddle layer dart.1.1 = false := by
  have htransition : sixVertexDegreeTwoCanonicalTransitionMask homega heta
      hdegree middle homegaSector hetaSector hmiddle dart.1.1 = false := by
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    by_cases hleft : cut.cutLeft = []
    · simp [sixVertexDegreeTwoCanonicalTransitionMask, cut, hleft]
    · by_cases hright : cut.cutRight = []
      · simp [sixVertexDegreeTwoCanonicalTransitionMask, cut, hleft, hright]
      · have hrightVertex : dart.1.1 ≠
            doubledAlignedVertex (cut.cutRight.head hright) := by
          intro hv
          apply hinactive
          change (sixVertexLocalDisagreementSides
            (sixVertexLocalIncomingPattern omega dart.1.1)
            (sixVertexLocalIncomingPattern eta dart.1.1)).card = 2
          rw [hv]
          exact sixVertexDisagreementDart_local_card_eq_two hdegree
            (cut.cutRight.head hright).1
        have hleftVertex : dart.1.1 ≠
            doubledAlignedVertex (cut.cutLeft.head hleft) := by
          intro hv
          apply hinactive
          change (sixVertexLocalDisagreementSides
            (sixVertexLocalIncomingPattern omega dart.1.1)
            (sixVertexLocalIncomingPattern eta dart.1.1)).card = 2
          rw [hv]
          exact sixVertexDisagreementDart_local_card_eq_two hdegree
            (cut.cutLeft.head hleft).1
        simp [sixVertexDegreeTwoCanonicalTransitionMask, cut, hleft, hright,
          hrightVertex, hleftVertex]
  have hcorrection :
      sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
        homegaSector hetaSector hmiddle layer dart.1.1 = false := by
    have hnot : Not ((sixVertexLocalDisagreementSides
        (sixVertexLocalIncomingPattern omega dart.1.1)
        (sixVertexLocalIncomingPattern eta dart.1.1)).card = 2) := hinactive
    simp [sixVertexDegreeTwoCanonicalCorrectionMask,
      sixVertexDegreeTwoCanonicalInternalMismatchVertex, hnot]
  simp [sixVertexDegreeTwoCanonicalExpandedRetieMask, htransition,
    hcorrection]

theorem sixVertexDegreeTwoCanonicalExpandedBoundaryFalseDart_of_unmasked
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (dart : FKMedialBlackDart T)
    (hmaskD : sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree
      middle homegaSector hetaSector hmiddle layer dart.1.1 = false)
    (hnext : Not (activeBlackDart (omega := omega) (eta := eta)
      (alignedBoundaryPerm homega heta hdegree false dart))) :
    sixVertexDegreeTwoCanonicalExpandedBoundaryFalseDart homega heta hdegree
        middle homegaSector hetaSector hmiddle layer dart =
      alignedBoundaryPerm homega heta hdegree false dart := by
  let mask := sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree
    middle homegaSector hetaSector hmiddle layer
  let next := alignedBoundaryPerm homega heta hdegree false dart
  have hmaskNext : mask next.1.1 = false := by
    exact sixVertexDegreeTwoCanonicalExpandedRetieMask_inactive homega heta
      hdegree middle homegaSector hetaSector hmiddle layer next hnext
  have hswapNext : alignedBlackDartLayerSwap homega heta hdegree next = next :=
    alignedBlackDartLayerSwap_inactive homega heta hdegree next hnext
  have hswapNextSymm :
      (alignedBlackDartLayerSwap homega heta hdegree).symm next = next := by
    apply (alignedBlackDartLayerSwap homega heta hdegree).injective
    simpa [hswapNext]
  simp [sixVertexDegreeTwoCanonicalExpandedBoundaryFalseDart,
    sixVertexDegreeTwoAlignedFalseDartSlotSwap, mask, next, hmaskD,
    hmaskNext, hswapNextSymm]

theorem sixVertexDegreeTwoCanonicalExpanded_falseDart_color_of_unmasked
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (dart : FKMedialBlackDart T)
    (hmaskD : sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree
      middle homegaSector hetaSector hmiddle layer dart.1.1 = false)
    (hnext : Not (activeBlackDart (omega := omega) (eta := eta)
      (alignedBoundaryPerm homega heta hdegree false dart))) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
            heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle
            homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta hdegree
            middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree layer
            (sixVertexDegreeTwoCanonicalExpandedBoundaryFalseDart homega heta
              hdegree middle homegaSector hetaSector hmiddle layer dart))) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
            heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle
            homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta hdegree
            middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree layer dart)) := by
  rw [sixVertexDegreeTwoCanonicalExpandedBoundaryFalseDart_of_unmasked homega
    heta hdegree middle homegaSector hetaSector hmiddle layer dart hmaskD hnext]
  exact sixVertexDegreeTwoAlignedTransportedColor_falseBoundary_of_inactive
    homega heta hdegree middle homegaSector hetaSector hmiddle layer dart hnext

end

end StatMech.FrontierD
