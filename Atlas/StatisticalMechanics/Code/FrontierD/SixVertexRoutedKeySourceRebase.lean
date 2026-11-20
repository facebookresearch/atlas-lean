/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexRoutedKeySlotColorInvariant










namespace StatMech.FrontierD

noncomputable section



theorem coloredIndexedOccurrenceBoundaryIntertwining_rebase
    {T : EvenTorus} (source rebased : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (hcolor : forall slot : FKLayeredStrandSlot T,
      fkColoredLayeredSlotColor rebased slot =
        fkColoredLayeredSlotColor source slot)
    (hboundary : FKColoredIndexedOccurrenceBoundaryIntertwining
      source targetPairing n key hinjective) :
    FKColoredIndexedOccurrenceBoundaryIntertwining
      rebased targetPairing n key hinjective := by
  intro x
  simpa only [fkColoredStrandSpliceRawColor, hcolor] using hboundary x


theorem indexedOccurrenceSplice_target_rebase
    {T : EvenTorus} (source rebased : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (hcolor : forall slot : FKLayeredStrandSlot T,
      fkColoredLayeredSlotColor rebased slot =
        fkColoredLayeredSlotColor source slot)
    (hboundary : FKColoredIndexedOccurrenceBoundaryIntertwining
      source targetPairing n key hinjective) :
    (FKColoredStrandSplice.ofIndexedOccurrences rebased targetPairing n key
        hinjective
        (coloredIndexedOccurrenceBoundaryIntertwining_rebase source rebased
          targetPairing n key hinjective hcolor hboundary)).target =
      (FKColoredStrandSplice.ofIndexedOccurrences source targetPairing n key
        hinjective hboundary).target := by
  funext layer
  apply FKColoredLoopPairing.ext
  · rfl
  · funext dart
    change fkColoredStrandSpliceRawColor rebased targetPairing
        (fkIndexedOccurrenceSlotEquiv n key hinjective) (layer, dart) =
      fkColoredStrandSpliceRawColor source targetPairing
        (fkIndexedOccurrenceSlotEquiv n key hinjective) (layer, dart)
    simp only [fkColoredStrandSpliceRawColor, hcolor]



noncomputable def FKColoredFineTwoCycleUnitTransferRoutedKey.rebase
    {T : EvenTorus} {source rebased : FKColoredLoopPairingPair T}
    (certificate : FKColoredFineTwoCycleUnitTransferRoutedKey source)
    (hcolor : forall slot : FKLayeredStrandSlot T,
      fkColoredLayeredSlotColor rebased slot =
        fkColoredLayeredSlotColor source slot)
    (harrows : forall layer,
      (rebased layer).arrows = (source layer).arrows) :
    FKColoredFineTwoCycleUnitTransferRoutedKey rebased := by
  let routed := certificate.toFKColoredUnitTransferRoutedKey
  let hboundary := coloredIndexedOccurrenceBoundaryIntertwining_rebase
    source rebased routed.targetPairing routed.occurrenceCount routed.key
      routed.key_injective hcolor routed.boundaryIntertwining
  let rebasedSplice := FKColoredStrandSplice.ofIndexedOccurrences rebased
    routed.targetPairing routed.occurrenceCount routed.key
      routed.key_injective hboundary
  have htarget : rebasedSplice.target = routed.splice.target := by
    exact indexedOccurrenceSplice_target_rebase source rebased
      routed.targetPairing routed.occurrenceCount routed.key
      routed.key_injective hcolor routed.boundaryIntertwining
  refine
    { targetPairing := routed.targetPairing
      occurrenceCount := routed.occurrenceCount
      key := routed.key
      key_injective := routed.key_injective
      boundaryIntertwining := hboundary
      preservesTotalC := ?_
      seamDelta_false := ?_
      seamDelta_true := ?_
      fine := ?_
      twoCycle := ?_ }
  · unfold FKColoredStrandSplice.PreservesTotalC
      fkColoredSlotPairEqualCount
    simpa only [hcolor] using routed.preservesTotalC
  · unfold FKColoredStrandSplice.seamDelta
    rw [htarget, harrows false]
    exact routed.seamDelta_false
  · unfold FKColoredStrandSplice.seamDelta
    rw [htarget, harrows true]
    exact routed.seamDelta_true
  · change sixVertexHorizontalPairBoundedFineRowProfile
        ((rebasedSplice.target false).arrows.horizontal,
          (rebasedSplice.target true).arrows.horizontal) = _
    rw [htarget, harrows false, harrows true]
    exact certificate.fine
  · change sixVertexPairAtMostTwoCycleRelated
      ((rebased false).arrows, (rebased true).arrows)
      ((rebasedSplice.target false).arrows,
        (rebasedSplice.target true).arrows)
    rw [htarget, harrows false, harrows true]
    exact certificate.twoCycle



theorem FKColoredFineTwoCycleUnitTransferRoutedKey.rebase_target
    {T : EvenTorus} {source rebased : FKColoredLoopPairingPair T}
    (certificate : FKColoredFineTwoCycleUnitTransferRoutedKey source)
    (hcolor : forall slot : FKLayeredStrandSlot T,
      fkColoredLayeredSlotColor rebased slot =
        fkColoredLayeredSlotColor source slot)
    (harrows : forall layer,
      (rebased layer).arrows = (source layer).arrows) :
    (certificate.rebase hcolor harrows).splice.target =
      certificate.splice.target := by
  exact indexedOccurrenceSplice_target_rebase source rebased
    certificate.toFKColoredUnitTransferRoutedKey.targetPairing
    certificate.toFKColoredUnitTransferRoutedKey.occurrenceCount
    certificate.toFKColoredUnitTransferRoutedKey.key
    certificate.toFKColoredUnitTransferRoutedKey.key_injective hcolor
    certificate.toFKColoredUnitTransferRoutedKey.boundaryIntertwining

end

end StatMech.FrontierD
