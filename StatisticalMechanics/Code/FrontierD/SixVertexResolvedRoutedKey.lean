/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexIndexedOccurrenceSplice
import Code.FrontierD.SixVertexMarkedPairResolvedInjection











namespace StatMech.FrontierD

noncomputable section



structure FKColoredUnitTransferRoutedKey
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) where
  targetPairing : Bool -> FKMedialLoopPairing T
  occurrenceCount : Nat
  key : Bool -> Fin occurrenceCount -> T.Vertex × Bool
  key_injective : forall layer, Function.Injective (key layer)
  boundaryIntertwining : FKColoredIndexedOccurrenceBoundaryIntertwining
    source targetPairing occurrenceCount key key_injective
  preservesTotalC :
    (FKColoredStrandSplice.ofIndexedOccurrences source targetPairing
      occurrenceCount key key_injective boundaryIntertwining).PreservesTotalC
  seamDelta_false :
    (FKColoredStrandSplice.ofIndexedOccurrences source targetPairing
      occurrenceCount key key_injective boundaryIntertwining).seamDelta
        false = 1
  seamDelta_true :
    (FKColoredStrandSplice.ofIndexedOccurrences source targetPairing
      occurrenceCount key key_injective boundaryIntertwining).seamDelta
        true = -1


def FKColoredUnitTransferRoutedKey.splice
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (certificate : FKColoredUnitTransferRoutedKey source) :
    FKColoredStrandSplice source :=
  FKColoredStrandSplice.ofIndexedOccurrences source
    certificate.targetPairing certificate.occurrenceCount certificate.key
    certificate.key_injective certificate.boundaryIntertwining

theorem FKColoredUnitTransferRoutedKey.splice_preservesTotalC
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (certificate : FKColoredUnitTransferRoutedKey source) :
    certificate.splice.PreservesTotalC :=
  certificate.preservesTotalC

theorem FKColoredUnitTransferRoutedKey.splice_seamDelta_false
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (certificate : FKColoredUnitTransferRoutedKey source) :
    certificate.splice.seamDelta false = 1 :=
  certificate.seamDelta_false

theorem FKColoredUnitTransferRoutedKey.splice_seamDelta_true
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (certificate : FKColoredUnitTransferRoutedKey source) :
    certificate.splice.seamDelta true = -1 :=
  certificate.seamDelta_true


theorem FKColoredUnitTransferRoutedKey.target_bigrade
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (certificate : FKColoredUnitTransferRoutedKey source) :
    (fkColoredLoopPairingPairTotalC certificate.splice.target,
        fkColoredTrueStrandSlotCount certificate.splice.target) =
      (fkColoredLoopPairingPairTotalC source,
        fkColoredTrueStrandSlotCount source) :=
  certificate.splice.target_bigrade certificate.splice_preservesTotalC


@[simp] theorem FKColoredUnitTransferRoutedKey.recover
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (certificate : FKColoredUnitTransferRoutedKey source) :
    certificate.splice.symm.target = source :=
  certificate.splice.symm_target



theorem FKColoredUnitTransferRoutedKey.target_middleSectors
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (certificate : FKColoredUnitTransferRoutedKey source)
    (middle : Nat) (hmiddle : 0 < middle)
    (hlower : sixVertexUpCount
        (svTorusVerticalRows T (source false).arrows
          (svFinLast T.height_pos)) = middle - 1)
    (hupper : sixVertexUpCount
        (svTorusVerticalRows T (source true).arrows
          (svFinLast T.height_pos)) = middle + 1) :
    sixVertexUpCount
        (svTorusVerticalRows T (certificate.splice.target false).arrows
          (svFinLast T.height_pos)) = middle /\
      sixVertexUpCount
        (svTorusVerticalRows T (certificate.splice.target true).arrows
          (svFinLast T.height_pos)) = middle :=
  certificate.splice.target_middleSectors middle hmiddle hlower hupper
    certificate.splice_seamDelta_false certificate.splice_seamDelta_true


abbrev SixVertexExplicitResolvedUnitTransferRoutedKey
    {T : EvenTorus} {lower upper : Fin (T.width + 1)} {k : Nat}
    (resolved : SixVertexExplicitResolvedMarkedPair T lower upper k) :=
  FKColoredUnitTransferRoutedKey
    (sixVertexExplicitResolvedColoredPair resolved)

end

end StatMech.FrontierD
