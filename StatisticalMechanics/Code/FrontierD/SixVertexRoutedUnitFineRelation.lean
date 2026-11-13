/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexResolvedUnitCrossFineRelation
import Code.FrontierD.SixVertexResolvedRoutedKey









namespace StatMech.FrontierD

noncomputable section

local instance sixVertexRoutedUnitFineRelationPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p



structure FKColoredFineTwoCycleUnitTransferRoutedKey
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    extends FKColoredUnitTransferRoutedKey source where
  fine : sixVertexHorizontalPairBoundedFineRowProfile
      (((toFKColoredUnitTransferRoutedKey.splice.target false).arrows.horizontal),
        ((toFKColoredUnitTransferRoutedKey.splice.target true).arrows.horizontal)) =
    sixVertexHorizontalPairBoundedFineRowProfile
      ((source false).arrows.horizontal, (source true).arrows.horizontal)
  twoCycle : sixVertexPairAtMostTwoCycleRelated
    ((source false).arrows, (source true).arrows)
    ((toFKColoredUnitTransferRoutedKey.splice.target false).arrows,
      (toFKColoredUnitTransferRoutedKey.splice.target true).arrows)

namespace FKColoredFineTwoCycleUnitTransferRoutedKey

def splice {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey source) :
    FKColoredStrandSplice source :=
  key.toFKColoredUnitTransferRoutedKey.splice

theorem target_bigrade
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey source) :
    (fkColoredLoopPairingPairTotalC key.splice.target,
        fkColoredTrueStrandSlotCount key.splice.target) =
      (fkColoredLoopPairingPairTotalC source,
        fkColoredTrueStrandSlotCount source) :=
  key.toFKColoredUnitTransferRoutedKey.target_bigrade

theorem target_fine
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey source) :
    sixVertexHorizontalPairBoundedFineRowProfile
        ((key.splice.target false).arrows.horizontal,
          (key.splice.target true).arrows.horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile
        ((source false).arrows.horizontal,
          (source true).arrows.horizontal) :=
  key.fine

theorem target_twoCycleFine
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey source) :
    sixVertexPairAtMostTwoCycleFineRelated
      ((source false).arrows, (source true).arrows)
      ((key.splice.target false).arrows,
        (key.splice.target true).arrows) :=
  ⟨key.twoCycle, key.fine.symm⟩

end FKColoredFineTwoCycleUnitTransferRoutedKey

def sixVertexLoopDecoratedRoutedUnitTarget
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : SixVertexLoopDecoratedPair T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt))
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source)) :
    SixVertexLoopDecoratedPair T middle middle := by
  let colored := sixVertexLoopDecoratedPairColored source
  have hsectors := key.toFKColoredUnitTransferRoutedKey.target_middleSectors
    middle.val hmiddle_pos
    (by simpa [colored, sixVertexHorizontalLowerSector] using source.1.1.2.2)
    (by simpa [colored, sixVertexHorizontalUpperSector] using source.1.2.2.2)
  exact ⟨(⟨(key.splice.target false).arrows,
      (key.splice.target false).iceRule, hsectors.1⟩,
    ⟨(key.splice.target true).arrows,
      (key.splice.target true).iceRule, hsectors.2⟩),
    (key.splice.target false).toCompatible,
    (key.splice.target true).toCompatible⟩

theorem sixVertexLoopDecoratedRoutedUnitTarget_colored
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : SixVertexLoopDecoratedPair T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt))
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source)) :
    sixVertexLoopDecoratedPairColored
        (sixVertexLoopDecoratedRoutedUnitTarget middle hmiddle_pos
          hmiddle_lt source key) = key.splice.target := by
  funext layer
  cases layer <;> exact FKColoredLoopPairing.toCompatible_toColored _

def sixVertexLoopDecoratedRoutedUnitFineTarget
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source.1)) :
    SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile := by
  refine ⟨sixVertexLoopDecoratedRoutedUnitTarget middle hmiddle_pos
    hmiddle_lt source.1 key, ?_⟩
  rw [sixVertexLoopDecoratedRoutedUnitTarget_colored]
  exact key.target_fine.trans source.2

theorem sixVertexLoopDecoratedRoutedUnitFineTarget_bigrade
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source.1)) :
    sixVertexLoopDecoratedPairBigrade
        (sixVertexLoopDecoratedRoutedUnitFineTarget middle hmiddle_pos
          hmiddle_lt profile source key).1 =
      sixVertexLoopDecoratedPairBigrade source.1 := by
  change sixVertexLoopDecoratedPairBigrade
      (sixVertexLoopDecoratedRoutedUnitTarget middle hmiddle_pos
        hmiddle_lt source.1 key) =
    sixVertexLoopDecoratedPairBigrade source.1
  rw [sixVertexLoopDecoratedPairBigrade_eq_colored,
    sixVertexLoopDecoratedPairBigrade_eq_colored,
    sixVertexLoopDecoratedRoutedUnitTarget_colored]
  exact key.target_bigrade

def SixVertexLoopRoutedUnitFineRelated
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber
      T middle middle profile) : Prop :=
  exists key : FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source.1),
    target = sixVertexLoopDecoratedRoutedUnitFineTarget middle
      hmiddle_pos hmiddle_lt profile source key

theorem sixVertexLoopRoutedUnitFineRelated_nonempty
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source.1)) :
    (Finset.univ.filter (SixVertexLoopRoutedUnitFineRelated middle
      hmiddle_pos hmiddle_lt profile source)).Nonempty := by
  refine ⟨sixVertexLoopDecoratedRoutedUnitFineTarget middle hmiddle_pos
    hmiddle_lt profile source key, ?_⟩
  simp [SixVertexLoopRoutedUnitFineRelated]

theorem rawFineProfile_of_routedUnitRelationEdgeDegree
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hne : forall (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile),
      Nonempty (FKColoredFineTwoCycleUnitTransferRoutedKey
        (sixVertexLoopDecoratedPairColored source.1)))
    (hdegree : forall profile source target,
      SixVertexLoopRoutedUnitFineRelated middle hmiddle_pos hmiddle_lt
          profile source target ->
        (Finset.univ.filter fun otherSource =>
          SixVertexLoopRoutedUnitFineRelated middle hmiddle_pos hmiddle_lt
            profile otherSource target).card <=
        (Finset.univ.filter
          (SixVertexLoopRoutedUnitFineRelated middle hmiddle_pos hmiddle_lt
            profile source)).card) :
    forall profile : SixVertexHorizontalBoundedFineRowProfile T,
      0 <= sixVertexHorizontalFineRowProfileSignedSum T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt)
        middle middle profile := by
  apply rawFineProfile_of_loopRelationEdgeDegree
    (SixVertexLoopRoutedUnitFineRelated middle hmiddle_pos hmiddle_lt)
  · intro profile source
    obtain ⟨key⟩ := hne profile source
    exact sixVertexLoopRoutedUnitFineRelated_nonempty middle hmiddle_pos
      hmiddle_lt profile source key
  · exact hdegree

end

end StatMech.FrontierD
