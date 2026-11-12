/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexLoopFullMaskFineRelation











namespace StatMech.FrontierD

noncomputable section

local instance sixVertexResolvedUnitCrossFineRelationPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p



theorem fkColoredVertexCrossTarget_slotColor
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask)
    (slot : FKLayeredStrandSlot T) :
    fkColoredLayeredSlotColor
        (fkColoredVertexCrossTarget source mask hbond) slot =
      fkColoredLayeredSlotColor source
        (fkColoredFullSwapLayeredSlotEquiv mask slot) := by
  rcases slot with ⟨layer, v, side⟩
  cases layer <;> cases side <;> cases hm : mask v <;>
    cases hfalse : (source false).pairing v <;>
    cases htrue : (source true).pairing v <;>
    simp [fkColoredLayeredSlotColor, fkColoredFullSwapLayeredSlotEquiv,
      fkColoredVertexCrossTarget, fkColoredVertexCrossRawColor,
      fkColoredLocalPairCrossIf, fkColoredLocalPairReconnection, hm,
      hfalse, htrue, FKColoredLoopPairing.localPairing,
      FKColoredLocalPairing.sideColor]

theorem fkColoredVertexCrossTarget_trueStrandSlotCount
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask) :
    fkColoredTrueStrandSlotCount
        (fkColoredVertexCrossTarget source mask hbond) =
      fkColoredTrueStrandSlotCount source := by
  unfold fkColoredTrueStrandSlotCount
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv (fkColoredFullSwapLayeredSlotEquiv mask)
  intro slot
  rw [fkColoredVertexCrossTarget_slotColor]

theorem fkColoredVertexCrossTarget_bigrade
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask) :
    (fkColoredLoopPairingPairTotalC
        (fkColoredVertexCrossTarget source mask hbond),
      fkColoredTrueStrandSlotCount
        (fkColoredVertexCrossTarget source mask hbond)) =
      (fkColoredLoopPairingPairTotalC source,
        fkColoredTrueStrandSlotCount source) := by
  exact Prod.ext
    (fkColoredVertexCrossTarget_totalC source mask hbond)
    (fkColoredVertexCrossTarget_trueStrandSlotCount source mask hbond)



structure FKColoredResolvedUnitCross
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) where
  mask : T.Vertex -> Bool
  bondCoherent : FKColoredVertexCrossBondCoherent source mask
  seamDelta_false : fkColoredVertexCrossSeamDelta source mask
    bondCoherent false = 1
  seamDelta_true : fkColoredVertexCrossSeamDelta source mask
    bondCoherent true = -1
  twoCycle : sixVertexPairAtMostTwoCycleRelated
    ((source false).arrows, (source true).arrows)
    ((fkColoredVertexCrossTarget source mask bondCoherent false).arrows,
      (fkColoredVertexCrossTarget source mask bondCoherent true).arrows)

def FKColoredResolvedUnitCross.target
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (cross : FKColoredResolvedUnitCross source) :
    FKColoredLoopPairingPair T :=
  fkColoredVertexCrossTarget source cross.mask cross.bondCoherent

theorem FKColoredResolvedUnitCross.target_bigrade
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (cross : FKColoredResolvedUnitCross source) :
    (fkColoredLoopPairingPairTotalC cross.target,
        fkColoredTrueStrandSlotCount cross.target) =
      (fkColoredLoopPairingPairTotalC source,
        fkColoredTrueStrandSlotCount source) :=
  fkColoredVertexCrossTarget_bigrade source cross.mask cross.bondCoherent

theorem FKColoredResolvedUnitCross.target_fine
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (cross : FKColoredResolvedUnitCross source) :
    sixVertexHorizontalPairBoundedFineRowProfile
        ((cross.target false).arrows.horizontal,
          (cross.target true).arrows.horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile
        ((source false).arrows.horizontal,
          (source true).arrows.horizontal) :=
  fkColoredVertexCrossTarget_boundedFineRowProfile source cross.mask
    cross.bondCoherent

theorem FKColoredResolvedUnitCross.target_twoCycleFine
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (cross : FKColoredResolvedUnitCross source) :
    sixVertexPairAtMostTwoCycleFineRelated
      ((source false).arrows, (source true).arrows)
      ((cross.target false).arrows, (cross.target true).arrows) :=
  ⟨cross.twoCycle, cross.target_fine.symm⟩


def sixVertexLoopDecoratedResolvedUnitCrossTarget
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : SixVertexLoopDecoratedPair T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt))
    (cross : FKColoredResolvedUnitCross
      (sixVertexLoopDecoratedPairColored source)) :
    SixVertexLoopDecoratedPair T middle middle := by
  let colored := sixVertexLoopDecoratedPairColored source
  have hsectors := fkColoredVertexCrossTarget_middleSectors colored
    cross.mask cross.bondCoherent middle.val hmiddle_pos
    (by simpa [colored, sixVertexHorizontalLowerSector] using source.1.1.2.2)
    (by simpa [colored, sixVertexHorizontalUpperSector] using source.1.2.2.2)
    cross.seamDelta_false cross.seamDelta_true
  exact ⟨(⟨(cross.target false).arrows,
      (cross.target false).iceRule, hsectors.1⟩,
    ⟨(cross.target true).arrows,
      (cross.target true).iceRule, hsectors.2⟩),
    (cross.target false).toCompatible,
    (cross.target true).toCompatible⟩

theorem sixVertexLoopDecoratedResolvedUnitCrossTarget_colored
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (source : SixVertexLoopDecoratedPair T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt))
    (cross : FKColoredResolvedUnitCross
      (sixVertexLoopDecoratedPairColored source)) :
    sixVertexLoopDecoratedPairColored
        (sixVertexLoopDecoratedResolvedUnitCrossTarget middle hmiddle_pos
          hmiddle_lt source cross) = cross.target := by
  funext layer
  cases layer <;> exact FKColoredLoopPairing.toCompatible_toColored _

def sixVertexLoopDecoratedResolvedUnitCrossFineTarget
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (cross : FKColoredResolvedUnitCross
      (sixVertexLoopDecoratedPairColored source.1)) :
    SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile := by
  refine ⟨sixVertexLoopDecoratedResolvedUnitCrossTarget middle
    hmiddle_pos hmiddle_lt source.1 cross, ?_⟩
  rw [sixVertexLoopDecoratedResolvedUnitCrossTarget_colored]
  exact cross.target_fine.trans source.2

theorem sixVertexLoopDecoratedResolvedUnitCrossFineTarget_bigrade
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (cross : FKColoredResolvedUnitCross
      (sixVertexLoopDecoratedPairColored source.1)) :
    sixVertexLoopDecoratedPairBigrade
        (sixVertexLoopDecoratedResolvedUnitCrossFineTarget middle
          hmiddle_pos hmiddle_lt profile source cross).1 =
      sixVertexLoopDecoratedPairBigrade source.1 := by
  change sixVertexLoopDecoratedPairBigrade
      (sixVertexLoopDecoratedResolvedUnitCrossTarget middle
        hmiddle_pos hmiddle_lt source.1 cross) =
    sixVertexLoopDecoratedPairBigrade source.1
  rw [sixVertexLoopDecoratedPairBigrade_eq_colored,
    sixVertexLoopDecoratedPairBigrade_eq_colored,
    sixVertexLoopDecoratedResolvedUnitCrossTarget_colored]
  exact cross.target_bigrade


def SixVertexLoopResolvedUnitCrossFineRelated
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber
      T middle middle profile) : Prop :=
  exists cross : FKColoredResolvedUnitCross
      (sixVertexLoopDecoratedPairColored source.1),
    target = sixVertexLoopDecoratedResolvedUnitCrossFineTarget middle
      hmiddle_pos hmiddle_lt profile source cross

theorem sixVertexLoopResolvedUnitCrossFineRelated_nonempty
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (cross : FKColoredResolvedUnitCross
      (sixVertexLoopDecoratedPairColored source.1)) :
    (Finset.univ.filter
      (SixVertexLoopResolvedUnitCrossFineRelated middle hmiddle_pos
        hmiddle_lt profile source)).Nonempty := by
  refine ⟨sixVertexLoopDecoratedResolvedUnitCrossFineTarget middle
    hmiddle_pos hmiddle_lt profile source cross, ?_⟩
  simp [SixVertexLoopResolvedUnitCrossFineRelated]

noncomputable def sixVertexLoopResolvedUnitCrossOfRelated
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (hrelated : SixVertexLoopResolvedUnitCrossFineRelated middle
      hmiddle_pos hmiddle_lt profile source target) :
    FKColoredResolvedUnitCross
      (sixVertexLoopDecoratedPairColored source.1) :=
  hrelated.choose

theorem sixVertexLoopResolvedUnitCrossOfRelated_target
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (hrelated : SixVertexLoopResolvedUnitCrossFineRelated middle
      hmiddle_pos hmiddle_lt profile source target) :
    target = sixVertexLoopDecoratedResolvedUnitCrossFineTarget middle
      hmiddle_pos hmiddle_lt profile source
        (sixVertexLoopResolvedUnitCrossOfRelated middle hmiddle_pos
          hmiddle_lt profile source target hrelated) :=
  hrelated.choose_spec

theorem sixVertexLoopResolvedUnitCrossFineRelated_bigrade
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (hrelated : SixVertexLoopResolvedUnitCrossFineRelated middle
      hmiddle_pos hmiddle_lt profile source target) :
    sixVertexLoopDecoratedPairBigrade target.1 =
      sixVertexLoopDecoratedPairBigrade source.1 := by
  rw [sixVertexLoopResolvedUnitCrossOfRelated_target middle hmiddle_pos
    hmiddle_lt profile source target hrelated]
  exact sixVertexLoopDecoratedResolvedUnitCrossFineTarget_bigrade middle
    hmiddle_pos hmiddle_lt profile source _

theorem sixVertexLoopResolvedUnitCrossFineRelated_twoCycle
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (hrelated : SixVertexLoopResolvedUnitCrossFineRelated middle
      hmiddle_pos hmiddle_lt profile source target) :
    sixVertexPairAtMostTwoCycleFineRelated
      ((sixVertexLoopDecoratedPairColored source.1 false).arrows,
        (sixVertexLoopDecoratedPairColored source.1 true).arrows)
      ((sixVertexLoopDecoratedPairColored target.1 false).arrows,
        (sixVertexLoopDecoratedPairColored target.1 true).arrows) := by
  let cross := sixVertexLoopResolvedUnitCrossOfRelated middle hmiddle_pos
    hmiddle_lt profile source target hrelated
  have htarget := congrArg (fun decorated =>
      sixVertexLoopDecoratedPairColored decorated.1)
    (sixVertexLoopResolvedUnitCrossOfRelated_target middle hmiddle_pos
      hmiddle_lt profile source target hrelated)
  change sixVertexLoopDecoratedPairColored target.1 =
    sixVertexLoopDecoratedPairColored
      (sixVertexLoopDecoratedResolvedUnitCrossTarget middle hmiddle_pos
        hmiddle_lt source.1 cross) at htarget
  rw [sixVertexLoopDecoratedResolvedUnitCrossTarget_colored] at htarget
  rw [htarget]
  exact cross.target_twoCycleFine



theorem rawFineProfile_of_resolvedUnitCrossRelationEdgeDegree
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hne : forall (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile),
      Nonempty (FKColoredResolvedUnitCross
        (sixVertexLoopDecoratedPairColored source.1)))
    (hdegree : forall
      (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
      (target : SixVertexLoopDecoratedPairFineProfileFiber
        T middle middle profile),
      SixVertexLoopResolvedUnitCrossFineRelated middle hmiddle_pos
          hmiddle_lt profile source target ->
        (Finset.univ.filter fun otherSource =>
          SixVertexLoopResolvedUnitCrossFineRelated middle hmiddle_pos
            hmiddle_lt profile otherSource target).card <=
        (Finset.univ.filter
          (SixVertexLoopResolvedUnitCrossFineRelated middle hmiddle_pos
            hmiddle_lt profile source)).card) :
    forall profile : SixVertexHorizontalBoundedFineRowProfile T,
      0 <= sixVertexHorizontalFineRowProfileSignedSum T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt)
        middle middle profile := by
  apply rawFineProfile_of_loopRelationEdgeDegree
    (SixVertexLoopResolvedUnitCrossFineRelated middle hmiddle_pos hmiddle_lt)
  · intro profile source
    obtain ⟨cross⟩ := hne profile source
    exact sixVertexLoopResolvedUnitCrossFineRelated_nonempty middle
      hmiddle_pos hmiddle_lt profile source cross
  · exact hdegree

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_resolvedUnitCrossRelationEdgeDegree
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hne : forall (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile),
      Nonempty (FKColoredResolvedUnitCross
        (sixVertexLoopDecoratedPairColored source.1)))
    (hdegree : forall
      (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
      (target : SixVertexLoopDecoratedPairFineProfileFiber
        T middle middle profile),
      SixVertexLoopResolvedUnitCrossFineRelated middle hmiddle_pos
          hmiddle_lt profile source target ->
        (Finset.univ.filter fun otherSource =>
          SixVertexLoopResolvedUnitCrossFineRelated middle hmiddle_pos
            hmiddle_lt profile otherSource target).card <=
        (Finset.univ.filter
          (SixVertexLoopResolvedUnitCrossFineRelated middle hmiddle_pos
            hmiddle_lt profile source)).card) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val := by
  apply sixVertexMarkedTraceCoefficientwiseLogConcave_of_rawFineProfile
    T middle hmiddle_pos hmiddle_lt
  exact rawFineProfile_of_resolvedUnitCrossRelationEdgeDegree middle
    hmiddle_pos hmiddle_lt hne hdegree

end

end StatMech.FrontierD
