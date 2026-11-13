/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexLoopFineFiberBridge









namespace StatMech.FrontierD

noncomputable section

local instance sixVertexLoopLexUnitFineRelationPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p



def sixVertexLoopDecoratedUnitTransferFineTarget
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (hunit : SixVertexLoopDecoratedLexComponentIsUnit middle
      hmiddle_pos hmiddle_lt source.1) :
    SixVertexLoopDecoratedPairFineProfileFiber
      T middle middle profile := by
  let colored := sixVertexLoopDecoratedPairColored source.1
  let h := sixVertexLoopDecoratedPositiveSeam
    middle hmiddle_pos hmiddle_lt source.1
  let target := sixVertexLoopDecoratedUnitTransferTarget middle
    hmiddle_pos hmiddle_lt source.1 hunit
  have htarget :=
    sixVertexLexDisagreementComponentColoredTarget_middle_of_transfer_one
      colored middle.val
      (by simpa [colored, sixVertexHorizontalLowerSector] using
        source.1.1.1.2.2)
      (by simpa [colored, sixVertexHorizontalUpperSector] using
        source.1.1.2.2.2)
      hmiddle_pos h hunit
  refine ⟨target, ?_⟩
  have hfine := htarget.2.2
  rw [← sixVertexLoopDecoratedUnitTransferTarget_colored
    middle hmiddle_pos hmiddle_lt source.1 hunit] at hfine
  exact hfine.trans source.2



def SixVertexLoopLexUnitFineRelated
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber
      T middle middle profile) : Prop :=
  exists hunit : SixVertexLoopDecoratedLexComponentIsUnit middle
      hmiddle_pos hmiddle_lt source.1,
    target = sixVertexLoopDecoratedUnitTransferFineTarget middle
      hmiddle_pos hmiddle_lt profile source hunit

theorem sixVertexLoopLexUnitFineRelated_target
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (hunit : SixVertexLoopDecoratedLexComponentIsUnit middle
      hmiddle_pos hmiddle_lt source.1) :
    SixVertexLoopLexUnitFineRelated middle hmiddle_pos hmiddle_lt profile
      source (sixVertexLoopDecoratedUnitTransferFineTarget middle
        hmiddle_pos hmiddle_lt profile source hunit) := by
  exact ⟨hunit, rfl⟩

theorem sixVertexLoopLexUnitFineRelated_iff_eq
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber
      T middle middle profile)
    (hunit : SixVertexLoopDecoratedLexComponentIsUnit middle
      hmiddle_pos hmiddle_lt source.1) :
    SixVertexLoopLexUnitFineRelated middle hmiddle_pos hmiddle_lt profile
        source target ↔
      target = sixVertexLoopDecoratedUnitTransferFineTarget middle
        hmiddle_pos hmiddle_lt profile source hunit := by
  constructor
  · rintro ⟨other, rfl⟩
    congr
  · intro htarget
    exact ⟨hunit, htarget⟩



theorem sixVertexLoopLexUnitFineRelated_nonempty
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (hunit : SixVertexLoopDecoratedLexComponentIsUnit middle
      hmiddle_pos hmiddle_lt source.1) :
    (Finset.univ.filter
      (SixVertexLoopLexUnitFineRelated middle hmiddle_pos hmiddle_lt
        profile source)).Nonempty := by
  refine ⟨sixVertexLoopDecoratedUnitTransferFineTarget middle
    hmiddle_pos hmiddle_lt profile source hunit, ?_⟩
  simp [sixVertexLoopLexUnitFineRelated_target middle hmiddle_pos
    hmiddle_lt profile source hunit]




theorem card_sixVertexLoopLexUnitFineRelated_eq_one
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (hunit : SixVertexLoopDecoratedLexComponentIsUnit middle
      hmiddle_pos hmiddle_lt source.1) :
    (Finset.univ.filter
      (SixVertexLoopLexUnitFineRelated middle hmiddle_pos hmiddle_lt
        profile source)).card = 1 := by
  classical
  rw [show Finset.univ.filter
      (SixVertexLoopLexUnitFineRelated middle hmiddle_pos hmiddle_lt
        profile source) =
      {sixVertexLoopDecoratedUnitTransferFineTarget middle
        hmiddle_pos hmiddle_lt profile source hunit} by
    ext target
    simp [sixVertexLoopLexUnitFineRelated_iff_eq middle hmiddle_pos
      hmiddle_lt profile source target hunit]]
  simp

end

end StatMech.FrontierD
