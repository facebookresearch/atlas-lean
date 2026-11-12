/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexFullComponentMaskSwap










namespace StatMech.FrontierD

noncomputable section

local instance sixVertexLoopFullMaskFineRelationPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p



theorem sixVertexLoopDecoratedPairColored_injective
    {T : EvenTorus} {left right : Fin (T.width + 1)} :
    Function.Injective
      (sixVertexLoopDecoratedPairColored :
        SixVertexLoopDecoratedPair T left right ->
          FKColoredLoopPairingPair T) := by
  intro first second h
  have hpair : first.1 = second.1 := by
    apply Prod.ext
    · apply Subtype.ext
      simpa using congrArg FKColoredLoopPairing.arrows (congrFun h false)
    · apply Subtype.ext
      simpa using congrArg FKColoredLoopPairing.arrows (congrFun h true)
  cases first with
  | mk firstPair firstDecoration =>
    cases second with
    | mk secondPair secondDecoration =>
      dsimp at hpair
      subst secondPair
      have hdecoration : firstDecoration = secondDecoration := by
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg FKColoredLoopPairing.pairing (congrFun h false)
        · apply Subtype.ext
          exact congrArg FKColoredLoopPairing.pairing (congrFun h true)
      exact Sigma.ext rfl (heq_of_eq hdecoration)



theorem fkColoredFullSwapTarget_injective_fixedMask
    {T : EvenTorus} (mask : T.Vertex -> Bool)
    (first second : FKColoredLoopPairingPair T)
    (hfirst : FKColoredFullSwapBondCoherent first mask)
    (hsecond : FKColoredFullSwapBondCoherent second mask)
    (heq : fkColoredFullSwapTarget first mask hfirst =
      fkColoredFullSwapTarget second mask hsecond) :
    first = second := by
  funext layer
  apply FKColoredLoopPairing.ext
  · funext v
    by_cases hm : mask v = true
    · have hv := congrArg (fun target =>
          (target (!layer)).pairing v) heq
      simpa [fkColoredFullSwapTarget_pairing, hm] using hv
    · have hv := congrArg (fun target => (target layer).pairing v) heq
      simpa [fkColoredFullSwapTarget_pairing, hm] using hv
  · funext d
    by_cases hm : mask d.1 = true
    · have hd := congrArg (fun target => (target (!layer)).color d) heq
      simpa [fkColoredFullSwapTarget_color, hm] using hd
    · have hd := congrArg (fun target => (target layer).color d) heq
      simpa [fkColoredFullSwapTarget_color, hm] using hd

theorem fkColoredFullSwapTarget_injective_of_mask_eq
    {T : EvenTorus} (firstMask secondMask : T.Vertex -> Bool)
    (first second : FKColoredLoopPairingPair T)
    (hfirst : FKColoredFullSwapBondCoherent first firstMask)
    (hsecond : FKColoredFullSwapBondCoherent second secondMask)
    (hmasks : firstMask = secondMask)
    (heq : fkColoredFullSwapTarget first firstMask hfirst =
      fkColoredFullSwapTarget second secondMask hsecond) :
    first = second := by
  funext layer
  apply FKColoredLoopPairing.ext
  · funext v
    by_cases hm : firstMask v = true
    · have hmSecond : secondMask v = true := by rw [← hmasks]; exact hm
      have hv := congrArg (fun target =>
        (target (!layer)).pairing v) heq
      simpa [fkColoredFullSwapTarget_pairing, hm, hmSecond] using hv
    · have hmSecond : secondMask v ≠ true := by
        rwa [← hmasks]
      have hv := congrArg (fun target => (target layer).pairing v) heq
      simpa [fkColoredFullSwapTarget_pairing, hm, hmSecond] using hv
  · funext d
    by_cases hm : firstMask d.1 = true
    · have hmSecond : secondMask d.1 = true := by rw [← hmasks]; exact hm
      have hd := congrArg (fun target => (target (!layer)).color d) heq
      simpa [fkColoredFullSwapTarget_color, hm, hmSecond] using hd
    · have hmSecond : secondMask d.1 ≠ true := by
        rwa [← hmasks]
      have hd := congrArg (fun target => (target layer).color d) heq
      simpa [fkColoredFullSwapTarget_color, hm, hmSecond] using hd



theorem sixVertexTorusMaskSeamTransfer_pairSwitch
    {T : EvenTorus} (mask omega eta : SixVertexArrows T) :
    sixVertexTorusMaskSeamTransfer mask
        (sixVertexTorusSwitchFirst mask omega eta)
        (sixVertexTorusSwitchSecond mask omega eta) =
      -sixVertexTorusMaskSeamTransfer mask omega eta := by
  unfold sixVertexTorusMaskSeamTransfer
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  cases hm : mask.vertical (i, svFinLast T.height_pos) <;>
    cases ho : omega.vertical (i, svFinLast T.height_pos) <;>
    cases he : eta.vertical (i, svFinLast T.height_pos) <;>
    simp [sixVertexTorusSwitchFirst, sixVertexTorusSwitchSecond, hm, ho, he]


theorem SixVertexFullDisagreementMask.pairSwitch
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hmask : SixVertexFullDisagreementMask omega eta mask) :
    SixVertexFullDisagreementMask
      (sixVertexTorusSwitchFirst mask omega eta)
      (sixVertexTorusSwitchSecond mask omega eta) mask := by
  constructor
  · intro v d hd
    rw [sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees,
      sixVertexTorusEdgeDisagrees_pairSwitch_iff]
    exact (sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
      omega eta v d).1 (hmask.1 v d hd)
  · intro v d r hd hr
    apply hmask.2 v d r hd
    rw [sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees] at hr ⊢
    exact (sixVertexTorusEdgeDisagrees_pairSwitch_iff
      mask omega eta _).1 hr



theorem SixVertexFullDisagreementMask.eq_fullDisagreementMask_switchFirst
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hmask : SixVertexFullDisagreementMask omega eta mask) :
    mask = sixVertexFullDisagreementMask omega
      (sixVertexTorusSwitchFirst mask omega eta) := by
  apply SixVertexArrows.ext <;> funext v
  · by_cases hm : mask.horizontal v = true
    · have hdiff : omega.horizontal v ≠ eta.horizontal v := by
        simpa [sixVertexLocalIncomingPattern, fkLoopEastIncoming] using
          hmask.1 v 1 (by
            simpa [sixVertexTorusLocalSwitchMask] using hm)
      simp [sixVertexFullDisagreementMask, sixVertexTorusSwitchFirst,
        hm, hdiff]
    · have hmfalse : mask.horizontal v = false :=
        Bool.eq_false_of_not_eq_true hm
      simp [sixVertexFullDisagreementMask, sixVertexTorusSwitchFirst,
        hmfalse]
  · by_cases hm : mask.vertical v = true
    · have hdiff : omega.vertical v ≠ eta.vertical v := by
        simpa [sixVertexLocalIncomingPattern, fkLoopNorthIncoming] using
          hmask.1 v 3 (by
            simpa [sixVertexTorusLocalSwitchMask] using hm)
      simp [sixVertexFullDisagreementMask, sixVertexTorusSwitchFirst,
        hm, hdiff]
    · have hmfalse : mask.vertical v = false :=
        Bool.eq_false_of_not_eq_true hm
      simp [sixVertexFullDisagreementMask, sixVertexTorusSwitchFirst,
        hmfalse]



theorem sixVertexTorusSwitchFirst_injective_on_fullMasks
    {T : EvenTorus} {omega eta first second : SixVertexArrows T}
    (hfirst : SixVertexFullDisagreementMask omega eta first)
    (hsecond : SixVertexFullDisagreementMask omega eta second)
    (heq : sixVertexTorusSwitchFirst first omega eta =
      sixVertexTorusSwitchFirst second omega eta) :
    first = second := by
  calc
    first = sixVertexFullDisagreementMask omega
        (sixVertexTorusSwitchFirst first omega eta) :=
      hfirst.eq_fullDisagreementMask_switchFirst
    _ = sixVertexFullDisagreementMask omega
        (sixVertexTorusSwitchFirst second omega eta) := by rw [heq]
    _ = second := hsecond.eq_fullDisagreementMask_switchFirst.symm

theorem sixVertexPairUnionHorizontal_pairSwitch
    {T : EvenTorus} (mask omega eta : SixVertexArrows T) :
    sixVertexPairUnionHorizontal (omega, eta) =
      sixVertexPairUnionHorizontal
        (sixVertexTorusSwitchFirst mask omega eta,
          sixVertexTorusSwitchSecond mask omega eta) := by
  funext v
  unfold sixVertexPairUnionHorizontal
  by_cases hm : mask.horizontal v = true <;>
    simp [sixVertexTorusSwitchFirst, sixVertexTorusSwitchSecond,
      hm, add_comm]

theorem sixVertexPairUnionVertical_pairSwitch
    {T : EvenTorus} (mask omega eta : SixVertexArrows T) :
    sixVertexPairUnionVertical (omega, eta) =
      sixVertexPairUnionVertical
        (sixVertexTorusSwitchFirst mask omega eta,
          sixVertexTorusSwitchSecond mask omega eta) := by
  funext v
  unfold sixVertexPairUnionVertical
  by_cases hm : mask.vertical v = true <;>
    simp [sixVertexTorusSwitchFirst, sixVertexTorusSwitchSecond,
      hm, add_comm]



theorem SixVertexFullDisagreementMask.pairAtMostTwoCycleFineRelated
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hmask : SixVertexFullDisagreementMask omega eta mask) :
    sixVertexPairAtMostTwoCycleFineRelated (omega, eta)
      (sixVertexTorusSwitchFirst mask omega eta,
        sixVertexTorusSwitchSecond mask omega eta) := by
  constructor
  · apply sixVertexPairAtMostTwoCycleRelated_of_union_eq
    · exact sixVertexPairUnionHorizontal_pairSwitch mask omega eta
    · exact sixVertexPairUnionVertical_pairSwitch mask omega eta
  · exact hmask.boundedFineRowProfile.symm



theorem sixVertexLexDisagreementComponentMask_full
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
    SixVertexFullDisagreementMask omega eta
      (sixVertexLexDisagreementComponentMask T omega eta h) := by
  constructor
  · intro v d hd
    rw [sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees]
    apply sixVertexLexDisagreementComponentMask_selects_only_disagreement
      T omega eta h
    rw [← sixVertexTorusLocalSwitchMask_apply]
    exact hd
  · intro v d r hd hr
    exact sixVertexLexDisagreementComponentMask_incident_closure
      T omega eta h v d r hd hr



def sixVertexLoopDecoratedFullMaskFineTarget
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (sixVertexLoopDecoratedPairColored source.1 false).arrows
      (sixVertexLoopDecoratedPairColored source.1 true).arrows mask)
    (htransfer : sixVertexTorusMaskSeamTransfer mask
      (sixVertexLoopDecoratedPairColored source.1 false).arrows
      (sixVertexLoopDecoratedPairColored source.1 true).arrows = 1) :
    SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile := by
  refine ⟨sixVertexLoopDecoratedFullMaskTarget middle hmiddle_pos
    hmiddle_lt source.1 mask hmask htransfer, ?_⟩
  have hfine := sixVertexFullDisagreementColoredTarget_boundedFineRowProfile
    (sixVertexLoopDecoratedPairColored source.1) mask hmask
  rw [← sixVertexLoopDecoratedFullMaskTarget_colored middle hmiddle_pos
    hmiddle_lt source.1 mask hmask htransfer] at hfine
  exact hfine.trans source.2

theorem sixVertexLoopDecoratedFullMaskFineTarget_false_arrows
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (sixVertexLoopDecoratedPairColored source.1 false).arrows
      (sixVertexLoopDecoratedPairColored source.1 true).arrows mask)
    (htransfer : sixVertexTorusMaskSeamTransfer mask
      (sixVertexLoopDecoratedPairColored source.1 false).arrows
      (sixVertexLoopDecoratedPairColored source.1 true).arrows = 1) :
    (sixVertexLoopDecoratedPairColored
        (sixVertexLoopDecoratedFullMaskFineTarget middle hmiddle_pos
          hmiddle_lt profile source mask hmask htransfer).1 false).arrows =
      sixVertexTorusSwitchFirst mask
        (sixVertexLoopDecoratedPairColored source.1 false).arrows
        (sixVertexLoopDecoratedPairColored source.1 true).arrows := by
  change (sixVertexLoopDecoratedPairColored
    (sixVertexLoopDecoratedFullMaskTarget middle hmiddle_pos hmiddle_lt
      source.1 mask hmask htransfer) false).arrows = _
  rw [sixVertexLoopDecoratedFullMaskTarget_colored,
    sixVertexFullDisagreementColoredTarget_arrows]
  rfl

theorem sixVertexLoopDecoratedFullMaskFineTarget_true_arrows
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (sixVertexLoopDecoratedPairColored source.1 false).arrows
      (sixVertexLoopDecoratedPairColored source.1 true).arrows mask)
    (htransfer : sixVertexTorusMaskSeamTransfer mask
      (sixVertexLoopDecoratedPairColored source.1 false).arrows
      (sixVertexLoopDecoratedPairColored source.1 true).arrows = 1) :
    (sixVertexLoopDecoratedPairColored
        (sixVertexLoopDecoratedFullMaskFineTarget middle hmiddle_pos
          hmiddle_lt profile source mask hmask htransfer).1 true).arrows =
      sixVertexTorusSwitchSecond mask
        (sixVertexLoopDecoratedPairColored source.1 false).arrows
        (sixVertexLoopDecoratedPairColored source.1 true).arrows := by
  change (sixVertexLoopDecoratedPairColored
    (sixVertexLoopDecoratedFullMaskTarget middle hmiddle_pos hmiddle_lt
      source.1 mask hmask htransfer) true).arrows = _
  rw [sixVertexLoopDecoratedFullMaskTarget_colored,
    sixVertexFullDisagreementColoredTarget_arrows]
  rfl



abbrev SixVertexLoopFullUnitMask
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile) :=
  {mask : SixVertexArrows T //
    SixVertexFullDisagreementMask
        (sixVertexLoopDecoratedPairColored source.1 false).arrows
        (sixVertexLoopDecoratedPairColored source.1 true).arrows mask /\
      sixVertexTorusMaskSeamTransfer mask
        (sixVertexLoopDecoratedPairColored source.1 false).arrows
        (sixVertexLoopDecoratedPairColored source.1 true).arrows = 1}



abbrev SixVertexLoopFullNegativeMask
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (target : SixVertexLoopDecoratedPairFineProfileFiber
      T middle middle profile) :=
  {mask : SixVertexArrows T //
    SixVertexFullDisagreementMask
        (sixVertexLoopDecoratedPairColored target.1 false).arrows
        (sixVertexLoopDecoratedPairColored target.1 true).arrows mask /\
      sixVertexTorusMaskSeamTransfer mask
        (sixVertexLoopDecoratedPairColored target.1 false).arrows
        (sixVertexLoopDecoratedPairColored target.1 true).arrows = -1}

def sixVertexLoopFullUnitMaskTarget
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (certificate : SixVertexLoopFullUnitMask middle hmiddle_pos
      hmiddle_lt profile source) :
    SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile :=
  sixVertexLoopDecoratedFullMaskFineTarget middle hmiddle_pos hmiddle_lt
    profile source certificate.1 certificate.2.1 certificate.2.2

theorem sixVertexLoopFullUnitMaskTarget_injective
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile) :
    Function.Injective (sixVertexLoopFullUnitMaskTarget middle
      hmiddle_pos hmiddle_lt profile source) := by
  intro first second heq
  apply Subtype.ext
  apply sixVertexTorusSwitchFirst_injective_on_fullMasks
      first.2.1 second.2.1
  have harrows := congrArg (fun target =>
    (sixVertexLoopDecoratedPairColored target.1 false).arrows) heq
  simpa only [sixVertexLoopFullUnitMaskTarget,
    sixVertexLoopDecoratedFullMaskFineTarget_false_arrows] using harrows



def SixVertexLoopFullMaskFineRelated
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber
      T middle middle profile) : Prop :=
  exists (mask : SixVertexArrows T)
      (hmask : SixVertexFullDisagreementMask
        (sixVertexLoopDecoratedPairColored source.1 false).arrows
        (sixVertexLoopDecoratedPairColored source.1 true).arrows mask)
      (htransfer : sixVertexTorusMaskSeamTransfer mask
        (sixVertexLoopDecoratedPairColored source.1 false).arrows
        (sixVertexLoopDecoratedPairColored source.1 true).arrows = 1),
    target = sixVertexLoopDecoratedFullMaskFineTarget middle hmiddle_pos
      hmiddle_lt profile source mask hmask htransfer

theorem sixVertexLoopFullMaskFineRelated_target
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (sixVertexLoopDecoratedPairColored source.1 false).arrows
      (sixVertexLoopDecoratedPairColored source.1 true).arrows mask)
    (htransfer : sixVertexTorusMaskSeamTransfer mask
      (sixVertexLoopDecoratedPairColored source.1 false).arrows
      (sixVertexLoopDecoratedPairColored source.1 true).arrows = 1) :
    SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt profile
      source (sixVertexLoopDecoratedFullMaskFineTarget middle hmiddle_pos
        hmiddle_lt profile source mask hmask htransfer) := by
  exact ⟨mask, hmask, htransfer, rfl⟩



theorem sixVertexLoopDecoratedFullMaskFineTarget_lex
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (hunit : SixVertexLoopDecoratedLexComponentIsUnit middle
      hmiddle_pos hmiddle_lt source.1) :
    let h := sixVertexLoopDecoratedPositiveSeam middle hmiddle_pos
      hmiddle_lt source.1
    let mask := sixVertexLexDisagreementComponentMask T
      (sixVertexLoopDecoratedPairColored source.1 false).arrows
      (sixVertexLoopDecoratedPairColored source.1 true).arrows h
    let hmask := sixVertexLexDisagreementComponentMask_full T
      (sixVertexLoopDecoratedPairColored source.1 false).arrows
      (sixVertexLoopDecoratedPairColored source.1 true).arrows h
    sixVertexLoopDecoratedFullMaskFineTarget middle hmiddle_pos hmiddle_lt
        profile source mask hmask hunit =
      sixVertexLoopDecoratedUnitTransferFineTarget middle hmiddle_pos
        hmiddle_lt profile source hunit := by
  dsimp
  rfl

theorem sixVertexLoopLexUnitFineRelated_imp_fullMaskFineRelated
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (hrelated : SixVertexLoopLexUnitFineRelated middle hmiddle_pos
      hmiddle_lt profile source target) :
    SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
      profile source target := by
  obtain ⟨hunit, rfl⟩ := hrelated
  let h := sixVertexLoopDecoratedPositiveSeam middle hmiddle_pos
    hmiddle_lt source.1
  let mask := sixVertexLexDisagreementComponentMask T
    (sixVertexLoopDecoratedPairColored source.1 false).arrows
    (sixVertexLoopDecoratedPairColored source.1 true).arrows h
  let hmask := sixVertexLexDisagreementComponentMask_full T
    (sixVertexLoopDecoratedPairColored source.1 false).arrows
    (sixVertexLoopDecoratedPairColored source.1 true).arrows h
  have htransfer : sixVertexTorusMaskSeamTransfer mask
      (sixVertexLoopDecoratedPairColored source.1 false).arrows
      (sixVertexLoopDecoratedPairColored source.1 true).arrows = 1 := by
    exact hunit
  refine ⟨mask, hmask, htransfer, ?_⟩
  exact (sixVertexLoopDecoratedFullMaskFineTarget_lex middle hmiddle_pos
    hmiddle_lt profile source hunit).symm



noncomputable def sixVertexLoopFullUnitMaskOfRelated
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (hrelated : SixVertexLoopFullMaskFineRelated middle hmiddle_pos
      hmiddle_lt profile source target) :
    SixVertexLoopFullUnitMask middle hmiddle_pos hmiddle_lt profile source :=
  ⟨hrelated.choose, hrelated.choose_spec.choose,
    hrelated.choose_spec.choose_spec.choose⟩

theorem sixVertexLoopFullUnitMaskOfRelated_target
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (hrelated : SixVertexLoopFullMaskFineRelated middle hmiddle_pos
      hmiddle_lt profile source target) :
    target = sixVertexLoopFullUnitMaskTarget middle hmiddle_pos hmiddle_lt
      profile source (sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos
        hmiddle_lt profile source target hrelated) := by
  exact hrelated.choose_spec.choose_spec.choose_spec

theorem sixVertexLoopFullUnitMaskOfRelated_false_arrows
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (hrelated : SixVertexLoopFullMaskFineRelated middle hmiddle_pos
      hmiddle_lt profile source target) :
    let certificate := sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos
      hmiddle_lt profile source target hrelated
    (sixVertexLoopDecoratedPairColored target.1 false).arrows =
      sixVertexTorusSwitchFirst certificate.1
        (sixVertexLoopDecoratedPairColored source.1 false).arrows
        (sixVertexLoopDecoratedPairColored source.1 true).arrows := by
  let certificate := sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos
    hmiddle_lt profile source target hrelated
  calc
    (sixVertexLoopDecoratedPairColored target.1 false).arrows =
        (sixVertexLoopDecoratedPairColored
          (sixVertexLoopFullUnitMaskTarget middle hmiddle_pos hmiddle_lt
            profile source certificate).1 false).arrows :=
      congrArg (fun decorated =>
        (sixVertexLoopDecoratedPairColored decorated.1 false).arrows)
        (sixVertexLoopFullUnitMaskOfRelated_target middle hmiddle_pos
          hmiddle_lt profile source target hrelated)
    _ = _ := sixVertexLoopDecoratedFullMaskFineTarget_false_arrows
      middle hmiddle_pos hmiddle_lt profile source _ _ _

theorem sixVertexLoopFullUnitMaskOfRelated_true_arrows
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (hrelated : SixVertexLoopFullMaskFineRelated middle hmiddle_pos
      hmiddle_lt profile source target) :
    let certificate := sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos
      hmiddle_lt profile source target hrelated
    (sixVertexLoopDecoratedPairColored target.1 true).arrows =
      sixVertexTorusSwitchSecond certificate.1
        (sixVertexLoopDecoratedPairColored source.1 false).arrows
        (sixVertexLoopDecoratedPairColored source.1 true).arrows := by
  let certificate := sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos
    hmiddle_lt profile source target hrelated
  calc
    (sixVertexLoopDecoratedPairColored target.1 true).arrows =
        (sixVertexLoopDecoratedPairColored
          (sixVertexLoopFullUnitMaskTarget middle hmiddle_pos hmiddle_lt
            profile source certificate).1 true).arrows :=
      congrArg (fun decorated =>
        (sixVertexLoopDecoratedPairColored decorated.1 true).arrows)
        (sixVertexLoopFullUnitMaskOfRelated_target middle hmiddle_pos
          hmiddle_lt profile source target hrelated)
    _ = _ := sixVertexLoopDecoratedFullMaskFineTarget_true_arrows
      middle hmiddle_pos hmiddle_lt profile source _ _ _

theorem sixVertexLoopFullUnitMaskOfRelated_colored
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (hrelated : SixVertexLoopFullMaskFineRelated middle hmiddle_pos
      hmiddle_lt profile source target) :
    let certificate := sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos
      hmiddle_lt profile source target hrelated
    sixVertexLoopDecoratedPairColored target.1 =
      sixVertexFullDisagreementColoredTarget
        (sixVertexLoopDecoratedPairColored source.1)
        certificate.1 certificate.2.1 := by
  let certificate := sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos
    hmiddle_lt profile source target hrelated
  calc
    sixVertexLoopDecoratedPairColored target.1 =
        sixVertexLoopDecoratedPairColored
          (sixVertexLoopFullUnitMaskTarget middle hmiddle_pos hmiddle_lt
            profile source certificate).1 :=
      congrArg (fun decorated =>
        sixVertexLoopDecoratedPairColored decorated.1)
        (sixVertexLoopFullUnitMaskOfRelated_target middle hmiddle_pos
          hmiddle_lt profile source target hrelated)
    _ = _ := sixVertexLoopDecoratedFullMaskTarget_colored middle
      hmiddle_pos hmiddle_lt source.1 certificate.1
        certificate.2.1 certificate.2.2



noncomputable def sixVertexLoopFullNegativeMaskOfPreimage
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (preimage : {source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile //
      SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
        profile source target}) :
    SixVertexLoopFullNegativeMask profile target := by
  let certificate := sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos
    hmiddle_lt profile preimage.1 target preimage.2
  refine ⟨certificate.1, ?_, ?_⟩
  · rw [sixVertexLoopFullUnitMaskOfRelated_false_arrows middle
      hmiddle_pos hmiddle_lt profile preimage.1 target preimage.2,
    sixVertexLoopFullUnitMaskOfRelated_true_arrows middle
      hmiddle_pos hmiddle_lt profile preimage.1 target preimage.2]
    exact certificate.2.1.pairSwitch
  · rw [sixVertexLoopFullUnitMaskOfRelated_false_arrows middle
      hmiddle_pos hmiddle_lt profile preimage.1 target preimage.2,
    sixVertexLoopFullUnitMaskOfRelated_true_arrows middle
      hmiddle_pos hmiddle_lt profile preimage.1 target preimage.2,
    sixVertexTorusMaskSeamTransfer_pairSwitch, certificate.2.2]

@[simp] theorem sixVertexLoopFullNegativeMaskOfPreimage_val
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (preimage : {source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile //
      SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
        profile source target}) :
    (sixVertexLoopFullNegativeMaskOfPreimage middle hmiddle_pos
      hmiddle_lt profile target preimage).1 =
        (sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos hmiddle_lt
          profile preimage.1 target preimage.2).1 := rfl



theorem sixVertexLoopFullNegativeMaskOfPreimage_injective
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile) :
    Function.Injective (sixVertexLoopFullNegativeMaskOfPreimage middle
      hmiddle_pos hmiddle_lt profile target) := by
  intro first second heq
  let firstCertificate := sixVertexLoopFullUnitMaskOfRelated middle
    hmiddle_pos hmiddle_lt profile first.1 target first.2
  let secondCertificate := sixVertexLoopFullUnitMaskOfRelated middle
    hmiddle_pos hmiddle_lt profile second.1 target second.2
  have hmask : firstCertificate.1 = secondCertificate.1 := by
    have := congrArg Subtype.val heq
    simpa [firstCertificate, secondCertificate] using this
  have hfirst := sixVertexLoopFullUnitMaskOfRelated_colored middle
    hmiddle_pos hmiddle_lt profile first.1 target first.2
  have hsecond := sixVertexLoopFullUnitMaskOfRelated_colored middle
    hmiddle_pos hmiddle_lt profile second.1 target second.2
  dsimp only at hfirst hsecond
  apply Subtype.ext
  apply Subtype.ext
  apply sixVertexLoopDecoratedPairColored_injective
  apply fkColoredFullSwapTarget_injective_of_mask_eq
    (sixVertexFullDisagreementVertexMask firstCertificate.1)
    (sixVertexFullDisagreementVertexMask secondCertificate.1)
    (sixVertexLoopDecoratedPairColored first.1.1)
    (sixVertexLoopDecoratedPairColored second.1.1)
    (firstCertificate.2.1.fullSwapBondCoherent
      (sixVertexLoopDecoratedPairColored first.1.1) firstCertificate.1)
    (secondCertificate.2.1.fullSwapBondCoherent
      (sixVertexLoopDecoratedPairColored second.1.1) secondCertificate.1)
    (congrArg sixVertexFullDisagreementVertexMask hmask)
  exact hfirst.symm.trans hsecond

theorem card_sixVertexLoopFullMaskFineRelated_preimages_le_negativeMasks
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile) :
    (Finset.univ.filter fun source :
        SixVertexLoopDecoratedPairFineProfileFiber T
          (sixVertexHorizontalLowerSector middle hmiddle_pos)
          (sixVertexHorizontalUpperSector middle hmiddle_lt) profile =>
      SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
        profile source target).card <=
      Fintype.card (SixVertexLoopFullNegativeMask profile target) := by
  have hcard := Fintype.card_le_of_injective
    (sixVertexLoopFullNegativeMaskOfPreimage middle hmiddle_pos
      hmiddle_lt profile target)
    (sixVertexLoopFullNegativeMaskOfPreimage_injective middle hmiddle_pos
      hmiddle_lt profile target)
  simpa only [Fintype.card_subtype] using hcard



noncomputable def sixVertexLoopFullUnitMaskEquivRelated
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile) :
    SixVertexLoopFullUnitMask middle hmiddle_pos hmiddle_lt profile source ≃
      {target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile //
        SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
          profile source target} where
  toFun certificate := ⟨sixVertexLoopFullUnitMaskTarget middle hmiddle_pos
    hmiddle_lt profile source certificate,
    sixVertexLoopFullMaskFineRelated_target middle hmiddle_pos hmiddle_lt
      profile source certificate.1 certificate.2.1 certificate.2.2⟩
  invFun target := sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos
    hmiddle_lt profile source target.1 target.2
  left_inv certificate := by
    apply sixVertexLoopFullUnitMaskTarget_injective middle hmiddle_pos
      hmiddle_lt profile source
    exact (sixVertexLoopFullUnitMaskOfRelated_target middle hmiddle_pos
      hmiddle_lt profile source _ _).symm
  right_inv target := by
    apply Subtype.ext
    exact (sixVertexLoopFullUnitMaskOfRelated_target middle hmiddle_pos
      hmiddle_lt profile source target.1 target.2).symm

theorem card_sixVertexLoopFullMaskFineRelated
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile) :
    (Finset.univ.filter
      (SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
        profile source)).card =
      Fintype.card (SixVertexLoopFullUnitMask middle hmiddle_pos
        hmiddle_lt profile source) := by
  rw [← Fintype.card_subtype]
  exact (Fintype.card_congr (sixVertexLoopFullUnitMaskEquivRelated
    middle hmiddle_pos hmiddle_lt profile source)).symm



theorem sixVertexLoopFullMaskFineRelated_nonempty
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (sixVertexLoopDecoratedPairColored source.1 false).arrows
      (sixVertexLoopDecoratedPairColored source.1 true).arrows mask)
    (htransfer : sixVertexTorusMaskSeamTransfer mask
      (sixVertexLoopDecoratedPairColored source.1 false).arrows
      (sixVertexLoopDecoratedPairColored source.1 true).arrows = 1) :
    (Finset.univ.filter
      (SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
        profile source)).Nonempty := by
  refine ⟨sixVertexLoopDecoratedFullMaskFineTarget middle hmiddle_pos
    hmiddle_lt profile source mask hmask htransfer, ?_⟩
  simp [sixVertexLoopFullMaskFineRelated_target middle hmiddle_pos
    hmiddle_lt profile source mask hmask htransfer]


theorem sixVertexLoopFullMaskFineRelated_bigrade
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (hrelated : SixVertexLoopFullMaskFineRelated middle hmiddle_pos
      hmiddle_lt profile source target) :
    sixVertexLoopDecoratedPairBigrade target.1 =
      sixVertexLoopDecoratedPairBigrade source.1 := by
  obtain ⟨mask, hmask, htransfer, rfl⟩ := hrelated
  exact sixVertexLoopDecoratedFullMaskTarget_bigrade middle hmiddle_pos
    hmiddle_lt source.1 mask hmask htransfer

theorem sixVertexLoopFullMaskFineRelated_twoCycle
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (hrelated : SixVertexLoopFullMaskFineRelated middle hmiddle_pos
      hmiddle_lt profile source target) :
    sixVertexPairAtMostTwoCycleFineRelated
      ((sixVertexLoopDecoratedPairColored source.1 false).arrows,
        (sixVertexLoopDecoratedPairColored source.1 true).arrows)
      ((sixVertexLoopDecoratedPairColored target.1 false).arrows,
        (sixVertexLoopDecoratedPairColored target.1 true).arrows) := by
  let certificate := sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos
    hmiddle_lt profile source target hrelated
  have hedge := certificate.2.1.pairAtMostTwoCycleFineRelated
  rw [← sixVertexLoopFullUnitMaskOfRelated_false_arrows middle
      hmiddle_pos hmiddle_lt profile source target hrelated,
    ← sixVertexLoopFullUnitMaskOfRelated_true_arrows middle
      hmiddle_pos hmiddle_lt profile source target hrelated] at hedge
  exact hedge



theorem rawFineProfile_of_fullMaskUnitDegree
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hne : forall (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile),
      Nonempty (SixVertexLoopFullUnitMask middle hmiddle_pos
        hmiddle_lt profile source))
    (hdegree : forall
      (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
      (target : SixVertexLoopDecoratedPairFineProfileFiber
        T middle middle profile),
      SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
          profile source target ->
        (Finset.univ.filter fun otherSource =>
          SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
            profile otherSource target).card <=
          Fintype.card (SixVertexLoopFullUnitMask middle hmiddle_pos
            hmiddle_lt profile source)) :
    forall profile : SixVertexHorizontalBoundedFineRowProfile T,
      0 <= sixVertexHorizontalFineRowProfileSignedSum T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt)
        middle middle profile := by
  apply rawFineProfile_of_loopRelationEdgeDegree
    (SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt)
  · intro profile source
    obtain ⟨certificate⟩ := hne profile source
    exact sixVertexLoopFullMaskFineRelated_nonempty middle hmiddle_pos
      hmiddle_lt profile source certificate.1 certificate.2.1
        certificate.2.2
  · intro profile source target hrelated
    rw [card_sixVertexLoopFullMaskFineRelated middle hmiddle_pos
      hmiddle_lt profile source]
    exact hdegree profile source target hrelated



theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_fullMaskUnitDegree
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hne : forall (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile),
      Nonempty (SixVertexLoopFullUnitMask middle hmiddle_pos
        hmiddle_lt profile source))
    (hdegree : forall
      (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
      (target : SixVertexLoopDecoratedPairFineProfileFiber
        T middle middle profile),
      SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
          profile source target ->
        (Finset.univ.filter fun otherSource =>
          SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
            profile otherSource target).card <=
          Fintype.card (SixVertexLoopFullUnitMask middle hmiddle_pos
            hmiddle_lt profile source)) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val := by
  apply sixVertexMarkedTraceCoefficientwiseLogConcave_of_rawFineProfile
    T middle hmiddle_pos hmiddle_lt
  exact rawFineProfile_of_fullMaskUnitDegree middle hmiddle_pos hmiddle_lt
    hne hdegree




theorem rawFineProfile_of_fullMaskNegativePositiveDegree
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hne : forall (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile),
      Nonempty (SixVertexLoopFullUnitMask middle hmiddle_pos
        hmiddle_lt profile source))
    (hmaskDegree : forall
      (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
      (target : SixVertexLoopDecoratedPairFineProfileFiber
        T middle middle profile),
      SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
          profile source target ->
        Fintype.card (SixVertexLoopFullNegativeMask profile target) <=
          Fintype.card (SixVertexLoopFullUnitMask middle hmiddle_pos
            hmiddle_lt profile source)) :
    forall profile : SixVertexHorizontalBoundedFineRowProfile T,
      0 <= sixVertexHorizontalFineRowProfileSignedSum T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt)
        middle middle profile := by
  apply rawFineProfile_of_fullMaskUnitDegree middle hmiddle_pos hmiddle_lt hne
  intro profile source target hrelated
  exact (card_sixVertexLoopFullMaskFineRelated_preimages_le_negativeMasks
    middle hmiddle_pos hmiddle_lt profile target).trans
      (hmaskDegree profile source target hrelated)

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_fullMaskNegativePositiveDegree
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hne : forall (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile),
      Nonempty (SixVertexLoopFullUnitMask middle hmiddle_pos
        hmiddle_lt profile source))
    (hmaskDegree : forall
      (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
      (target : SixVertexLoopDecoratedPairFineProfileFiber
        T middle middle profile),
      SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
          profile source target ->
        Fintype.card (SixVertexLoopFullNegativeMask profile target) <=
          Fintype.card (SixVertexLoopFullUnitMask middle hmiddle_pos
            hmiddle_lt profile source)) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val := by
  apply sixVertexMarkedTraceCoefficientwiseLogConcave_of_rawFineProfile
    T middle hmiddle_pos hmiddle_lt
  exact rawFineProfile_of_fullMaskNegativePositiveDegree middle
    hmiddle_pos hmiddle_lt hne hmaskDegree

end

end StatMech.FrontierD
