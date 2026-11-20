/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDegreeTwoStrandCycleFlip
import Code.FrontierD.SixVertexPairUnionCyclePhysicalRepair










namespace StatMech.FrontierD

noncomputable section



def sixVertexDegreeTwoUnitStrandPhysicalTarget
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt)
    (hdegree : SixVertexLocallyDegreeTwo source.1.1 source.2.1)
    (seed : SixVertexOrientedDisagreementDart source.1.1 source.2.1)
    (hunit : (sixVertexDegreeTwoStrandSeamWord source.1.2.1
      source.2.2.1 hdegree seed).sum = 1) :
    SixVertexConfigurationPhysicalTarget T middle := by
  let mask := (sixVertexDegreeTwoStrandDirectedSimpleCycle
    source.1.2.1 source.2.2.1 hdegree seed).mask
  have hfirstIce : (sixVertexTorusFlip mask source.1.1).IceRule :=
    sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_ice
      source.1.2.1 source.2.2.1 hdegree seed
  have hsecondIce : (sixVertexTorusFlip mask source.2.1).IceRule :=
    sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_second_ice
      source.1.2.1 source.2.2.1 hdegree seed
  have hfirstInt :
      (sixVertexUpCount (svTorusVerticalRows T
        (sixVertexTorusFlip mask source.1.1)
        (svFinLast T.height_pos)) : Int) = middle.val := by
    rw [sixVertexTorusFlip_upCount,
      sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_seamDelta_eq_wordSum,
      hunit, source.1.2.2]
    push_cast
    omega
  have hsecondInt :
      (sixVertexUpCount (svTorusVerticalRows T
        (sixVertexTorusFlip mask source.2.1)
        (svFinLast T.height_pos)) : Int) = middle.val := by
    rw [sixVertexTorusFlip_upCount,
      sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_second_seamDelta,
      hunit, source.2.2.2]
    push_cast
    omega
  exact
    (⟨sixVertexTorusFlip mask source.1.1, hfirstIce,
      by exact_mod_cast hfirstInt⟩,
    ⟨sixVertexTorusFlip mask source.2.1, hsecondIce,
      by exact_mod_cast hsecondInt⟩)

@[simp] theorem sixVertexDegreeTwoUnitStrandPhysicalTarget_arrows
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt)
    (hdegree : SixVertexLocallyDegreeTwo source.1.1 source.2.1)
    (seed : SixVertexOrientedDisagreementDart source.1.1 source.2.1)
    (hunit : (sixVertexDegreeTwoStrandSeamWord source.1.2.1
      source.2.2.1 hdegree seed).sum = 1) :
    ((sixVertexDegreeTwoUnitStrandPhysicalTarget source hdegree seed hunit).1.1,
      (sixVertexDegreeTwoUnitStrandPhysicalTarget source hdegree seed hunit).2.1) =
      (sixVertexTorusFlip
          (sixVertexDegreeTwoStrandDirectedSimpleCycle
            source.1.2.1 source.2.2.1 hdegree seed).mask source.1.1,
        sixVertexTorusFlip
          (sixVertexDegreeTwoStrandDirectedSimpleCycle
            source.1.2.1 source.2.2.1 hdegree seed).mask source.2.1) := by
  rfl



theorem sixVertexDegreeTwoUnitStrandPhysicalTarget_horizontalUnion
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt)
    (hdegree : SixVertexLocallyDegreeTwo source.1.1 source.2.1)
    (seed : SixVertexOrientedDisagreementDart source.1.1 source.2.1)
    (hunit : (sixVertexDegreeTwoStrandSeamWord source.1.2.1
      source.2.2.1 hdegree seed).sum = 1) :
    sixVertexPairUnionHorizontal
        ((sixVertexDegreeTwoUnitStrandPhysicalTarget
          source hdegree seed hunit).1.1,
        (sixVertexDegreeTwoUnitStrandPhysicalTarget
          source hdegree seed hunit).2.1) =
      sixVertexPairUnionHorizontal (source.1.1, source.2.1) := by
  rw [sixVertexDegreeTwoUnitStrandPhysicalTarget_arrows]
  exact sixVertexPairUnionHorizontal_bothFlip_of_disagrees
    (sixVertexDegreeTwoStrandDirectedSimpleCycle_mask_disagrees
      source.1.2.1 source.2.2.1 hdegree seed)



theorem sixVertexDegreeTwoUnitStrandPhysicalTarget_verticalUnion
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt)
    (hdegree : SixVertexLocallyDegreeTwo source.1.1 source.2.1)
    (seed : SixVertexOrientedDisagreementDart source.1.1 source.2.1)
    (hunit : (sixVertexDegreeTwoStrandSeamWord source.1.2.1
      source.2.2.1 hdegree seed).sum = 1) :
    sixVertexPairUnionVertical
        ((sixVertexDegreeTwoUnitStrandPhysicalTarget
          source hdegree seed hunit).1.1,
        (sixVertexDegreeTwoUnitStrandPhysicalTarget
          source hdegree seed hunit).2.1) =
      sixVertexPairUnionVertical (source.1.1, source.2.1) := by
  rw [sixVertexDegreeTwoUnitStrandPhysicalTarget_arrows]
  exact sixVertexPairUnionVertical_bothFlip_of_disagrees
    (sixVertexDegreeTwoStrandDirectedSimpleCycle_mask_disagrees
      source.1.2.1 source.2.2.1 hdegree seed)



theorem sixVertexDegreeTwoUnitStrandPhysicalTarget_pair_related
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt)
    (hdegree : SixVertexLocallyDegreeTwo source.1.1 source.2.1)
    (seed : SixVertexOrientedDisagreementDart source.1.1 source.2.1)
    (hunit : (sixVertexDegreeTwoStrandSeamWord source.1.2.1
      source.2.2.1 hdegree seed).sum = 1) :
    sixVertexPairAtMostTwoCycleRelated (source.1.1, source.2.1)
      ((sixVertexDegreeTwoUnitStrandPhysicalTarget
        source hdegree seed hunit).1.1,
      (sixVertexDegreeTwoUnitStrandPhysicalTarget
        source hdegree seed hunit).2.1) := by
  apply sixVertexPairAtMostTwoCycleRelated_of_union_eq
  · exact (sixVertexDegreeTwoUnitStrandPhysicalTarget_horizontalUnion
      source hdegree seed hunit).symm
  · exact (sixVertexDegreeTwoUnitStrandPhysicalTarget_verticalUnion
      source hdegree seed hunit).symm



theorem sixVertexLocalBalancedFlipMask_full_of_degreeTwo
    (first second mask : SixVertexLocalIncomingPattern)
    (hdegree : (sixVertexLocalDisagreementSides first second).card = 0 ∨
      (sixVertexLocalDisagreementSides first second).card = 2)
    (hbalanced : SixVertexLocalBalancedFlipMask first mask)
    (hsupport : ∀ side, mask side = true →
      first side ≠ second side) :
    ∀ selected other, mask selected = true →
      first other ≠ second other → mask other = true := by
  simp only [sixVertexLocalDisagreementSides,
    SixVertexLocalBalancedFlipMask,
    sixVertexLocalSelectedIncomingCount,
    sixVertexLocalSwitchMaskCount,
    Finset.card_filter] at hdegree hbalanced
  decide +revert



theorem SixVertexBalancedFlipMask.fullDisagreementMask_of_degreeTwo
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hbalanced : SixVertexBalancedFlipMask omega mask)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (hsupport : ∀ edge, sixVertexTorusMaskSelects mask edge = true →
      sixVertexTorusEdgeDisagrees omega eta edge) :
    SixVertexFullDisagreementMask omega eta mask := by
  constructor
  · intro v side hselected
    rw [sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees]
    apply hsupport
    rwa [← sixVertexTorusLocalSwitchMask_apply]
  · intro v selected other hselected hother
    apply sixVertexLocalBalancedFlipMask_full_of_degreeTwo
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)
      (sixVertexTorusLocalSwitchMask mask v)
      (hdegree v) (hbalanced v) _ selected other hselected hother
    intro side hside
    rw [sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees]
    apply hsupport
    rwa [← sixVertexTorusLocalSwitchMask_apply]



theorem sixVertexTorusSwitchFirst_eq_flip_of_disagrees
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hsupport : ∀ edge, sixVertexTorusMaskSelects mask edge = true →
      sixVertexTorusEdgeDisagrees omega eta edge) :
    sixVertexTorusSwitchFirst mask omega eta =
      sixVertexTorusFlip mask omega := by
  ext base
  · by_cases hm : mask.horizontal base = true
    · have hdis := hsupport (0, base) (by
        simpa [sixVertexTorusMaskSelects] using hm)
      cases ho : omega.horizontal base <;>
        cases he : eta.horizontal base <;>
        simp [sixVertexTorusSwitchFirst, sixVertexTorusFlip,
          sixVertexTorusEdgeDisagrees, sixVertexTorusEdgeArrow,
          hm, ho, he] at hdis ⊢
    · have hmfalse := Bool.eq_false_of_not_eq_true hm
      simp [sixVertexTorusSwitchFirst, sixVertexTorusFlip, hmfalse]
  · by_cases hm : mask.vertical base = true
    · have hdis := hsupport (1, base) (by
        simpa [sixVertexTorusMaskSelects] using hm)
      cases ho : omega.vertical base <;>
        cases he : eta.vertical base <;>
        simp [sixVertexTorusSwitchFirst, sixVertexTorusFlip,
          sixVertexTorusEdgeDisagrees, sixVertexTorusEdgeArrow,
          hm, ho, he] at hdis ⊢
    · have hmfalse := Bool.eq_false_of_not_eq_true hm
      simp [sixVertexTorusSwitchFirst, sixVertexTorusFlip, hmfalse]



theorem sixVertexTorusSwitchSecond_eq_flip_of_disagrees
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hsupport : ∀ edge, sixVertexTorusMaskSelects mask edge = true →
      sixVertexTorusEdgeDisagrees omega eta edge) :
    sixVertexTorusSwitchSecond mask omega eta =
      sixVertexTorusFlip mask eta := by
  ext base
  · by_cases hm : mask.horizontal base = true
    · have hdis := hsupport (0, base) (by
        simpa [sixVertexTorusMaskSelects] using hm)
      cases ho : omega.horizontal base <;>
        cases he : eta.horizontal base <;>
        simp [sixVertexTorusSwitchSecond, sixVertexTorusFlip,
          sixVertexTorusEdgeDisagrees, sixVertexTorusEdgeArrow,
          hm, ho, he] at hdis ⊢
    · have hmfalse := Bool.eq_false_of_not_eq_true hm
      simp [sixVertexTorusSwitchSecond, sixVertexTorusFlip, hmfalse]
  · by_cases hm : mask.vertical base = true
    · have hdis := hsupport (1, base) (by
        simpa [sixVertexTorusMaskSelects] using hm)
      cases ho : omega.vertical base <;>
        cases he : eta.vertical base <;>
        simp [sixVertexTorusSwitchSecond, sixVertexTorusFlip,
          sixVertexTorusEdgeDisagrees, sixVertexTorusEdgeArrow,
          hm, ho, he] at hdis ⊢
    · have hmfalse := Bool.eq_false_of_not_eq_true hm
      simp [sixVertexTorusSwitchSecond, sixVertexTorusFlip, hmfalse]




theorem sixVertexTorusMaskSeamTransfer_eq_flipSeamDelta_of_disagrees
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hsupport : ∀ edge, sixVertexTorusMaskSelects mask edge = true →
      sixVertexTorusEdgeDisagrees omega eta edge) :
    sixVertexTorusMaskSeamTransfer mask omega eta =
      sixVertexTorusFlipSeamDelta mask omega := by
  unfold sixVertexTorusMaskSeamTransfer sixVertexTorusFlipSeamDelta
  apply Finset.sum_congr rfl
  intro column _
  by_cases hm : mask.vertical (column, svFinLast T.height_pos) = true
  · have hdis := hsupport
      (1, (column, svFinLast T.height_pos)) (by
        simpa [sixVertexTorusMaskSelects] using hm)
    cases ho : omega.vertical (column, svFinLast T.height_pos) <;>
      cases he : eta.vertical (column, svFinLast T.height_pos) <;>
      simp_all [sixVertexTorusFlip, sixVertexTorusEdgeDisagrees,
        sixVertexTorusEdgeArrow]
  · have hmfalse := Bool.eq_false_of_not_eq_true hm
    simp [sixVertexTorusFlip, hmfalse]



theorem sixVertexDegreeTwoUnitStrandPhysicalTarget_fine
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt)
    (hdegree : SixVertexLocallyDegreeTwo source.1.1 source.2.1)
    (seed : SixVertexOrientedDisagreementDart source.1.1 source.2.1)
    (hunit : (sixVertexDegreeTwoStrandSeamWord source.1.2.1
      source.2.2.1 hdegree seed).sum = 1) :
    sixVertexHorizontalPairBoundedFineRowProfile
        (source.1.1.horizontal, source.2.1.horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile
        ((sixVertexDegreeTwoUnitStrandPhysicalTarget
          source hdegree seed hunit).1.1.horizontal,
        (sixVertexDegreeTwoUnitStrandPhysicalTarget
          source hdegree seed hunit).2.1.horizontal) := by
  let mask := (sixVertexDegreeTwoStrandDirectedSimpleCycle
    source.1.2.1 source.2.2.1 hdegree seed).mask
  have hsupport :=
    sixVertexDegreeTwoStrandDirectedSimpleCycle_mask_disagrees
      source.1.2.1 source.2.2.1 hdegree seed
  have hbalanced : SixVertexBalancedFlipMask source.1.1 mask :=
    sixVertexBalancedFlipMask_of_ice_flip source.1.2.1
      (sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_ice
        source.1.2.1 source.2.2.1 hdegree seed)
  have hfull := hbalanced.fullDisagreementMask_of_degreeTwo
    hdegree hsupport
  have hfine := hfull.boundedFineRowProfile
  rw [sixVertexTorusSwitchFirst_eq_flip_of_disagrees hsupport,
    sixVertexTorusSwitchSecond_eq_flip_of_disagrees hsupport] at hfine
  change sixVertexHorizontalPairBoundedFineRowProfile
      (source.1.1.horizontal, source.2.1.horizontal) =
    sixVertexHorizontalPairBoundedFineRowProfile
      ((sixVertexTorusFlip mask source.1.1).horizontal,
        (sixVertexTorusFlip mask source.2.1).horizontal)
  exact hfine.symm



theorem sixVertexDegreeTwoUnitStrandPhysicalTarget_fineRelated
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt)
    (hdegree : SixVertexLocallyDegreeTwo source.1.1 source.2.1)
    (seed : SixVertexOrientedDisagreementDart source.1.1 source.2.1)
    (hunit : (sixVertexDegreeTwoStrandSeamWord source.1.2.1
      source.2.2.1 hdegree seed).sum = 1) :
    sixVertexPairAtMostTwoCycleFineRelated (source.1.1, source.2.1)
      ((sixVertexDegreeTwoUnitStrandPhysicalTarget
        source hdegree seed hunit).1.1,
      (sixVertexDegreeTwoUnitStrandPhysicalTarget
        source hdegree seed hunit).2.1) :=
  ⟨sixVertexDegreeTwoUnitStrandPhysicalTarget_pair_related
      source hdegree seed hunit,
    sixVertexDegreeTwoUnitStrandPhysicalTarget_fine
      source hdegree seed hunit⟩


theorem sixVertexTorusBothFlip_injective
    {T : EvenTorus} (mask : SixVertexArrows T) :
    Function.Injective (fun pair : SixVertexArrows T × SixVertexArrows T =>
      (sixVertexTorusFlip mask pair.1,
        sixVertexTorusFlip mask pair.2)) := by
  intro first second heq
  apply Prod.ext
  · have hfirst := congrArg (fun pair => pair.1) heq
    have := congrArg (sixVertexTorusFlip mask) hfirst
    simpa using this
  · have hsecond := congrArg (fun pair => pair.2) heq
    have := congrArg (sixVertexTorusFlip mask) hsecond
    simpa using this




theorem sixVertexDegreeTwoUnitStrandPhysicalTarget_recover_of_mask_eq
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (first second : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt)
    (hdegreeFirst : SixVertexLocallyDegreeTwo first.1.1 first.2.1)
    (hdegreeSecond : SixVertexLocallyDegreeTwo second.1.1 second.2.1)
    (seedFirst : SixVertexOrientedDisagreementDart first.1.1 first.2.1)
    (seedSecond : SixVertexOrientedDisagreementDart second.1.1 second.2.1)
    (hunitFirst : (sixVertexDegreeTwoStrandSeamWord first.1.2.1
      first.2.2.1 hdegreeFirst seedFirst).sum = 1)
    (hunitSecond : (sixVertexDegreeTwoStrandSeamWord second.1.2.1
      second.2.2.1 hdegreeSecond seedSecond).sum = 1)
    (hmask : (sixVertexDegreeTwoStrandDirectedSimpleCycle
        first.1.2.1 first.2.2.1 hdegreeFirst seedFirst).mask =
      (sixVertexDegreeTwoStrandDirectedSimpleCycle
        second.1.2.1 second.2.2.1 hdegreeSecond seedSecond).mask)
    (htarget : sixVertexDegreeTwoUnitStrandPhysicalTarget first
        hdegreeFirst seedFirst hunitFirst =
      sixVertexDegreeTwoUnitStrandPhysicalTarget second
        hdegreeSecond seedSecond hunitSecond) :
    first = second := by
  have harrows := congrArg (fun target => (target.1.1, target.2.1)) htarget
  change
    ((sixVertexDegreeTwoUnitStrandPhysicalTarget first hdegreeFirst
        seedFirst hunitFirst).1.1,
      (sixVertexDegreeTwoUnitStrandPhysicalTarget first hdegreeFirst
        seedFirst hunitFirst).2.1) =
    ((sixVertexDegreeTwoUnitStrandPhysicalTarget second hdegreeSecond
        seedSecond hunitSecond).1.1,
      (sixVertexDegreeTwoUnitStrandPhysicalTarget second hdegreeSecond
        seedSecond hunitSecond).2.1) at harrows
  rw [sixVertexDegreeTwoUnitStrandPhysicalTarget_arrows,
    sixVertexDegreeTwoUnitStrandPhysicalTarget_arrows, ← hmask] at harrows
  have hsource : (first.1.1, first.2.1) = (second.1.1, second.2.1) :=
    sixVertexTorusBothFlip_injective _ harrows
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg Prod.fst hsource
  · exact congrArg Prod.snd hsource


theorem sixVertexDegreeTwoUnitStrandPhysicalTarget_layers_ne
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt)
    (hdegree : SixVertexLocallyDegreeTwo source.1.1 source.2.1)
    (seed : SixVertexOrientedDisagreementDart source.1.1 source.2.1)
    (hunit : (sixVertexDegreeTwoStrandSeamWord source.1.2.1
      source.2.2.1 hdegree seed).sum = 1) :
    (sixVertexDegreeTwoUnitStrandPhysicalTarget
      source hdegree seed hunit).1 ≠
      (sixVertexDegreeTwoUnitStrandPhysicalTarget
        source hdegree seed hunit).2 := by
  intro hlayers
  have harrows := congrArg Subtype.val hlayers
  rw [show
      (sixVertexDegreeTwoUnitStrandPhysicalTarget
        source hdegree seed hunit).1.1 =
        sixVertexTorusFlip
          (sixVertexDegreeTwoStrandDirectedSimpleCycle
            source.1.2.1 source.2.2.1 hdegree seed).mask source.1.1 by rfl,
    show
      (sixVertexDegreeTwoUnitStrandPhysicalTarget
        source hdegree seed hunit).2.1 =
        sixVertexTorusFlip
          (sixVertexDegreeTwoStrandDirectedSimpleCycle
            source.1.2.1 source.2.2.1 hdegree seed).mask source.2.1 by rfl]
    at harrows
  have hsource := congrArg
    (sixVertexTorusFlip
      (sixVertexDegreeTwoStrandDirectedSimpleCycle
        source.1.2.1 source.2.2.1 hdegree seed).mask) harrows
  have hsourceArrows : source.1.1 = source.2.1 := by simpa using hsource
  have hcount := congrArg (fun arrows => sixVertexUpCount
    (svTorusVerticalRows T arrows (svFinLast T.height_pos))) hsourceArrows
  change sixVertexUpCount
      (svTorusVerticalRows T source.1.1 (svFinLast T.height_pos)) =
    sixVertexUpCount
      (svTorusVerticalRows T source.2.1 (svFinLast T.height_pos)) at hcount
  rw [source.1.2.2, source.2.2.2] at hcount
  change middle.val - 1 = middle.val + 1 at hcount
  omega

end

end StatMech.FrontierD
