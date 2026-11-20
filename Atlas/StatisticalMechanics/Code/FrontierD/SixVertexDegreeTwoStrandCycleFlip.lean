/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDegreeTwoStrandDirectedCycle
import Code.FrontierD.SixVertexDirectedSimpleCycleFlip










namespace StatMech.FrontierD

noncomputable section

local instance sixVertexStrandCycleFlipSameCycleDecidable
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    DecidableRel
      (sixVertexOrientedDegreeTwoStrandSuccessor
        homega heta hdegree).SameCycle :=
  Classical.decRel _



theorem sixVertexDirectedTorusEdgeOfArrow_follows
    {T : EvenTorus} (omega : SixVertexArrows T)
    (edge : SixVertexTorusEdge T) :
    (sixVertexDirectedTorusEdgeOfArrow omega edge).Follows omega := by
  rcases edge with ⟨direction, base⟩
  fin_cases direction <;>
    simp [sixVertexDirectedTorusEdgeOfArrow,
      SixVertexDirectedTorusEdge.Follows]



theorem sixVertexDegreeTwoStrandDirectedSimpleCycle_follows
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    (sixVertexDegreeTwoStrandDirectedSimpleCycle
      homega heta hdegree seed).Follows omega := by
  intro i
  exact sixVertexDirectedTorusEdgeOfArrow_follows omega
    (sixVertexTorusDartEdge T
      (sixVertexDegreeTwoLocalMate hdegree
      (sixVertexDegreeTwoStrandCycleEnumeration
          homega heta hdegree seed i).1).1)



theorem sixVertexDegreeTwoStrandCycleEnumeration_eq_pow
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta)
    (i : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed))) :
    sixVertexDegreeTwoStrandCycleEnumeration
        homega heta hdegree seed i =
      ((sixVertexOrientedDegreeTwoStrandSuccessor
        homega heta hdegree) ^ i.val) seed := by
  change ((sixVertexDegreeTwoStrandCyclePerm
      homega heta hdegree seed) ^ i.val) seed = _
  exact Equiv.Perm.cycleOf_pow_apply_self
    (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree) seed i.val



theorem sixVertexDirectedTorusEdgeOfArrow_seamFlow_of_disagrees
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (edge : SixVertexTorusEdge T)
    (hdisagrees : sixVertexTorusEdgeDisagrees omega eta edge) :
    (∑ column : Fin T.width,
      (sixVertexDirectedTorusEdgeOfArrow omega edge).verticalFlow
        (column, svFinLast T.height_pos)) =
      -sixVertexTorusEdgeSeamSign omega eta edge := by
  rcases edge with ⟨direction, ⟨edgeColumn, edgeRow⟩⟩
  fin_cases direction
  · simp [sixVertexDirectedTorusEdgeOfArrow,
      SixVertexDirectedTorusEdge.verticalFlow,
      sixVertexTorusEdgeSeamSign]
  · have homega_ne : omega.vertical (edgeColumn, edgeRow) ≠
        eta.vertical (edgeColumn, edgeRow) := by
      simpa [sixVertexTorusEdgeDisagrees, sixVertexTorusEdgeArrow] using
        hdisagrees
    by_cases hrow : edgeRow = svFinLast T.height_pos
    · subst edgeRow
      cases homegaBit : omega.vertical
          (edgeColumn, svFinLast T.height_pos) <;>
        cases hetaBit : eta.vertical
          (edgeColumn, svFinLast T.height_pos) <;>
        simp_all [sixVertexDirectedTorusEdgeOfArrow,
          SixVertexDirectedTorusEdge.verticalFlow,
          sixVertexTorusEdgeSeamSign]
    · simp [sixVertexDirectedTorusEdgeOfArrow,
        SixVertexDirectedTorusEdge.verticalFlow,
        sixVertexTorusEdgeSeamSign, hrow, Ne.symm hrow]



theorem sixVertexDegreeTwoOrientedStrandEdge_seamFlow
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : SixVertexOrientedDisagreementDart omega eta) :
    (∑ column : Fin T.width,
      (sixVertexDegreeTwoOrientedStrandEdge hdegree dart).verticalFlow
        (column, svFinLast T.height_pos)) =
      -sixVertexDegreeTwoStrandStepSeamSign hdegree dart := by
  exact sixVertexDirectedTorusEdgeOfArrow_seamFlow_of_disagrees
    (sixVertexTorusDartEdge T
      (sixVertexDegreeTwoLocalMate hdegree dart.1).1)
    (sixVertexDegreeTwoLocalMate hdegree dart.1).2



theorem sixVertexDegreeTwoStrandDirectedSimpleCycle_seamFlow
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    (∑ column : Fin T.width,
      (sixVertexDegreeTwoStrandDirectedSimpleCycle
        homega heta hdegree seed).verticalFlow
          (column, svFinLast T.height_pos)) =
      -∑ i, sixVertexDegreeTwoStrandStepSeamSign hdegree
        (sixVertexDegreeTwoStrandCycleEnumeration
          homega heta hdegree seed i) := by
  simp only [SixVertexDirectedSimpleCycle.verticalFlow,
    sixVertexDegreeTwoStrandDirectedSimpleCycle,
    sixVertexDegreeTwoDirectedSimpleCycleOfEnumeration]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact sixVertexDegreeTwoOrientedStrandEdge_seamFlow
    hdegree
      (sixVertexDegreeTwoStrandCycleEnumeration
        homega heta hdegree seed i)



private theorem sum_filter_ne_zero (steps : List Int) :
    (steps.filter fun z => z ≠ 0).sum = steps.sum := by
  rw [show steps.filter (fun z => z ≠ 0) =
      steps.filter intKeepNonzero by
    apply List.filter_congr
    intro z _
    simp [intKeepNonzero]]
  exact sum_filter_intKeepNonzero steps



theorem sixVertexDegreeTwoStrandSeamWord_sum_eq_cycleEnumeration
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    (sixVertexDegreeTwoStrandSeamWord
      homega heta hdegree seed).sum =
      ∑ i, sixVertexDegreeTwoStrandStepSeamSign hdegree
        (sixVertexDegreeTwoStrandCycleEnumeration
          homega heta hdegree seed i) := by
  unfold sixVertexDegreeTwoStrandSeamWord
  rw [sum_filter_ne_zero]
  simp only [sixVertexDegreeTwoOrderedStrand,
    List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  rw [sixVertexDegreeTwoStrandCycleEnumeration_eq_pow]
  rfl



theorem sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_seamDelta
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    sixVertexTorusFlipSeamDelta
        (sixVertexDegreeTwoStrandDirectedSimpleCycle
          homega heta hdegree seed).mask omega =
      ∑ i, sixVertexDegreeTwoStrandStepSeamSign hdegree
        (sixVertexDegreeTwoStrandCycleEnumeration
          homega heta hdegree seed i) := by
  rw [(sixVertexDegreeTwoStrandDirectedSimpleCycle
      homega heta hdegree seed).flip_seamDelta omega
    (sixVertexDegreeTwoStrandDirectedSimpleCycle_follows
      homega heta hdegree seed)]
  rw [sixVertexDegreeTwoStrandDirectedSimpleCycle_seamFlow]
  simp



theorem sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_seamDelta_eq_wordSum
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    sixVertexTorusFlipSeamDelta
        (sixVertexDegreeTwoStrandDirectedSimpleCycle
          homega heta hdegree seed).mask omega =
      (sixVertexDegreeTwoStrandSeamWord
        homega heta hdegree seed).sum := by
  rw [sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_seamDelta,
    sixVertexDegreeTwoStrandSeamWord_sum_eq_cycleEnumeration]



theorem sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_ice
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    (sixVertexTorusFlip
      (sixVertexDegreeTwoStrandDirectedSimpleCycle
        homega heta hdegree seed).mask omega).IceRule :=
  (sixVertexDegreeTwoStrandDirectedSimpleCycle
    homega heta hdegree seed).flip_ice omega homega
      (sixVertexDegreeTwoStrandDirectedSimpleCycle_follows
        homega heta hdegree seed)



theorem sixVertexDegreeTwoStrandDirectedSimpleCycle_mask_disagrees
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta)
    (edge : SixVertexTorusEdge T)
    (hselected : sixVertexTorusMaskSelects
      (sixVertexDegreeTwoStrandDirectedSimpleCycle
        homega heta hdegree seed).mask edge = true) :
    sixVertexTorusEdgeDisagrees omega eta edge := by
  rcases edge with ⟨direction, base⟩
  fin_cases direction
  · have hmask :
        (sixVertexDegreeTwoStrandDirectedSimpleCycle
          homega heta hdegree seed).mask.horizontal base = true := by
      simpa [sixVertexTorusMaskSelects] using hselected
    obtain ⟨i, hi⟩ :=
      ((sixVertexDegreeTwoStrandDirectedSimpleCycle
        homega heta hdegree seed).mask_horizontal base).1 hmask
    have hedge : sixVertexTorusDartEdge T
        (sixVertexDegreeTwoLocalMate hdegree
          (sixVertexDegreeTwoStrandCycleEnumeration
            homega heta hdegree seed i).1).1 = (0, base) := by
      apply sixVertexDirectedTorusEdgeOfArrow_physical_injective omega
      simpa [sixVertexDegreeTwoStrandDirectedSimpleCycle,
        sixVertexDegreeTwoDirectedSimpleCycleOfEnumeration,
        sixVertexDegreeTwoOrientedStrandEdge,
        sixVertexDirectedTorusEdgeOfArrow,
        SixVertexDirectedTorusEdge.physical] using hi
    change sixVertexTorusEdgeDisagrees omega eta (0, base)
    rw [← hedge]
    exact (sixVertexDegreeTwoLocalMate hdegree
      (sixVertexDegreeTwoStrandCycleEnumeration
        homega heta hdegree seed i).1).2
  · have hmask :
        (sixVertexDegreeTwoStrandDirectedSimpleCycle
          homega heta hdegree seed).mask.vertical base = true := by
      simpa [sixVertexTorusMaskSelects] using hselected
    obtain ⟨i, hi⟩ :=
      ((sixVertexDegreeTwoStrandDirectedSimpleCycle
        homega heta hdegree seed).mask_vertical base).1 hmask
    have hedge : sixVertexTorusDartEdge T
        (sixVertexDegreeTwoLocalMate hdegree
          (sixVertexDegreeTwoStrandCycleEnumeration
            homega heta hdegree seed i).1).1 = (1, base) := by
      apply sixVertexDirectedTorusEdgeOfArrow_physical_injective omega
      simpa [sixVertexDegreeTwoStrandDirectedSimpleCycle,
        sixVertexDegreeTwoDirectedSimpleCycleOfEnumeration,
        sixVertexDegreeTwoOrientedStrandEdge,
        sixVertexDirectedTorusEdgeOfArrow,
        SixVertexDirectedTorusEdge.physical] using hi
    change sixVertexTorusEdgeDisagrees omega eta (1, base)
    rw [← hedge]
    exact (sixVertexDegreeTwoLocalMate hdegree
      (sixVertexDegreeTwoStrandCycleEnumeration
        homega heta hdegree seed i).1).2



theorem sixVertexLocalBalancedFlipMask_transfer_of_disagrees
    (first second mask : SixVertexLocalIncomingPattern)
    (hbalanced : SixVertexLocalBalancedFlipMask first mask)
    (hdisagrees : ∀ side, mask side = true →
      first side ≠ second side) :
    SixVertexLocalBalancedFlipMask second mask := by
  simp only [SixVertexLocalBalancedFlipMask,
    sixVertexLocalSelectedIncomingCount,
    sixVertexLocalSwitchMaskCount] at hbalanced ⊢
  decide +revert



theorem SixVertexBalancedFlipMask.transfer_of_disagrees
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hbalanced : SixVertexBalancedFlipMask omega mask)
    (hdisagrees : ∀ edge, sixVertexTorusMaskSelects mask edge = true →
      sixVertexTorusEdgeDisagrees omega eta edge) :
    SixVertexBalancedFlipMask eta mask := by
  intro v
  apply sixVertexLocalBalancedFlipMask_transfer_of_disagrees
    (sixVertexLocalIncomingPattern omega v)
    (sixVertexLocalIncomingPattern eta v)
    (sixVertexTorusLocalSwitchMask mask v) (hbalanced v)
  intro side hselected
  rw [sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees]
  apply hdisagrees
  rwa [← sixVertexTorusLocalSwitchMask_apply]



theorem sixVertexDegreeTwoStrandDirectedSimpleCycle_mask_balanced_second
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    SixVertexBalancedFlipMask eta
      (sixVertexDegreeTwoStrandDirectedSimpleCycle
        homega heta hdegree seed).mask := by
  let cycle := sixVertexDegreeTwoStrandDirectedSimpleCycle
    homega heta hdegree seed
  have hfirst : SixVertexBalancedFlipMask omega cycle.mask :=
    sixVertexBalancedFlipMask_of_ice_flip homega
      (sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_ice
        homega heta hdegree seed)
  exact hfirst.transfer_of_disagrees
    (sixVertexDegreeTwoStrandDirectedSimpleCycle_mask_disagrees
      homega heta hdegree seed)



theorem sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_second_ice
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    (sixVertexTorusFlip
      (sixVertexDegreeTwoStrandDirectedSimpleCycle
        homega heta hdegree seed).mask eta).IceRule :=
  sixVertexTorusFlip_ice_of_balanced heta
    (sixVertexDegreeTwoStrandDirectedSimpleCycle_mask_balanced_second
      homega heta hdegree seed)



theorem sixVertexTorusFlipSeamDelta_eq_neg_of_disagrees
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hdisagrees : ∀ edge, sixVertexTorusMaskSelects mask edge = true →
      sixVertexTorusEdgeDisagrees omega eta edge) :
    sixVertexTorusFlipSeamDelta mask eta =
      -sixVertexTorusFlipSeamDelta mask omega := by
  unfold sixVertexTorusFlipSeamDelta
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro column _
  have hdis := hdisagrees
    (1, (column, svFinLast T.height_pos))
  cases hm : mask.vertical (column, svFinLast T.height_pos) <;>
    cases ho : omega.vertical (column, svFinLast T.height_pos) <;>
    cases he : eta.vertical (column, svFinLast T.height_pos) <;>
    simp [sixVertexTorusFlip, sixVertexTorusMaskSelects,
      sixVertexTorusEdgeDisagrees, sixVertexTorusEdgeArrow,
      hm, ho, he] at hdis ⊢



theorem sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_second_seamDelta
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    sixVertexTorusFlipSeamDelta
        (sixVertexDegreeTwoStrandDirectedSimpleCycle
          homega heta hdegree seed).mask eta =
      -(sixVertexDegreeTwoStrandSeamWord
        homega heta hdegree seed).sum := by
  rw [sixVertexTorusFlipSeamDelta_eq_neg_of_disagrees
      (sixVertexDegreeTwoStrandDirectedSimpleCycle_mask_disagrees
        homega heta hdegree seed),
    sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_seamDelta_eq_wordSum]



theorem sixVertexPairUnionHorizontal_bothFlip_of_disagrees
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hdisagrees : ∀ edge, sixVertexTorusMaskSelects mask edge = true →
      sixVertexTorusEdgeDisagrees omega eta edge) :
    sixVertexPairUnionHorizontal
        (sixVertexTorusFlip mask omega, sixVertexTorusFlip mask eta) =
      sixVertexPairUnionHorizontal (omega, eta) := by
  funext base
  by_cases hm : mask.horizontal base = true
  · have hdis := hdisagrees (0, base) (by
      simpa [sixVertexTorusMaskSelects] using hm)
    cases ho : omega.horizontal base <;>
      cases he : eta.horizontal base <;>
      simp [sixVertexPairUnionHorizontal, sixVertexTorusFlip,
        sixVertexTorusEdgeDisagrees, sixVertexTorusEdgeArrow,
        hm, ho, he] at hdis ⊢
  · have hmfalse := Bool.eq_false_of_not_eq_true hm
    simp [sixVertexPairUnionHorizontal, sixVertexTorusFlip, hmfalse]



theorem sixVertexPairUnionVertical_bothFlip_of_disagrees
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hdisagrees : ∀ edge, sixVertexTorusMaskSelects mask edge = true →
      sixVertexTorusEdgeDisagrees omega eta edge) :
    sixVertexPairUnionVertical
        (sixVertexTorusFlip mask omega, sixVertexTorusFlip mask eta) =
      sixVertexPairUnionVertical (omega, eta) := by
  funext base
  by_cases hm : mask.vertical base = true
  · have hdis := hdisagrees (1, base) (by
      simpa [sixVertexTorusMaskSelects] using hm)
    cases ho : omega.vertical base <;>
      cases he : eta.vertical base <;>
      simp [sixVertexPairUnionVertical, sixVertexTorusFlip,
        sixVertexTorusEdgeDisagrees, sixVertexTorusEdgeArrow,
        hm, ho, he] at hdis ⊢
  · have hmfalse := Bool.eq_false_of_not_eq_true hm
    simp [sixVertexPairUnionVertical, sixVertexTorusFlip, hmfalse]



theorem sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_pair_related
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    sixVertexPairAtMostTwoCycleRelated (omega, eta)
      (sixVertexTorusFlip
        (sixVertexDegreeTwoStrandDirectedSimpleCycle
          homega heta hdegree seed).mask omega, eta) :=
  (sixVertexDegreeTwoStrandDirectedSimpleCycle
    homega heta hdegree seed).flip_first_pair_related omega eta
      (sixVertexDegreeTwoStrandDirectedSimpleCycle_follows
        homega heta hdegree seed)

end

end StatMech.FrontierD
