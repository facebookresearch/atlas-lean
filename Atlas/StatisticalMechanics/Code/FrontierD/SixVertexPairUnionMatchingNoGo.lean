/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexPairTwoCycleCompletionHall











namespace StatMech.FrontierD

noncomputable section



def sixVertexPairSwitchMaskToTarget
    {T : EvenTorus}
    (source target : SixVertexArrows T × SixVertexArrows T) :
    SixVertexArrows T where
  horizontal v := decide
    (source.1.horizontal v ≠ target.1.horizontal v)
  vertical v := decide
    (source.1.vertical v ≠ target.1.vertical v)




theorem sixVertexPairSwitch_eq_target_of_union_eq
    {T : EvenTorus}
    (source target : SixVertexArrows T × SixVertexArrows T)
    (hhorizontal : sixVertexPairUnionHorizontal source =
      sixVertexPairUnionHorizontal target)
    (hvertical : sixVertexPairUnionVertical source =
      sixVertexPairUnionVertical target) :
    sixVertexTorusSwitchFirst
          (sixVertexPairSwitchMaskToTarget source target)
          source.1 source.2 = target.1 /\
      sixVertexTorusSwitchSecond
          (sixVertexPairSwitchMaskToTarget source target)
          source.1 source.2 = target.2 := by
  constructor <;> apply SixVertexArrows.ext
  · funext v
    have h := congrFun hhorizontal v
    unfold sixVertexPairUnionHorizontal at h
    generalize hs₁ : source.1.horizontal v = s₁ at h ⊢
    generalize hs₂ : source.2.horizontal v = s₂ at h ⊢
    generalize ht₁ : target.1.horizontal v = t₁ at h ⊢
    generalize ht₂ : target.2.horizontal v = t₂ at h ⊢
    cases s₁ <;> cases s₂ <;> cases t₁ <;> cases t₂ <;>
      simp_all [sixVertexTorusSwitchFirst,
        sixVertexPairSwitchMaskToTarget]
  · funext v
    have h := congrFun hvertical v
    unfold sixVertexPairUnionVertical at h
    generalize hs₁ : source.1.vertical v = s₁ at h ⊢
    generalize hs₂ : source.2.vertical v = s₂ at h ⊢
    generalize ht₁ : target.1.vertical v = t₁ at h ⊢
    generalize ht₂ : target.2.vertical v = t₂ at h ⊢
    cases s₁ <;> cases s₂ <;> cases t₁ <;> cases t₂ <;>
      simp_all [sixVertexTorusSwitchFirst,
        sixVertexPairSwitchMaskToTarget]
  · funext v
    have h := congrFun hhorizontal v
    unfold sixVertexPairUnionHorizontal at h
    generalize hs₁ : source.1.horizontal v = s₁ at h ⊢
    generalize hs₂ : source.2.horizontal v = s₂ at h ⊢
    generalize ht₁ : target.1.horizontal v = t₁ at h ⊢
    generalize ht₂ : target.2.horizontal v = t₂ at h ⊢
    cases s₁ <;> cases s₂ <;> cases t₁ <;> cases t₂ <;>
      simp_all [sixVertexTorusSwitchSecond,
        sixVertexPairSwitchMaskToTarget]
  · funext v
    have h := congrFun hvertical v
    unfold sixVertexPairUnionVertical at h
    generalize hs₁ : source.1.vertical v = s₁ at h ⊢
    generalize hs₂ : source.2.vertical v = s₂ at h ⊢
    generalize ht₁ : target.1.vertical v = t₁ at h ⊢
    generalize ht₂ : target.2.vertical v = t₂ at h ⊢
    cases s₁ <;> cases s₂ <;> cases t₁ <;> cases t₂ <;>
      simp_all [sixVertexTorusSwitchSecond,
        sixVertexPairSwitchMaskToTarget]



theorem sixVertexFourByTwo_no_unionEqual_middlePair
    (alpha beta : SixVertexArrows sixVertexFourByTwoTorus)
    (halphaIce : alpha.IceRule) (hbetaIce : beta.IceRule)
    (halphaSector : sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByTwoTorus alpha
        (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1)
    (hhorizontal : sixVertexPairUnionHorizontal
        (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows) =
      sixVertexPairUnionHorizontal (alpha, beta))
    (hvertical : sixVertexPairUnionVertical
        (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows) =
      sixVertexPairUnionVertical (alpha, beta)) : False := by
  let source :=
    (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows)
  let target := (alpha, beta)
  let mask := sixVertexPairSwitchMaskToTarget source target
  obtain ⟨hfirst, hsecond⟩ :=
    sixVertexPairSwitch_eq_target_of_union_eq
      source target hhorizontal hvertical
  apply sixVertexFourByTwo_no_icePairSwitch_to_middle mask
  rw [hfirst, hsecond]
  exact ⟨halphaIce, hbetaIce, halphaSector⟩

def sixVertexFourByTwoSectorZero :
    Fin (sixVertexFourByTwoTorus.width + 1) :=
  ⟨0, by norm_num [sixVertexFourByTwoTorus]⟩

def sixVertexFourByTwoSectorOne :
    Fin (sixVertexFourByTwoTorus.width + 1) :=
  ⟨1, by norm_num [sixVertexFourByTwoTorus]⟩

def sixVertexFourByTwoSectorTwo :
    Fin (sixVertexFourByTwoTorus.width + 1) :=
  ⟨2, by norm_num [sixVertexFourByTwoTorus]⟩

def sixVertexFourByTwoLowConfiguration :
    SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorZero :=
  ⟨sixVertexFourByTwoLowArrows,
    sixVertexFourByTwoLowArrows_ice,
    sixVertexFourByTwoLowArrows_seamCount⟩

def sixVertexFourByTwoHighConfiguration :
    SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorTwo :=
  ⟨sixVertexFourByTwoHighArrows,
    sixVertexFourByTwoHighArrows_ice,
    sixVertexFourByTwoHighArrows_seamCount⟩

def sixVertexFourByTwoSourceFineProfile :
    SixVertexHorizontalBoundedFineRowProfile sixVertexFourByTwoTorus :=
  sixVertexHorizontalPairBoundedFineRowProfile
    (sixVertexFourByTwoLowArrows.horizontal,
      sixVertexFourByTwoHighArrows.horizontal)

def sixVertexFourByTwoSourceFineProfilePair :
    SixVertexConfigurationPairFineProfileFiber sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorTwo
      sixVertexFourByTwoSourceFineProfile :=
  ⟨(sixVertexFourByTwoLowConfiguration,
      sixVertexFourByTwoHighConfiguration), rfl⟩



theorem sixVertexFourByTwo_not_completionUnionMatching :
    ¬ SixVertexHorizontalFineProfileCompletionUnionMatching
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorZero
      sixVertexFourByTwoSectorOne sixVertexFourByTwoSectorTwo := by
  intro hmatching
  obtain ⟨matching, _, hpreserves⟩ :=
    hmatching sixVertexFourByTwoSourceFineProfile
  let source :=
    sixVertexConfigurationPairFineProfileFiberEquivHorizontalCompletions
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorZero
      sixVertexFourByTwoSectorTwo sixVertexFourByTwoSourceFineProfile
      sixVertexFourByTwoSourceFineProfilePair
  let target := matching source
  have hunion := hpreserves source
  have hsourceArrows :=
    sixVertexFineProfileCompletionPairArrows_equiv
      sixVertexFourByTwoSourceFineProfilePair
  change sixVertexHorizontalFineProfileCompletionPairArrows source =
      (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows) at hsourceArrows
  unfold SixVertexHorizontalFineProfileCompletionPairUnionEqual at hunion
  rw [hsourceArrows] at hunion
  apply sixVertexFourByTwo_no_unionEqual_middlePair
    (sixVertexHorizontalFineProfileCompletionPairArrows target).1
    (sixVertexHorizontalFineProfileCompletionPairArrows target).2
  · exact target.2.1.1.2
  · exact target.2.2.1.2
  · exact target.2.1.2
  · exact hunion.1
  · exact hunion.2

end

end StatMech.FrontierD
