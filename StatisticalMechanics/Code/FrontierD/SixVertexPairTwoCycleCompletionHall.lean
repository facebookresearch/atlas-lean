/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexPairTwoCycleHall











namespace StatMech.FrontierD

noncomputable section

local instance instDecidablePropTwoCycleCompletionHall (p : Prop) :
    Decidable p := Classical.propDecidable p


abbrev SixVertexHorizontalFineProfilePair
    (T : EvenTorus) (profile : SixVertexHorizontalBoundedFineRowProfile T) :=
  {horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T //
    sixVertexHorizontalPairBoundedFineRowProfile horizontal = profile}



abbrev SixVertexHorizontalFineProfileCompletionPair
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (profile : SixVertexHorizontalBoundedFineRowProfile T) :=
  Sigma fun horizontal : SixVertexHorizontalFineProfilePair T profile =>
    SixVertexHorizontalSectorCompletion T left horizontal.1.1 ×
      SixVertexHorizontalSectorCompletion T right horizontal.1.2



def sixVertexHorizontalFineProfileCompletionPairArrows
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    {profile : SixVertexHorizontalBoundedFineRowProfile T}
    (completed : SixVertexHorizontalFineProfileCompletionPair
      T left right profile) : SixVertexArrows T × SixVertexArrows T :=
  (sixVertexArrowsOfFields completed.1.1.1 completed.2.1.1.1,
    sixVertexArrowsOfFields completed.1.1.2 completed.2.2.1.1)



def sixVertexConfigurationPairFineProfileFiberEquivHorizontalCompletions
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (profile : SixVertexHorizontalBoundedFineRowProfile T) :
    SixVertexConfigurationPairFineProfileFiber T left right profile ≃
      SixVertexHorizontalFineProfileCompletionPair
        T left right profile where
  toFun pair :=
    ⟨⟨(pair.1.1.1.horizontal, pair.1.2.1.horizontal), pair.2⟩,
      (⟨⟨pair.1.1.1.vertical, pair.1.1.2.1⟩, pair.1.1.2.2⟩,
        ⟨⟨pair.1.2.1.vertical, pair.1.2.2.1⟩, pair.1.2.2.2⟩)⟩
  invFun completed :=
    ⟨(⟨sixVertexArrowsOfFields
          completed.1.1.1 completed.2.1.1.1,
        completed.2.1.1.2, completed.2.1.2⟩,
      ⟨sixVertexArrowsOfFields
          completed.1.1.2 completed.2.2.1.1,
        completed.2.2.1.2, completed.2.2.2⟩),
      completed.1.2⟩
  left_inv pair := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;>
      apply SixVertexArrows.ext <;> rfl
  right_inv completed := by
    rcases completed with
      ⟨⟨⟨firstHorizontal, secondHorizontal⟩, hprofile⟩,
        ⟨⟨⟨firstVertical, firstIce⟩, firstSector⟩,
          ⟨⟨secondVertical, secondIce⟩, secondSector⟩⟩⟩
    rfl

@[simp] theorem sixVertexFineProfileCompletionPairArrows_equiv
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    {profile : SixVertexHorizontalBoundedFineRowProfile T}
    (pair : SixVertexConfigurationPairFineProfileFiber
      T left right profile) :
    sixVertexHorizontalFineProfileCompletionPairArrows
        (sixVertexConfigurationPairFineProfileFiberEquivHorizontalCompletions
          T left right profile pair) =
      (pair.1.1.1, pair.1.2.1) := by
  apply Prod.ext <;> apply SixVertexArrows.ext <;> rfl




def SixVertexHorizontalFineProfileCompletionPairTwoCycleRelated
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    {profile : SixVertexHorizontalBoundedFineRowProfile T}
    (source : SixVertexHorizontalFineProfileCompletionPair
      T lower upper profile)
    (target : SixVertexHorizontalFineProfileCompletionPair
      T middle middle profile) : Prop :=
  sixVertexPairAtMostTwoCycleRelated
    (sixVertexHorizontalFineProfileCompletionPairArrows source)
    (sixVertexHorizontalFineProfileCompletionPairArrows target)



def SixVertexHorizontalFineProfileCompletionPairUnionEqual
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    {profile : SixVertexHorizontalBoundedFineRowProfile T}
    (source : SixVertexHorizontalFineProfileCompletionPair
      T lower upper profile)
    (target : SixVertexHorizontalFineProfileCompletionPair
      T middle middle profile) : Prop :=
  let sourceArrows :=
    sixVertexHorizontalFineProfileCompletionPairArrows source
  let targetArrows :=
    sixVertexHorizontalFineProfileCompletionPairArrows target
  sixVertexPairUnionHorizontal sourceArrows =
      sixVertexPairUnionHorizontal targetArrows /\
    sixVertexPairUnionVertical sourceArrows =
      sixVertexPairUnionVertical targetArrows

theorem SixVertexHorizontalFineProfileCompletionPairUnionEqual.twoCycle
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    {profile : SixVertexHorizontalBoundedFineRowProfile T}
    {source : SixVertexHorizontalFineProfileCompletionPair
      T lower upper profile}
    {target : SixVertexHorizontalFineProfileCompletionPair
      T middle middle profile}
    (hunion : SixVertexHorizontalFineProfileCompletionPairUnionEqual
      source target) :
    SixVertexHorizontalFineProfileCompletionPairTwoCycleRelated
      source target := by
  exact sixVertexPairAtMostTwoCycleRelated_of_union_eq
    hunion.1 hunion.2

theorem fineProfileCompletionPairTwoCycleRelated_equiv_iff
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    {profile : SixVertexHorizontalBoundedFineRowProfile T}
    (source : SixVertexConfigurationPairFineProfileFiber
      T lower upper profile)
    (target : SixVertexConfigurationPairFineProfileFiber
      T middle middle profile) :
    SixVertexHorizontalFineProfileCompletionPairTwoCycleRelated
        (sixVertexConfigurationPairFineProfileFiberEquivHorizontalCompletions
          T lower upper profile source)
        (sixVertexConfigurationPairFineProfileFiberEquivHorizontalCompletions
          T middle middle profile target) <->
      SixVertexConfigurationPairTwoCycleFineProfileRelated
        source target := by
  rw [SixVertexHorizontalFineProfileCompletionPairTwoCycleRelated,
    sixVertexFineProfileCompletionPairArrows_equiv,
    sixVertexFineProfileCompletionPairArrows_equiv]
  constructor
  · intro hrelated
    exact ⟨hrelated, source.2.trans target.2.symm⟩
  · intro hrelated
    exact hrelated.1




def SixVertexHorizontalFineProfileCompletionTwoCycleMatching
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) : Prop :=
  forall profile : SixVertexHorizontalBoundedFineRowProfile T,
    exists matching :
        SixVertexHorizontalFineProfileCompletionPair
            T lower upper profile ->
          SixVertexHorizontalFineProfileCompletionPair
            T middle middle profile,
      Function.Injective matching /\
        forall source,
          SixVertexHorizontalFineProfileCompletionPairTwoCycleRelated
            source (matching source)



def SixVertexHorizontalFineProfileCompletionUnionMatching
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) : Prop :=
  forall profile : SixVertexHorizontalBoundedFineRowProfile T,
    exists matching :
        SixVertexHorizontalFineProfileCompletionPair
            T lower upper profile ->
          SixVertexHorizontalFineProfileCompletionPair
            T middle middle profile,
      Function.Injective matching /\
        forall source,
          SixVertexHorizontalFineProfileCompletionPairUnionEqual
            source (matching source)



theorem horizontalFineProfileCompletionTwoCycleMatching_of_unionMatching
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    (hunion : SixVertexHorizontalFineProfileCompletionUnionMatching
      T lower middle upper) :
    SixVertexHorizontalFineProfileCompletionTwoCycleMatching
      T lower middle upper := by
  intro profile
  obtain ⟨matching, hinjective, hpreserves⟩ := hunion profile
  exact ⟨matching, hinjective,
    fun source => (hpreserves source).twoCycle⟩



theorem horizontalFineProfileCompletionTwoCycleMatching_iff_fiberHall
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) :
    SixVertexHorizontalFineProfileCompletionTwoCycleMatching
        T lower middle upper <->
      SixVertexConfigurationPairTwoCycleFineProfileFiberHall
        T lower middle upper := by
  rw [configurationPairTwoCycleFineProfileFiberHall_iff]
  constructor
  · intro hcompletion profile
    obtain ⟨matching, hinjective, hrelated⟩ := hcompletion profile
    let sourceEquiv :=
      sixVertexConfigurationPairFineProfileFiberEquivHorizontalCompletions
        T lower upper profile
    let targetEquiv :=
      sixVertexConfigurationPairFineProfileFiberEquivHorizontalCompletions
        T middle middle profile
    let fiberMatching := fun source =>
      targetEquiv.symm (matching (sourceEquiv source))
    refine ⟨fiberMatching, ?_, ?_⟩
    · intro source₁ source₂ heq
      apply sourceEquiv.injective
      apply hinjective
      apply targetEquiv.symm.injective
      exact heq
    · intro source
      exact (fineProfileCompletionPairTwoCycleRelated_equiv_iff
        source (fiberMatching source)).mp (by
          change SixVertexHorizontalFineProfileCompletionPairTwoCycleRelated
            (sourceEquiv source) (matching (sourceEquiv source))
          exact hrelated (sourceEquiv source))
  · intro hFiber profile
    obtain ⟨matching, hinjective, hrelated⟩ := hFiber profile
    let sourceEquiv :=
      sixVertexConfigurationPairFineProfileFiberEquivHorizontalCompletions
        T lower upper profile
    let targetEquiv :=
      sixVertexConfigurationPairFineProfileFiberEquivHorizontalCompletions
        T middle middle profile
    let completionMatching := fun source =>
      targetEquiv (matching (sourceEquiv.symm source))
    refine ⟨completionMatching, ?_, ?_⟩
    · intro source₁ source₂ heq
      apply sourceEquiv.symm.injective
      apply hinjective
      apply targetEquiv.injective
      exact heq
    · intro source
      exact (fineProfileCompletionPairTwoCycleRelated_equiv_iff
        (sourceEquiv.symm source)
        (matching (sourceEquiv.symm source))).mpr
          (hrelated (sourceEquiv.symm source))



theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_completionMatching
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hmatching : SixVertexHorizontalFineProfileCompletionTwoCycleMatching T
      ⟨middle.val - 1, by omega⟩ middle
      ⟨middle.val + 1, by omega⟩) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val := by
  apply sixVertexMarkedTraceCoefficientwiseLogConcave_of_twoCycleFineHall
    T middle hmiddle_pos hmiddle_lt
  apply configurationPairTwoCycleFineHall_of_profileFiberHall
  exact (horizontalFineProfileCompletionTwoCycleMatching_iff_fiberHall
    T ⟨middle.val - 1, by omega⟩ middle
      ⟨middle.val + 1, by omega⟩).mp hmatching



theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_unionMatching
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hmatching : SixVertexHorizontalFineProfileCompletionUnionMatching T
      ⟨middle.val - 1, by omega⟩ middle
      ⟨middle.val + 1, by omega⟩) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_completionMatching
    T middle hmiddle_pos hmiddle_lt
      (horizontalFineProfileCompletionTwoCycleMatching_of_unionMatching
        hmatching)

end

end StatMech.FrontierD
