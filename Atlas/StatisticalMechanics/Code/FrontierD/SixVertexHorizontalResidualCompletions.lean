/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexHorizontalActualDeficitSupport










namespace StatMech.FrontierD

noncomputable section

local instance sixVertexHorizontalResidualCompletionsPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p

abbrev SixVertexHorizontalPairSectorCompletions
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :=
  SixVertexHorizontalSectorCompletion T left horizontal.1 ×
    SixVertexHorizontalSectorCompletion T right horizontal.2

theorem sixVertexHorizontalProfileDeficit_eq_sub
    {T : EvenTorus}
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (profile : SixVertexHorizontalPairCompletionProfile T) :
    sixVertexHorizontalProfileDeficit
        sourceLeft sourceRight targetLeft targetRight profile =
      sixVertexHorizontalPairProfileChooseWeight
          sourceLeft sourceRight profile -
        sixVertexHorizontalPairProfileChooseWeight
          targetLeft targetRight profile := by
  unfold sixVertexHorizontalProfileDeficit
    sixVertexHorizontalProfileSignedKernel
  omega

theorem sixVertexHorizontalProfileSurplus_eq_sub
    {T : EvenTorus}
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (profile : SixVertexHorizontalPairCompletionProfile T) :
    sixVertexHorizontalProfileSurplus
        sourceLeft sourceRight targetLeft targetRight profile =
      sixVertexHorizontalPairProfileChooseWeight
          targetLeft targetRight profile -
        sixVertexHorizontalPairProfileChooseWeight
          sourceLeft sourceRight profile := by
  unfold sixVertexHorizontalProfileSurplus
    sixVertexHorizontalProfileSignedKernel
  omega



theorem sixVertexHorizontalPairProfileChooseWeight_eq_zero_of_left_isEmpty
    {T : EvenTorus} (sourceLeft sourceRight : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
    (hleft : IsEmpty
      (SixVertexHorizontalSectorCompletion T sourceLeft horizontal.1)) :
    sixVertexHorizontalPairProfileChooseWeight sourceLeft sourceRight
        (sixVertexHorizontalPairCompletionProfile T horizontal) = 0 := by
  rw [← sixVertexHorizontalPairChooseWeight_eq_profile]
  rw [sixVertexHorizontalSectorCompletionChooseCount_eq_zero_of_isEmpty
    T sourceLeft horizontal.1 hleft, zero_mul]



theorem sixVertexHorizontalPairProfileChooseWeight_eq_zero_of_right_isEmpty
    {T : EvenTorus} (sourceLeft sourceRight : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
    (hright : IsEmpty
      (SixVertexHorizontalSectorCompletion T sourceRight horizontal.2)) :
    sixVertexHorizontalPairProfileChooseWeight sourceLeft sourceRight
        (sixVertexHorizontalPairCompletionProfile T horizontal) = 0 := by
  rw [← sixVertexHorizontalPairChooseWeight_eq_profile]
  rw [sixVertexHorizontalSectorCompletionChooseCount_eq_zero_of_isEmpty
    T sourceRight horizontal.2 hright, mul_zero]


noncomputable def sixVertexHorizontalDeficitCompletionEmbedding
    {T : EvenTorus} {grade : Nat × Nat}
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (profile : SixVertexHorizontalPairCompletionProfile T)
    (fiber : SixVertexHorizontalPairProfileFiber T grade profile) :
    Fin (sixVertexHorizontalProfileDeficit sourceLeft sourceRight
      targetLeft targetRight profile) ↪
      SixVertexHorizontalPairSectorCompletions T sourceLeft sourceRight
        fiber.1.1 := by
  let horizontal := fiber.1.1
  letI : Fintype (SixVertexVerticalCompletion T horizontal.1) :=
    Subtype.fintype _
  letI : Fintype (SixVertexVerticalCompletion T horizontal.2) :=
    Subtype.fintype _
  letI : Fintype (SixVertexHorizontalSectorCompletion
      T sourceLeft horizontal.1) := Subtype.fintype _
  letI : Fintype (SixVertexHorizontalSectorCompletion
      T sourceRight horizontal.2) := Subtype.fintype _
  have hprofile :
      sixVertexHorizontalPairCompletionProfile T horizontal = profile :=
    fiber.2
  have hindex (index : Fin (sixVertexHorizontalProfileDeficit
      sourceLeft sourceRight targetLeft targetRight profile)) : index.val <
      Fintype.card (SixVertexHorizontalPairSectorCompletions
        T sourceLeft sourceRight horizontal) := by
    calc
      index.val < sixVertexHorizontalProfileDeficit sourceLeft sourceRight
          targetLeft targetRight profile := index.isLt
      _ <= sixVertexHorizontalPairProfileChooseWeight
          sourceLeft sourceRight profile := by
        rw [sixVertexHorizontalProfileDeficit_eq_sub]
        exact Nat.sub_le _ _
      _ = sixVertexHorizontalSectorCompletionChooseCount
            T sourceLeft horizontal.1 *
          sixVertexHorizontalSectorCompletionChooseCount
            T sourceRight horizontal.2 := by
        rw [sixVertexHorizontalPairChooseWeight_eq_profile, hprofile]
      _ = Fintype.card (SixVertexHorizontalPairSectorCompletions
          T sourceLeft sourceRight horizontal) := by
        rw [Fintype.card_prod]
        exact congrArg₂ (fun a b : Nat => a * b)
          (card_sixVertexHorizontalSectorCompletion_eq_chooseCount
            T sourceLeft horizontal.1).symm
          (card_sixVertexHorizontalSectorCompletion_eq_chooseCount
            T sourceRight horizontal.2).symm
  let completionEquiv := Fintype.equivFin
    (SixVertexHorizontalPairSectorCompletions
      T sourceLeft sourceRight horizontal)
  refine
    { toFun := fun index => completionEquiv.symm ⟨index.val, hindex index⟩
      inj' := ?_ }
  intro first second heq
  apply Fin.ext
  have hindexEq := congrArg completionEquiv heq
  simpa only [Equiv.apply_symm_apply] using congrArg Fin.val hindexEq


noncomputable def sixVertexHorizontalSurplusCompletionEmbedding
    {T : EvenTorus} {grade : Nat × Nat}
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (profile : SixVertexHorizontalPairCompletionProfile T)
    (fiber : SixVertexHorizontalPairProfileFiber T grade profile) :
    Fin (sixVertexHorizontalProfileSurplus sourceLeft sourceRight
      targetLeft targetRight profile) ↪
      SixVertexHorizontalPairSectorCompletions T targetLeft targetRight
        fiber.1.1 := by
  let horizontal := fiber.1.1
  letI : Fintype (SixVertexVerticalCompletion T horizontal.1) :=
    Subtype.fintype _
  letI : Fintype (SixVertexVerticalCompletion T horizontal.2) :=
    Subtype.fintype _
  letI : Fintype (SixVertexHorizontalSectorCompletion
      T targetLeft horizontal.1) := Subtype.fintype _
  letI : Fintype (SixVertexHorizontalSectorCompletion
      T targetRight horizontal.2) := Subtype.fintype _
  have hprofile :
      sixVertexHorizontalPairCompletionProfile T horizontal = profile :=
    fiber.2
  have hindex (index : Fin (sixVertexHorizontalProfileSurplus
      sourceLeft sourceRight targetLeft targetRight profile)) : index.val <
      Fintype.card (SixVertexHorizontalPairSectorCompletions
        T targetLeft targetRight horizontal) := by
    calc
      index.val < sixVertexHorizontalProfileSurplus sourceLeft sourceRight
          targetLeft targetRight profile := index.isLt
      _ <= sixVertexHorizontalPairProfileChooseWeight
          targetLeft targetRight profile := by
        rw [sixVertexHorizontalProfileSurplus_eq_sub]
        exact Nat.sub_le _ _
      _ = sixVertexHorizontalSectorCompletionChooseCount
            T targetLeft horizontal.1 *
          sixVertexHorizontalSectorCompletionChooseCount
            T targetRight horizontal.2 := by
        rw [sixVertexHorizontalPairChooseWeight_eq_profile, hprofile]
      _ = Fintype.card (SixVertexHorizontalPairSectorCompletions
          T targetLeft targetRight horizontal) := by
        rw [Fintype.card_prod]
        exact congrArg₂ (fun a b : Nat => a * b)
          (card_sixVertexHorizontalSectorCompletion_eq_chooseCount
            T targetLeft horizontal.1).symm
          (card_sixVertexHorizontalSectorCompletion_eq_chooseCount
            T targetRight horizontal.2).symm
  let completionEquiv := Fintype.equivFin
    (SixVertexHorizontalPairSectorCompletions
      T targetLeft targetRight horizontal)
  refine
    { toFun := fun index => completionEquiv.symm ⟨index.val, hindex index⟩
      inj' := ?_ }
  intro first second heq
  apply Fin.ext
  have hindexEq := congrArg completionEquiv heq
  simpa only [Equiv.apply_symm_apply] using congrArg Fin.val hindexEq

noncomputable def sixVertexHorizontalActualDeficitCompletionPair
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (token : SixVertexHorizontalActualDeficitTokens T grade
      sourceLeft sourceRight targetLeft targetRight) :
    SixVertexHorizontalPairSectorCompletions T sourceLeft sourceRight
      (sixVertexHorizontalActualDeficitPair token) :=
  sixVertexHorizontalDeficitCompletionEmbedding sourceLeft sourceRight
    targetLeft targetRight token.1 token.2.1 token.2.2

noncomputable def sixVertexHorizontalActualSurplusCompletionPair
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (token : SixVertexHorizontalActualSurplusTokens T grade
      sourceLeft sourceRight targetLeft targetRight) :
    SixVertexHorizontalPairSectorCompletions T targetLeft targetRight
      (sixVertexHorizontalActualSurplusPair token) :=
  sixVertexHorizontalSurplusCompletionEmbedding sourceLeft sourceRight
    targetLeft targetRight token.1 token.2.1 token.2.2

noncomputable def sixVertexHorizontalActualDeficitConfigurationPair
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (token : SixVertexHorizontalActualDeficitTokens T grade
      sourceLeft sourceRight targetLeft targetRight) :
    {pair : SixVertexMarkedSectorConfiguration T sourceLeft ×
        SixVertexMarkedSectorConfiguration T sourceRight //
      sixVertexConfigurationPairBigrade pair = grade} :=
  (sixVertexConfigurationPairBigradeFiberEquivHorizontalCompletions
    T sourceLeft sourceRight grade).symm
      ⟨token.2.1.1,
        sixVertexHorizontalActualDeficitCompletionPair token⟩

noncomputable def sixVertexHorizontalActualSurplusConfigurationPair
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (token : SixVertexHorizontalActualSurplusTokens T grade
      sourceLeft sourceRight targetLeft targetRight) :
    {pair : SixVertexMarkedSectorConfiguration T targetLeft ×
        SixVertexMarkedSectorConfiguration T targetRight //
      sixVertexConfigurationPairBigrade pair = grade} :=
  (sixVertexConfigurationPairBigradeFiberEquivHorizontalCompletions
    T targetLeft targetRight grade).symm
      ⟨token.2.1.1,
        sixVertexHorizontalActualSurplusCompletionPair token⟩



theorem sixVertexHorizontalActualDeficitConfigurationPair_injective
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)} :
    Function.Injective
      (sixVertexHorizontalActualDeficitConfigurationPair :
        SixVertexHorizontalActualDeficitTokens T grade
            sourceLeft sourceRight targetLeft targetRight ->
          {pair : SixVertexMarkedSectorConfiguration T sourceLeft ×
              SixVertexMarkedSectorConfiguration T sourceRight //
            sixVertexConfigurationPairBigrade pair = grade}) := by
  rintro ⟨firstProfile, ⟨firstFiber, firstIndex⟩⟩
    ⟨secondProfile, ⟨secondFiber, secondIndex⟩⟩ heq
  let first : SixVertexHorizontalActualDeficitTokens T grade
      sourceLeft sourceRight targetLeft targetRight :=
    ⟨firstProfile, firstFiber, firstIndex⟩
  let second : SixVertexHorizontalActualDeficitTokens T grade
      sourceLeft sourceRight targetLeft targetRight :=
    ⟨secondProfile, secondFiber, secondIndex⟩
  change sixVertexHorizontalActualDeficitConfigurationPair first =
    sixVertexHorizontalActualDeficitConfigurationPair second at heq
  let coordinateEquiv :=
    sixVertexConfigurationPairBigradeFiberEquivHorizontalCompletions
      T sourceLeft sourceRight grade
  have hcoordinates := congrArg coordinateEquiv heq
  simp only [coordinateEquiv,
    sixVertexHorizontalActualDeficitConfigurationPair,
    Equiv.apply_symm_apply] at hcoordinates
  have hhorizontal : first.2.1.1 = second.2.1.1 :=
    congrArg Sigma.fst hcoordinates
  have hhorizontalValue : first.2.1.1.1 = second.2.1.1.1 :=
    congrArg Subtype.val hhorizontal
  have hprofile : firstProfile = secondProfile :=
    firstFiber.2.symm.trans ((congrArg
      (sixVertexHorizontalPairCompletionProfile T) hhorizontalValue).trans
        secondFiber.2)
  cases hprofile
  refine Sigma.ext rfl (heq_of_eq ?_)
  have hfiber : firstFiber = secondFiber := by
    apply Subtype.ext
    exact hhorizontal
  apply Prod.ext
  · exact hfiber
  · subst hfiber
    have hcompletion := eq_of_heq (Sigma.ext_iff.mp hcoordinates).2
    apply (sixVertexHorizontalDeficitCompletionEmbedding sourceLeft
      sourceRight targetLeft targetRight firstProfile firstFiber).injective
    simpa only [first, second,
      sixVertexHorizontalActualDeficitCompletionPair] using hcompletion



theorem sixVertexHorizontalActualSurplusConfigurationPair_injective
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)} :
    Function.Injective
      (sixVertexHorizontalActualSurplusConfigurationPair :
        SixVertexHorizontalActualSurplusTokens T grade
            sourceLeft sourceRight targetLeft targetRight ->
          {pair : SixVertexMarkedSectorConfiguration T targetLeft ×
              SixVertexMarkedSectorConfiguration T targetRight //
            sixVertexConfigurationPairBigrade pair = grade}) := by
  rintro ⟨firstProfile, ⟨firstFiber, firstIndex⟩⟩
    ⟨secondProfile, ⟨secondFiber, secondIndex⟩⟩ heq
  let first : SixVertexHorizontalActualSurplusTokens T grade
      sourceLeft sourceRight targetLeft targetRight :=
    ⟨firstProfile, firstFiber, firstIndex⟩
  let second : SixVertexHorizontalActualSurplusTokens T grade
      sourceLeft sourceRight targetLeft targetRight :=
    ⟨secondProfile, secondFiber, secondIndex⟩
  change sixVertexHorizontalActualSurplusConfigurationPair first =
    sixVertexHorizontalActualSurplusConfigurationPair second at heq
  let coordinateEquiv :=
    sixVertexConfigurationPairBigradeFiberEquivHorizontalCompletions
      T targetLeft targetRight grade
  have hcoordinates := congrArg coordinateEquiv heq
  simp only [coordinateEquiv,
    sixVertexHorizontalActualSurplusConfigurationPair,
    Equiv.apply_symm_apply] at hcoordinates
  have hhorizontal : first.2.1.1 = second.2.1.1 :=
    congrArg Sigma.fst hcoordinates
  have hhorizontalValue : first.2.1.1.1 = second.2.1.1.1 :=
    congrArg Subtype.val hhorizontal
  have hprofile : firstProfile = secondProfile :=
    firstFiber.2.symm.trans ((congrArg
      (sixVertexHorizontalPairCompletionProfile T) hhorizontalValue).trans
        secondFiber.2)
  cases hprofile
  refine Sigma.ext rfl (heq_of_eq ?_)
  have hfiber : firstFiber = secondFiber := by
    apply Subtype.ext
    exact hhorizontal
  apply Prod.ext
  · exact hfiber
  · subst hfiber
    have hcompletion := eq_of_heq (Sigma.ext_iff.mp hcoordinates).2
    apply (sixVertexHorizontalSurplusCompletionEmbedding sourceLeft
      sourceRight targetLeft targetRight firstProfile firstFiber).injective
    simpa only [first, second,
      sixVertexHorizontalActualSurplusCompletionPair] using hcompletion




theorem
    sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_sourceWeight_eq_zero
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (configuration :
      {pair : SixVertexMarkedSectorConfiguration T targetLeft ×
          SixVertexMarkedSectorConfiguration T targetRight //
        sixVertexConfigurationPairBigrade pair = grade})
    (hzero : sixVertexHorizontalPairProfileChooseWeight
      sourceLeft sourceRight
      (sixVertexHorizontalPairCompletionProfile T
        ((sixVertexConfigurationPairBigradeFiberEquivHorizontalCompletions
          T targetLeft targetRight grade) configuration).1.1) = 0) :
    ∃ token : SixVertexHorizontalActualSurplusTokens T grade
        sourceLeft sourceRight targetLeft targetRight,
      sixVertexHorizontalActualSurplusConfigurationPair token = configuration := by
  let coordinateEquiv :=
    sixVertexConfigurationPairBigradeFiberEquivHorizontalCompletions
      T targetLeft targetRight grade
  let coordinates := coordinateEquiv configuration
  let horizontal := coordinates.1
  let completions := coordinates.2
  letI : Fintype (SixVertexVerticalCompletion T horizontal.1.1) :=
    Subtype.fintype _
  letI : Fintype (SixVertexVerticalCompletion T horizontal.1.2) :=
    Subtype.fintype _
  letI : Fintype (SixVertexHorizontalSectorCompletion
      T targetLeft horizontal.1.1) := Subtype.fintype _
  letI : Fintype (SixVertexHorizontalSectorCompletion
      T targetRight horizontal.1.2) := Subtype.fintype _
  let profile := sixVertexHorizontalPairCompletionProfile T horizontal.1
  let fiber : SixVertexHorizontalPairProfileFiber T grade profile :=
    ⟨horizontal, rfl⟩
  let completionEquiv := Fintype.equivFin
    (SixVertexHorizontalPairSectorCompletions
      T targetLeft targetRight horizontal.1)
  have hsurplus :
      sixVertexHorizontalProfileSurplus sourceLeft sourceRight
          targetLeft targetRight profile =
        Fintype.card (SixVertexHorizontalPairSectorCompletions
          T targetLeft targetRight horizontal.1) := by
    rw [sixVertexHorizontalProfileSurplus_eq_sub, hzero]
    simp only [Nat.sub_zero]
    calc
      sixVertexHorizontalPairProfileChooseWeight
          targetLeft targetRight profile =
          sixVertexHorizontalSectorCompletionChooseCount
              T targetLeft horizontal.1.1 *
            sixVertexHorizontalSectorCompletionChooseCount
              T targetRight horizontal.1.2 := by
        exact (sixVertexHorizontalPairChooseWeight_eq_profile
          T targetLeft targetRight horizontal.1).symm
      _ = Fintype.card (SixVertexHorizontalPairSectorCompletions
          T targetLeft targetRight horizontal.1) := by
        rw [Fintype.card_prod]
        exact congrArg₂ (fun a b : Nat => a * b)
          (card_sixVertexHorizontalSectorCompletion_eq_chooseCount
            T targetLeft horizontal.1.1).symm
          (card_sixVertexHorizontalSectorCompletion_eq_chooseCount
            T targetRight horizontal.1.2).symm
  let index : Fin (sixVertexHorizontalProfileSurplus sourceLeft sourceRight
      targetLeft targetRight profile) :=
    ⟨(completionEquiv completions).val, by
      rw [hsurplus]
      exact (completionEquiv completions).isLt⟩
  let token : SixVertexHorizontalActualSurplusTokens T grade
      sourceLeft sourceRight targetLeft targetRight :=
    ⟨profile, fiber, index⟩
  refine ⟨token, ?_⟩
  apply coordinateEquiv.injective
  change Sigma.mk horizontal
      (sixVertexHorizontalActualSurplusCompletionPair token) = coordinates
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    change (sixVertexHorizontalSurplusCompletionEmbedding sourceLeft sourceRight
      targetLeft targetRight profile fiber) index = completions
    change completionEquiv.symm ⟨index.val, _⟩ = completions
    apply completionEquiv.injective
    simp only [Equiv.apply_symm_apply]
    apply Fin.ext
    rfl


theorem
    sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_horizontalSourceWeight_eq_zero
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (configuration :
      {pair : SixVertexMarkedSectorConfiguration T targetLeft ×
          SixVertexMarkedSectorConfiguration T targetRight //
        sixVertexConfigurationPairBigrade pair = grade})
    (hzero : sixVertexHorizontalPairProfileChooseWeight
      sourceLeft sourceRight
      (sixVertexHorizontalPairCompletionProfile T
        (configuration.1.1.1.horizontal,
          configuration.1.2.1.horizontal)) = 0) :
    ∃ token : SixVertexHorizontalActualSurplusTokens T grade
        sourceLeft sourceRight targetLeft targetRight,
      sixVertexHorizontalActualSurplusConfigurationPair token = configuration := by
  apply
    sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_sourceWeight_eq_zero
  exact hzero



theorem
    sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_left_isEmpty
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (configuration :
      {pair : SixVertexMarkedSectorConfiguration T targetLeft ×
          SixVertexMarkedSectorConfiguration T targetRight //
        sixVertexConfigurationPairBigrade pair = grade})
    (hleft : IsEmpty (SixVertexHorizontalSectorCompletion T sourceLeft
      configuration.1.1.1.horizontal)) :
    ∃ token : SixVertexHorizontalActualSurplusTokens T grade
        sourceLeft sourceRight targetLeft targetRight,
      sixVertexHorizontalActualSurplusConfigurationPair token = configuration := by
  apply
    sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_horizontalSourceWeight_eq_zero
  exact sixVertexHorizontalPairProfileChooseWeight_eq_zero_of_left_isEmpty
    sourceLeft sourceRight
      (configuration.1.1.1.horizontal, configuration.1.2.1.horizontal) hleft



theorem
    sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_right_isEmpty
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (configuration :
      {pair : SixVertexMarkedSectorConfiguration T targetLeft ×
          SixVertexMarkedSectorConfiguration T targetRight //
        sixVertexConfigurationPairBigrade pair = grade})
    (hright : IsEmpty (SixVertexHorizontalSectorCompletion T sourceRight
      configuration.1.2.1.horizontal)) :
    ∃ token : SixVertexHorizontalActualSurplusTokens T grade
        sourceLeft sourceRight targetLeft targetRight,
      sixVertexHorizontalActualSurplusConfigurationPair token = configuration := by
  apply
    sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_horizontalSourceWeight_eq_zero
  exact sixVertexHorizontalPairProfileChooseWeight_eq_zero_of_right_isEmpty
    sourceLeft sourceRight
      (configuration.1.1.1.horizontal, configuration.1.2.1.horizontal) hright

def sixVertexHorizontalResidualConfigurationSupport
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (support : forall grade,
      {pair : SixVertexMarkedSectorConfiguration T sourceLeft ×
          SixVertexMarkedSectorConfiguration T sourceRight //
        sixVertexConfigurationPairBigrade pair = grade} ->
      {pair : SixVertexMarkedSectorConfiguration T targetLeft ×
          SixVertexMarkedSectorConfiguration T targetRight //
        sixVertexConfigurationPairBigrade pair = grade} -> Prop) :
    forall grade,
      SixVertexHorizontalActualDeficitTokens T grade
          sourceLeft sourceRight targetLeft targetRight ->
        SixVertexHorizontalActualSurplusTokens T grade
          sourceLeft sourceRight targetLeft targetRight -> Prop :=
  fun grade source target =>
    support grade
      (sixVertexHorizontalActualDeficitConfigurationPair source)
      (sixVertexHorizontalActualSurplusConfigurationPair target)

theorem configurationBigradeFibers_of_residualConfigurationHall
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (support : forall grade,
      {pair : SixVertexMarkedSectorConfiguration T sourceLeft ×
          SixVertexMarkedSectorConfiguration T sourceRight //
        sixVertexConfigurationPairBigrade pair = grade} ->
      {pair : SixVertexMarkedSectorConfiguration T targetLeft ×
          SixVertexMarkedSectorConfiguration T targetRight //
        sixVertexConfigurationPairBigrade pair = grade} -> Prop)
    (hHall : SixVertexHorizontalActualDeficitTokenHall T
      sourceLeft sourceRight targetLeft targetRight
      (sixVertexHorizontalResidualConfigurationSupport T
        sourceLeft sourceRight targetLeft targetRight support)) :
    SixVertexConfigurationPairBigradeFiberDominates T
      sourceLeft sourceRight targetLeft targetRight :=
  configurationBigradeFibers_of_actualDeficitTokenHall T
    sourceLeft sourceRight targetLeft targetRight _ hHall

end

end StatMech.FrontierD
