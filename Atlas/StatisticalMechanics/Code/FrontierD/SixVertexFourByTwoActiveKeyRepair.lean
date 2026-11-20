/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexFourByTwoActiveKeyObstruction
import Code.FrontierD.SixVertexFourByTwoTwoCycleHall
import Code.FrontierD.SixVertexHorizontalResidualCompletions










namespace StatMech.FrontierD

noncomputable section

local instance sixVertexFourByTwoActiveRepairDecidableProp (p : Prop) :
    Decidable p :=
  Classical.propDecidable p

def sixVertexFourByTwoActiveCycleMiddleFirstCompletion :
    SixVertexHorizontalSectorCompletion sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorOne
      sixVertexFourByTwoCycleMiddleFirst.horizontal :=
  ⟨⟨sixVertexFourByTwoCycleMiddleFirst.vertical,
      sixVertexFourByTwoCycleMiddleFirst_ice⟩,
    sixVertexFourByTwoCycleMiddleFirst_seamCount⟩

def sixVertexFourByTwoActiveCycleMiddleSecondCompletion :
    SixVertexHorizontalSectorCompletion sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorOne
      sixVertexFourByTwoCycleMiddleSecond.horizontal :=
  ⟨⟨sixVertexFourByTwoCycleMiddleSecond.vertical,
      sixVertexFourByTwoCycleMiddleSecond_ice⟩,
    sixVertexFourByTwoCycleMiddleSecond_seamCount⟩

section finiteChecks

local instance sixVertexFourByTwoActiveRepairIceRuleDecidable
    (omega : SixVertexArrows sixVertexFourByTwoTorus) :
    Decidable omega.IceRule :=
  inferInstanceAs (Decidable (forall v, omega.incomingCount v = 2))

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoActiveCycleMiddleFirstLower_impossible
    (vertical : sixVertexFourByTwoTorus.Vertex -> Bool) :
    ¬ ((sixVertexArrowsOfFields
        sixVertexFourByTwoCycleMiddleFirst.horizontal vertical).IceRule ∧
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByTwoTorus
            (sixVertexArrowsOfFields
              sixVertexFourByTwoCycleMiddleFirst.horizontal vertical)
            (svFinLast sixVertexFourByTwoTorus.height_pos)) = 0) := by
  decide +revert

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoActiveCycleMiddleFirst_vertical_unique
    (vertical : sixVertexFourByTwoTorus.Vertex -> Bool) :
    (sixVertexArrowsOfFields
          sixVertexFourByTwoCycleMiddleFirst.horizontal vertical).IceRule ∧
        sixVertexUpCount
            (svTorusVerticalRows sixVertexFourByTwoTorus
              (sixVertexArrowsOfFields
                sixVertexFourByTwoCycleMiddleFirst.horizontal vertical)
              (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 ->
      vertical = sixVertexFourByTwoCycleMiddleFirst.vertical := by
  decide +revert

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoActiveCycleMiddleSecond_vertical_unique
    (vertical : sixVertexFourByTwoTorus.Vertex -> Bool) :
    (sixVertexArrowsOfFields
          sixVertexFourByTwoCycleMiddleSecond.horizontal vertical).IceRule ∧
        sixVertexUpCount
            (svTorusVerticalRows sixVertexFourByTwoTorus
              (sixVertexArrowsOfFields
                sixVertexFourByTwoCycleMiddleSecond.horizontal vertical)
              (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 ->
      vertical = sixVertexFourByTwoCycleMiddleSecond.vertical := by
  decide +revert

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoActiveCycleRepair_bigrade :
    sixVertexHorizontalPairBigrade
        (sixVertexFourByTwoCycleMiddleFirst.horizontal,
          sixVertexFourByTwoCycleMiddleSecond.horizontal) =
      sixVertexFourByTwoActiveObstructionGrade := by
  decide +revert

end finiteChecks

theorem sixVertexFourByTwoActiveCycleMiddleFirstLower_isEmpty :
    IsEmpty
      (SixVertexHorizontalSectorCompletion sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorZero
        sixVertexFourByTwoCycleMiddleFirst.horizontal) := by
  constructor
  rintro ⟨⟨vertical, hice⟩, hsector⟩
  exact sixVertexFourByTwoActiveCycleMiddleFirstLower_impossible vertical
    ⟨hice, hsector⟩

def sixVertexFourByTwoActiveCycleRepairProfile :
    SixVertexHorizontalPairCompletionProfile sixVertexFourByTwoTorus :=
  sixVertexHorizontalPairCompletionProfile sixVertexFourByTwoTorus
    (sixVertexFourByTwoCycleMiddleFirst.horizontal,
      sixVertexFourByTwoCycleMiddleSecond.horizontal)

def sixVertexFourByTwoActiveCycleRepairFiber :
    SixVertexHorizontalPairProfileFiber sixVertexFourByTwoTorus
      sixVertexFourByTwoActiveObstructionGrade
      sixVertexFourByTwoActiveCycleRepairProfile :=
  ⟨⟨(sixVertexFourByTwoCycleMiddleFirst.horizontal,
      sixVertexFourByTwoCycleMiddleSecond.horizontal),
    sixVertexFourByTwoActiveCycleRepair_bigrade⟩, rfl⟩




theorem sixVertexFourByTwoActiveCycleRepairProfile_sourceWeight_eq_zero :
    sixVertexHorizontalPairProfileChooseWeight
      sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorTwo
      sixVertexFourByTwoActiveCycleRepairProfile = 0 := by
  exact sixVertexHorizontalPairProfileChooseWeight_eq_zero_of_left_isEmpty
    sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorTwo
    (sixVertexFourByTwoCycleMiddleFirst.horizontal,
      sixVertexFourByTwoCycleMiddleSecond.horizontal)
    sixVertexFourByTwoActiveCycleMiddleFirstLower_isEmpty

theorem sixVertexFourByTwoActiveCycleRepairProfile_surplus_pos :
    0 < sixVertexHorizontalProfileSurplus
      sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorTwo
      sixVertexFourByTwoSectorOne sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveCycleRepairProfile := by
  rw [sixVertexHorizontalProfileSurplus_eq_sub]
  have hsourceFirst :
      sixVertexHorizontalSectorCompletionChooseCount
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorZero
        sixVertexFourByTwoCycleMiddleFirst.horizontal = 0 := by
    exact sixVertexHorizontalSectorCompletionChooseCount_eq_zero_of_isEmpty
      _ _ _ sixVertexFourByTwoActiveCycleMiddleFirstLower_isEmpty
  have htargetFirst :
      0 < sixVertexHorizontalSectorCompletionChooseCount
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
        sixVertexFourByTwoCycleMiddleFirst.horizontal := by
    exact sixVertexHorizontalSectorCompletionChooseCount_pos_of_nonempty
      _ _ _ ⟨sixVertexFourByTwoActiveCycleMiddleFirstCompletion⟩
  have htargetSecond :
      0 < sixVertexHorizontalSectorCompletionChooseCount
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
        sixVertexFourByTwoCycleMiddleSecond.horizontal := by
    exact sixVertexHorizontalSectorCompletionChooseCount_pos_of_nonempty
      _ _ _ ⟨sixVertexFourByTwoActiveCycleMiddleSecondCompletion⟩
  change 0 <
    sixVertexHorizontalPairProfileChooseWeight
        sixVertexFourByTwoSectorOne sixVertexFourByTwoSectorOne
        (sixVertexHorizontalPairCompletionProfile sixVertexFourByTwoTorus
          (sixVertexFourByTwoCycleMiddleFirst.horizontal,
            sixVertexFourByTwoCycleMiddleSecond.horizontal)) -
      sixVertexHorizontalPairProfileChooseWeight
        sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorTwo
        (sixVertexHorizontalPairCompletionProfile sixVertexFourByTwoTorus
          (sixVertexFourByTwoCycleMiddleFirst.horizontal,
            sixVertexFourByTwoCycleMiddleSecond.horizontal))
  rw [← sixVertexHorizontalPairChooseWeight_eq_profile,
    ← sixVertexHorizontalPairChooseWeight_eq_profile]
  simp only [hsourceFirst, zero_mul, Nat.sub_zero]
  positivity

def sixVertexFourByTwoActiveCycleRepairSurplusToken :
    SixVertexHorizontalActualSurplusTokens sixVertexFourByTwoTorus
      sixVertexFourByTwoActiveObstructionGrade sixVertexFourByTwoSectorZero
      sixVertexFourByTwoSectorTwo sixVertexFourByTwoSectorOne
      sixVertexFourByTwoSectorOne :=
  ⟨sixVertexFourByTwoActiveCycleRepairProfile,
    sixVertexFourByTwoActiveCycleRepairFiber,
    ⟨0, sixVertexFourByTwoActiveCycleRepairProfile_surplus_pos⟩⟩

theorem sixVertexFourByTwoActiveCycleMiddleFirstCompletion_unique
    (completion : SixVertexHorizontalSectorCompletion
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoCycleMiddleFirst.horizontal) :
    completion = sixVertexFourByTwoActiveCycleMiddleFirstCompletion := by
  rcases completion with ⟨⟨vertical, hice⟩, hsector⟩
  apply Subtype.ext
  apply Subtype.ext
  exact sixVertexFourByTwoActiveCycleMiddleFirst_vertical_unique vertical
    ⟨hice, hsector⟩

theorem sixVertexFourByTwoActiveCycleMiddleSecondCompletion_unique
    (completion : SixVertexHorizontalSectorCompletion
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoCycleMiddleSecond.horizontal) :
    completion = sixVertexFourByTwoActiveCycleMiddleSecondCompletion := by
  rcases completion with ⟨⟨vertical, hice⟩, hsector⟩
  apply Subtype.ext
  apply Subtype.ext
  exact sixVertexFourByTwoActiveCycleMiddleSecond_vertical_unique vertical
    ⟨hice, hsector⟩

theorem sixVertexFourByTwoActiveCycleRepairCompletionPair_eq :
    sixVertexHorizontalActualSurplusCompletionPair
        sixVertexFourByTwoActiveCycleRepairSurplusToken =
      (sixVertexFourByTwoActiveCycleMiddleFirstCompletion,
        sixVertexFourByTwoActiveCycleMiddleSecondCompletion) := by
  apply Prod.ext
  · exact sixVertexFourByTwoActiveCycleMiddleFirstCompletion_unique _
  · exact sixVertexFourByTwoActiveCycleMiddleSecondCompletion_unique _

def sixVertexFourByTwoActiveCycleMiddleFirstConfiguration :
    SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorOne :=
  ⟨sixVertexFourByTwoCycleMiddleFirst,
    sixVertexFourByTwoCycleMiddleFirst_ice,
    sixVertexFourByTwoCycleMiddleFirst_seamCount⟩

def sixVertexFourByTwoActiveCycleMiddleSecondConfiguration :
    SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorOne :=
  ⟨sixVertexFourByTwoCycleMiddleSecond,
    sixVertexFourByTwoCycleMiddleSecond_ice,
    sixVertexFourByTwoCycleMiddleSecond_seamCount⟩


def sixVertexFourByTwoActiveCycleRepairPhysicalTarget :
    {pair : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
          sixVertexFourByTwoSectorOne ×
        SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
          sixVertexFourByTwoSectorOne //
      sixVertexConfigurationPairBigrade pair =
        sixVertexFourByTwoActiveObstructionGrade} :=
  ⟨(sixVertexFourByTwoActiveCycleMiddleFirstConfiguration,
      sixVertexFourByTwoActiveCycleMiddleSecondConfiguration), by
    rw [sixVertexConfigurationPairBigrade_eq_horizontalPairBigrade]
    exact sixVertexFourByTwoActiveCycleRepair_bigrade⟩



theorem sixVertexFourByTwoActiveCycleRepairPhysicalTarget_surplusPreimage :
    ∃ token : SixVertexHorizontalActualSurplusTokens
        sixVertexFourByTwoTorus sixVertexFourByTwoActiveObstructionGrade
        sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorTwo
        sixVertexFourByTwoSectorOne sixVertexFourByTwoSectorOne,
      sixVertexHorizontalActualSurplusConfigurationPair token =
        sixVertexFourByTwoActiveCycleRepairPhysicalTarget := by
  apply
    sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_horizontalSourceWeight_eq_zero
  exact sixVertexFourByTwoActiveCycleRepairProfile_sourceWeight_eq_zero

theorem sixVertexFourByTwoActiveCycleRepairConfigurationPair_eq :
    (sixVertexHorizontalActualSurplusConfigurationPair
      sixVertexFourByTwoActiveCycleRepairSurplusToken).1 =
      (sixVertexFourByTwoActiveCycleMiddleFirstConfiguration,
        sixVertexFourByTwoActiveCycleMiddleSecondConfiguration) := by
  apply Prod.ext
  · apply Subtype.ext
    apply SixVertexArrows.ext
    · rfl
    · exact congrArg (fun pair => pair.1.1.1)
        sixVertexFourByTwoActiveCycleRepairCompletionPair_eq
  · apply Subtype.ext
    apply SixVertexArrows.ext
    · rfl
    · exact congrArg (fun pair => pair.2.1.1)
        sixVertexFourByTwoActiveCycleRepairCompletionPair_eq

theorem sixVertexFourByTwoActiveCycleRepairSurplusToken_key :
    sixVertexHorizontalActualSurplusFineUnionKey
        sixVertexFourByTwoActiveCycleRepairSurplusToken =
      sixVertexFourByTwoActiveCycleRepairKey := by
  unfold sixVertexHorizontalActualSurplusFineUnionKey
    sixVertexFourByTwoActiveCycleRepairKey
  exact congrArg
    (fun pair => sixVertexPairFineUnionKey (pair.1.1, pair.2.1))
    sixVertexFourByTwoActiveCycleRepairConfigurationPair_eq

def sixVertexFourByTwoActiveCycleRepairSurplusKeyFiber :
    SixVertexHorizontalActualSurplusFineUnionKeyFiber
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionMiddle_pos
      sixVertexFourByTwoActiveObstructionMiddle_lt
      sixVertexFourByTwoActiveObstructionGrade
      sixVertexFourByTwoActiveCycleRepairKey :=
  ⟨sixVertexFourByTwoActiveCycleRepairSurplusToken,
    sixVertexFourByTwoActiveCycleRepairSurplusToken_key⟩

theorem sixVertexFourByTwoActiveCycleRepairSurplusCapacity_pos :
    0 < sixVertexHorizontalActualSurplusFineUnionCapacity
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionMiddle_pos
      sixVertexFourByTwoActiveObstructionMiddle_lt
      sixVertexFourByTwoActiveObstructionGrade
      sixVertexFourByTwoActiveCycleRepairKey := by
  change 0 < Fintype.card
    (SixVertexHorizontalActualSurplusFineUnionKeyFiber
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionMiddle_pos
      sixVertexFourByTwoActiveObstructionMiddle_lt
      sixVertexFourByTwoActiveObstructionGrade
      sixVertexFourByTwoActiveCycleRepairKey)
  apply Fintype.card_pos_iff.mpr
  exact ⟨sixVertexFourByTwoActiveCycleRepairSurplusKeyFiber⟩

theorem sixVertexFourByTwoActiveObstructionToken_cycleRepair_supported :
    sixVertexHorizontalOffDiagonalTwoCycleSupport
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionMiddle_pos
      sixVertexFourByTwoActiveObstructionMiddle_lt
      sixVertexFourByTwoActiveObstructionGrade
      sixVertexFourByTwoActiveObstructionToken
      sixVertexFourByTwoActiveCycleRepairSurplusToken := by
  change SixVertexConfigurationPairTwoCycleFineRelated
    (sixVertexHorizontalActualDeficitConfigurationPair
      sixVertexFourByTwoActiveObstructionToken).1
    (sixVertexHorizontalActualSurplusConfigurationPair
      sixVertexFourByTwoActiveCycleRepairSurplusToken).1
  rw [sixVertexFourByTwoActiveObstructionConfigurationPair_eq,
    sixVertexFourByTwoActiveCycleRepairConfigurationPair_eq]
  exact sixVertexFourByTwo_cycleMiddle_fineRelated

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoActiveSourceIndex_eq_of_signature
    (i : Fin 4 × Fin 50) :
    ((forall v,
          ((sixVertexFourByTwoSourceIndexArrows i).1.horizontal v).toNat +
              ((sixVertexFourByTwoSourceIndexArrows i).2.horizontal v).toNat =
            (sixVertexFourByTwoLowArrows.horizontal v).toNat +
              (sixVertexFourByTwoHighArrows.horizontal v).toNat) ∧
        (forall v,
          ((sixVertexFourByTwoSourceIndexArrows i).1.vertical v).toNat +
              ((sixVertexFourByTwoSourceIndexArrows i).2.vertical v).toNat =
            (sixVertexFourByTwoLowArrows.vertical v).toNat +
              (sixVertexFourByTwoHighArrows.vertical v).toNat) ∧
        sixVertexHorizontalPairBoundedFineRowProfile
            ((sixVertexFourByTwoSourceIndexArrows i).1.horizontal,
              (sixVertexFourByTwoSourceIndexArrows i).2.horizontal) =
          sixVertexHorizontalPairBoundedFineRowProfile
            (sixVertexFourByTwoLowArrows.horizontal,
              sixVertexFourByTwoHighArrows.horizontal)) ->
      i = (0, 29) := by
  rcases i with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> decide +revert

theorem sixVertexFourByTwoActiveSourceIndex_eq_of_key
    (i : Fin 4 × Fin 50)
    (hkey : sixVertexPairFineUnionKey
        (sixVertexFourByTwoSourceIndexArrows i) =
      sixVertexPairFineUnionKey
        (sixVertexFourByTwoLowArrows,
          sixVertexFourByTwoHighArrows)) :
    i = (0, 29) := by
  apply sixVertexFourByTwoActiveSourceIndex_eq_of_signature i
  constructor
  · intro v
    have h := congrFun
      (congrArg SixVertexPairFineUnionKey.horizontal hkey) v
    exact congrArg Fin.val h
  · constructor
    · intro v
      have h := congrFun
        (congrArg SixVertexPairFineUnionKey.vertical hkey) v
      exact congrArg Fin.val h
    · exact congrArg SixVertexPairFineUnionKey.fine hkey

theorem sixVertexFourByTwoActiveSourceIndexArrows_eq :
    sixVertexFourByTwoSourceIndexArrows (0, 29) =
      (sixVertexFourByTwoLowArrows,
        sixVertexFourByTwoHighArrows) := by
  apply Prod.ext <;> apply SixVertexArrows.ext <;> funext v
  all_goals
    rcases v with ⟨x, y⟩
    fin_cases x <;> fin_cases y <;> decide +revert

theorem sixVertexFourByTwoActiveSourceConfigurationPair_unique_of_key
    (source :
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
          sixVertexFourByTwoSectorZero ×
        SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
          sixVertexFourByTwoSectorTwo)
    (hkey : sixVertexPairFineUnionKey (source.1.1, source.2.1) =
      sixVertexPairFineUnionKey
        (sixVertexFourByTwoLowArrows,
          sixVertexFourByTwoHighArrows)) :
    source = (sixVertexFourByTwoLowConfiguration,
      sixVertexFourByTwoHighConfiguration) := by
  let i := sixVertexFourByTwoSourcePairEquiv.symm source
  have hsource := sixVertexFourByTwoSourcePairEquiv.apply_symm_apply source
  have hsourceArrows := congrArg
    (fun pair => (pair.1.1, pair.2.1)) hsource
  change sixVertexFourByTwoSourceIndexArrows i =
    (source.1.1, source.2.1) at hsourceArrows
  have hindex : i = (0, 29) := by
    apply sixVertexFourByTwoActiveSourceIndex_eq_of_key i
    rw [hsourceArrows]
    exact hkey
  calc
    source = sixVertexFourByTwoSourcePairEquiv i := hsource.symm
    _ = sixVertexFourByTwoSourcePairEquiv (0, 29) := congrArg _ hindex
    _ = (sixVertexFourByTwoLowConfiguration,
          sixVertexFourByTwoHighConfiguration) := by
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst
          sixVertexFourByTwoActiveSourceIndexArrows_eq
      · apply Subtype.ext
        exact congrArg Prod.snd
          sixVertexFourByTwoActiveSourceIndexArrows_eq

theorem sixVertexFourByTwoActiveObstructionSourceKeyFiber_eq
    (source : SixVertexHorizontalActualDeficitFineUnionKeyFiber
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionMiddle_pos
      sixVertexFourByTwoActiveObstructionMiddle_lt
      sixVertexFourByTwoActiveObstructionGrade
      sixVertexFourByTwoActiveObstructionKey) :
    source = ⟨sixVertexFourByTwoActiveObstructionToken, rfl⟩ := by
  apply Subtype.ext
  apply sixVertexHorizontalActualDeficitConfigurationPair_injective
  apply Subtype.ext
  calc
    (sixVertexHorizontalActualDeficitConfigurationPair source.1).1 =
        (sixVertexFourByTwoLowConfiguration,
          sixVertexFourByTwoHighConfiguration) := by
      apply sixVertexFourByTwoActiveSourceConfigurationPair_unique_of_key
      exact source.2.trans
        sixVertexFourByTwoActiveObstructionKey_eq_sourceKey
    _ = (sixVertexHorizontalActualDeficitConfigurationPair
          sixVertexFourByTwoActiveObstructionToken).1 :=
      sixVertexFourByTwoActiveObstructionConfigurationPair_eq.symm

theorem sixVertexFourByTwoActiveObstructionSourceKeyFiber_subsingleton
    (first second : SixVertexHorizontalActualDeficitFineUnionKeyFiber
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionMiddle_pos
      sixVertexFourByTwoActiveObstructionMiddle_lt
      sixVertexFourByTwoActiveObstructionGrade
      sixVertexFourByTwoActiveObstructionKey) :
    first = second :=
  (sixVertexFourByTwoActiveObstructionSourceKeyFiber_eq first).trans
    (sixVertexFourByTwoActiveObstructionSourceKeyFiber_eq second).symm

def sixVertexFourByTwoActiveObstructionCycleRepairFiberEmbedding :
    SixVertexHorizontalActualDeficitFineUnionKeyFiber
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
        sixVertexFourByTwoActiveObstructionMiddle_pos
        sixVertexFourByTwoActiveObstructionMiddle_lt
        sixVertexFourByTwoActiveObstructionGrade
        sixVertexFourByTwoActiveObstructionKey ↪
      SixVertexHorizontalActualSurplusFineUnionKeyFiber
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
        sixVertexFourByTwoActiveObstructionMiddle_pos
        sixVertexFourByTwoActiveObstructionMiddle_lt
        sixVertexFourByTwoActiveObstructionGrade
        sixVertexFourByTwoActiveCycleRepairKey where
  toFun _ := sixVertexFourByTwoActiveCycleRepairSurplusKeyFiber
  inj' := fun first second _ =>
    sixVertexFourByTwoActiveObstructionSourceKeyFiber_subsingleton first second

theorem sixVertexFourByTwoActiveObstructionCycleRepairFiberEmbedding_supported
    (source : SixVertexHorizontalActualDeficitFineUnionKeyFiber
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionMiddle_pos
      sixVertexFourByTwoActiveObstructionMiddle_lt
      sixVertexFourByTwoActiveObstructionGrade
      sixVertexFourByTwoActiveObstructionKey) :
    sixVertexHorizontalOffDiagonalTwoCycleSupport
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionMiddle_pos
      sixVertexFourByTwoActiveObstructionMiddle_lt
      sixVertexFourByTwoActiveObstructionGrade source.1
      (sixVertexFourByTwoActiveObstructionCycleRepairFiberEmbedding source).1 := by
  rw [sixVertexFourByTwoActiveObstructionSourceKeyFiber_eq source]
  exact sixVertexFourByTwoActiveObstructionToken_cycleRepair_supported

theorem sixVertexFourByTwoActiveObstructionCapacity_le_cycleRepair :
    sixVertexHorizontalActualDeficitFineUnionCapacity
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
        sixVertexFourByTwoActiveObstructionMiddle_pos
        sixVertexFourByTwoActiveObstructionMiddle_lt
        sixVertexFourByTwoActiveObstructionGrade
        sixVertexFourByTwoActiveObstructionKey ≤
      sixVertexHorizontalActualSurplusFineUnionCapacity
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
        sixVertexFourByTwoActiveObstructionMiddle_pos
        sixVertexFourByTwoActiveObstructionMiddle_lt
        sixVertexFourByTwoActiveObstructionGrade
        sixVertexFourByTwoActiveCycleRepairKey := by
  simpa only [sixVertexHorizontalActualDeficitFineUnionCapacity,
    sixVertexHorizontalActualSurplusFineUnionCapacity] using
      Fintype.card_le_of_embedding
        sixVertexFourByTwoActiveObstructionCycleRepairFiberEmbedding



theorem sixVertexFourByTwoActiveObstruction_singletonKeyCapacityHall :
    (∑ key ∈ ({sixVertexFourByTwoActiveObstructionKey} :
        Finset (SixVertexPairFineUnionKey sixVertexFourByTwoTorus)),
      sixVertexHorizontalActualDeficitFineUnionCapacity
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
        sixVertexFourByTwoActiveObstructionMiddle_pos
        sixVertexFourByTwoActiveObstructionMiddle_lt
        sixVertexFourByTwoActiveObstructionGrade key) ≤
      ∑ key ∈ (Finset.univ.filter fun targetKey =>
          exists sourceKey,
            sourceKey ∈ ({sixVertexFourByTwoActiveObstructionKey} :
              Finset (SixVertexPairFineUnionKey sixVertexFourByTwoTorus)) ∧
            SixVertexPairFineUnionKeyTwoCycleRelated sourceKey targetKey),
        sixVertexHorizontalActualSurplusFineUnionCapacity
          sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
          sixVertexFourByTwoActiveObstructionMiddle_pos
          sixVertexFourByTwoActiveObstructionMiddle_lt
          sixVertexFourByTwoActiveObstructionGrade key := by
  simp only [Finset.sum_singleton]
  refine sixVertexFourByTwoActiveObstructionCapacity_le_cycleRepair.trans ?_
  apply Finset.single_le_sum (fun _ _ => Nat.zero_le _)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨sixVertexFourByTwoActiveObstructionKey,
    Finset.mem_singleton_self _,
    sixVertexFourByTwoActiveObstructionKey_cycleRepair_related⟩

end

end StatMech.FrontierD
