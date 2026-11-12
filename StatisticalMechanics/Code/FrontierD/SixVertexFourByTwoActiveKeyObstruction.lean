/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexActiveKeyCapacityRouting
import Code.FrontierD.SixVertexPairUnionMatchingNoGo
import Code.FrontierD.SixVertexPairTwoCycleObstructionRepair










open Finset

namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoActiveObstructionGrade : Nat × Nat :=
  sixVertexHorizontalPairBigrade
    (sixVertexFourByTwoLowArrows.horizontal,
      sixVertexFourByTwoHighArrows.horizontal)

def sixVertexFourByTwoActiveLowCompletion :
    SixVertexHorizontalSectorCompletion sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorZero
      sixVertexFourByTwoLowArrows.horizontal :=
  ⟨⟨sixVertexFourByTwoLowArrows.vertical,
      sixVertexFourByTwoLowArrows_ice⟩,
    sixVertexFourByTwoLowArrows_seamCount⟩

def sixVertexFourByTwoActiveHighCompletion :
    SixVertexHorizontalSectorCompletion sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorTwo
      sixVertexFourByTwoHighArrows.horizontal :=
  ⟨⟨sixVertexFourByTwoHighArrows.vertical,
      sixVertexFourByTwoHighArrows_ice⟩,
    sixVertexFourByTwoHighArrows_seamCount⟩

section finiteChecks

local instance sixVertexFourByTwoActiveIceRuleDecidable
    (omega : SixVertexArrows sixVertexFourByTwoTorus) :
    Decidable omega.IceRule :=
  inferInstanceAs (Decidable (forall v, omega.incomingCount v = 2))

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoActiveHighMiddle_impossible
    (vertical : sixVertexFourByTwoTorus.Vertex -> Bool) :
    ¬ ((sixVertexArrowsOfFields
        sixVertexFourByTwoHighArrows.horizontal vertical).IceRule ∧
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByTwoTorus
            (sixVertexArrowsOfFields
              sixVertexFourByTwoHighArrows.horizontal vertical)
            (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1) := by
  decide +revert

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoActiveLowCompletion_vertical_unique
    (vertical : sixVertexFourByTwoTorus.Vertex -> Bool) :
    (sixVertexArrowsOfFields
          sixVertexFourByTwoLowArrows.horizontal vertical).IceRule ∧
        sixVertexUpCount
            (svTorusVerticalRows sixVertexFourByTwoTorus
              (sixVertexArrowsOfFields
                sixVertexFourByTwoLowArrows.horizontal vertical)
              (svFinLast sixVertexFourByTwoTorus.height_pos)) = 0 ->
      vertical = sixVertexFourByTwoLowArrows.vertical := by
  decide +revert

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoActiveHighCompletion_vertical_unique
    (vertical : sixVertexFourByTwoTorus.Vertex -> Bool) :
    (sixVertexArrowsOfFields
          sixVertexFourByTwoHighArrows.horizontal vertical).IceRule ∧
        sixVertexUpCount
            (svTorusVerticalRows sixVertexFourByTwoTorus
              (sixVertexArrowsOfFields
                sixVertexFourByTwoHighArrows.horizontal vertical)
              (svFinLast sixVertexFourByTwoTorus.height_pos)) = 2 ->
      vertical = sixVertexFourByTwoHighArrows.vertical := by
  decide +revert

end finiteChecks

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoActiveHighMiddle_isEmpty :
    IsEmpty
      (SixVertexHorizontalSectorCompletion sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorOne
        sixVertexFourByTwoHighArrows.horizontal) := by
  constructor
  rintro ⟨⟨vertical, hice⟩, hsector⟩
  exact sixVertexFourByTwoActiveHighMiddle_impossible vertical ⟨hice, hsector⟩

def sixVertexFourByTwoActiveObstructionProfile :
    SixVertexHorizontalPairCompletionProfile sixVertexFourByTwoTorus :=
  sixVertexHorizontalPairCompletionProfile sixVertexFourByTwoTorus
    (sixVertexFourByTwoLowArrows.horizontal,
      sixVertexFourByTwoHighArrows.horizontal)

def sixVertexFourByTwoActiveObstructionFiber :
    SixVertexHorizontalPairProfileFiber sixVertexFourByTwoTorus
      sixVertexFourByTwoActiveObstructionGrade sixVertexFourByTwoActiveObstructionProfile :=
  ⟨⟨(sixVertexFourByTwoLowArrows.horizontal,
      sixVertexFourByTwoHighArrows.horizontal), rfl⟩, rfl⟩

theorem sixVertexFourByTwoActiveObstructionProfile_deficit_pos :
    0 < sixVertexHorizontalProfileDeficit
      sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorTwo
      sixVertexFourByTwoSectorOne sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionProfile := by
  rw [sixVertexHorizontalProfileDeficit_eq_sub]
  have hsourceFirst :
      0 < sixVertexHorizontalSectorCompletionChooseCount
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorZero
        sixVertexFourByTwoLowArrows.horizontal := by
    exact sixVertexHorizontalSectorCompletionChooseCount_pos_of_nonempty
      _ _ _ ⟨sixVertexFourByTwoActiveLowCompletion⟩
  have hsourceSecond :
      0 < sixVertexHorizontalSectorCompletionChooseCount
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorTwo
        sixVertexFourByTwoHighArrows.horizontal := by
    exact sixVertexHorizontalSectorCompletionChooseCount_pos_of_nonempty
      _ _ _ ⟨sixVertexFourByTwoActiveHighCompletion⟩
  have htargetSecond :
      sixVertexHorizontalSectorCompletionChooseCount
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
        sixVertexFourByTwoHighArrows.horizontal = 0 := by
    exact sixVertexHorizontalSectorCompletionChooseCount_eq_zero_of_isEmpty
      _ _ _ sixVertexFourByTwoActiveHighMiddle_isEmpty
  change 0 <
    sixVertexHorizontalPairProfileChooseWeight
        sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorTwo
        (sixVertexHorizontalPairCompletionProfile sixVertexFourByTwoTorus
          (sixVertexFourByTwoLowArrows.horizontal,
            sixVertexFourByTwoHighArrows.horizontal)) -
      sixVertexHorizontalPairProfileChooseWeight
        sixVertexFourByTwoSectorOne sixVertexFourByTwoSectorOne
        (sixVertexHorizontalPairCompletionProfile sixVertexFourByTwoTorus
          (sixVertexFourByTwoLowArrows.horizontal,
            sixVertexFourByTwoHighArrows.horizontal))
  rw [← sixVertexHorizontalPairChooseWeight_eq_profile,
    ← sixVertexHorizontalPairChooseWeight_eq_profile]
  simp only [htargetSecond, mul_zero, Nat.sub_zero]
  positivity

def sixVertexFourByTwoActiveObstructionToken :
    SixVertexHorizontalActualDeficitTokens sixVertexFourByTwoTorus
      sixVertexFourByTwoActiveObstructionGrade sixVertexFourByTwoSectorZero
      sixVertexFourByTwoSectorTwo sixVertexFourByTwoSectorOne
      sixVertexFourByTwoSectorOne :=
  ⟨sixVertexFourByTwoActiveObstructionProfile, sixVertexFourByTwoActiveObstructionFiber,
    ⟨0, sixVertexFourByTwoActiveObstructionProfile_deficit_pos⟩⟩

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoActiveLowCompletion_unique
    (completion : SixVertexHorizontalSectorCompletion
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorZero
      sixVertexFourByTwoLowArrows.horizontal) :
    completion = sixVertexFourByTwoActiveLowCompletion := by
  rcases completion with ⟨⟨vertical, hice⟩, hsector⟩
  apply Subtype.ext
  apply Subtype.ext
  exact sixVertexFourByTwoActiveLowCompletion_vertical_unique vertical ⟨hice, hsector⟩

set_option maxRecDepth 100000 in
theorem sixVertexFourByTwoActiveHighCompletion_unique
    (completion : SixVertexHorizontalSectorCompletion
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorTwo
      sixVertexFourByTwoHighArrows.horizontal) :
    completion = sixVertexFourByTwoActiveHighCompletion := by
  rcases completion with ⟨⟨vertical, hice⟩, hsector⟩
  apply Subtype.ext
  apply Subtype.ext
  exact sixVertexFourByTwoActiveHighCompletion_vertical_unique vertical ⟨hice, hsector⟩

theorem sixVertexFourByTwoActiveObstructionCompletionPair_eq :
    sixVertexHorizontalActualDeficitCompletionPair sixVertexFourByTwoActiveObstructionToken =
      (sixVertexFourByTwoActiveLowCompletion, sixVertexFourByTwoActiveHighCompletion) := by
  apply Prod.ext
  · exact sixVertexFourByTwoActiveLowCompletion_unique _
  · exact sixVertexFourByTwoActiveHighCompletion_unique _

theorem sixVertexFourByTwoActiveObstructionConfigurationPair_eq :
    (sixVertexHorizontalActualDeficitConfigurationPair
      sixVertexFourByTwoActiveObstructionToken).1 =
      (sixVertexFourByTwoLowConfiguration,
        sixVertexFourByTwoHighConfiguration) := by
  apply Prod.ext
  · apply Subtype.ext
    apply SixVertexArrows.ext
    · rfl
    · exact congrArg (fun pair => pair.1.1.1)
        sixVertexFourByTwoActiveObstructionCompletionPair_eq
  · apply Subtype.ext
    apply SixVertexArrows.ext
    · rfl
    · exact congrArg (fun pair => pair.2.1.1)
        sixVertexFourByTwoActiveObstructionCompletionPair_eq

def sixVertexFourByTwoActiveObstructionKey : SixVertexPairFineUnionKey sixVertexFourByTwoTorus :=
  sixVertexHorizontalActualDeficitFineUnionKey sixVertexFourByTwoActiveObstructionToken

def sixVertexFourByTwoActiveCycleRepairKey :
    SixVertexPairFineUnionKey sixVertexFourByTwoTorus :=
  sixVertexPairFineUnionKey
    (sixVertexFourByTwoCycleMiddleFirst,
      sixVertexFourByTwoCycleMiddleSecond)

theorem sixVertexFourByTwoActiveObstructionKey_eq_sourceKey :
    sixVertexFourByTwoActiveObstructionKey =
      sixVertexPairFineUnionKey
        (sixVertexFourByTwoLowArrows,
          sixVertexFourByTwoHighArrows) := by
  unfold sixVertexFourByTwoActiveObstructionKey
    sixVertexHorizontalActualDeficitFineUnionKey
  exact congrArg
    (fun pair => sixVertexPairFineUnionKey (pair.1.1, pair.2.1))
    sixVertexFourByTwoActiveObstructionConfigurationPair_eq



theorem sixVertexFourByTwoActiveObstructionKey_cycleRepair_related :
    SixVertexPairFineUnionKeyTwoCycleRelated
      sixVertexFourByTwoActiveObstructionKey sixVertexFourByTwoActiveCycleRepairKey := by
  rw [sixVertexFourByTwoActiveObstructionKey_eq_sourceKey]
  exact sixVertexPairFineUnionKeyTwoCycleRelated_complete
    sixVertexFourByTwo_cycleMiddle_fineRelated

theorem sixVertexFourByTwoActiveObstructionKey_ne_cycleRepairKey :
    sixVertexFourByTwoActiveObstructionKey ≠ sixVertexFourByTwoActiveCycleRepairKey := by
  rw [sixVertexFourByTwoActiveObstructionKey_eq_sourceKey]
  intro hkey
  have hhorizontal := congrArg SixVertexPairFineUnionKey.horizontal hkey
  have hvertical := congrArg SixVertexPairFineUnionKey.vertical hkey
  apply sixVertexFourByTwo_no_unionEqual_middlePair
    sixVertexFourByTwoCycleMiddleFirst
    sixVertexFourByTwoCycleMiddleSecond
    sixVertexFourByTwoCycleMiddleFirst_ice
    sixVertexFourByTwoCycleMiddleSecond_ice
    sixVertexFourByTwoCycleMiddleFirst_seamCount
  · funext v
    have h := congrFun hhorizontal v
    have hnat :
        (sixVertexFourByTwoLowArrows.horizontal v).toNat +
            (sixVertexFourByTwoHighArrows.horizontal v).toNat =
          (sixVertexFourByTwoCycleMiddleFirst.horizontal v).toNat +
            (sixVertexFourByTwoCycleMiddleSecond.horizontal v).toNat := by
      simpa [sixVertexFourByTwoActiveCycleRepairKey, sixVertexPairFineUnionKey] using h
    unfold sixVertexPairUnionHorizontal
    exact_mod_cast hnat
  · funext v
    have h := congrFun hvertical v
    have hnat :
        (sixVertexFourByTwoLowArrows.vertical v).toNat +
            (sixVertexFourByTwoHighArrows.vertical v).toNat =
          (sixVertexFourByTwoCycleMiddleFirst.vertical v).toNat +
            (sixVertexFourByTwoCycleMiddleSecond.vertical v).toNat := by
      simpa [sixVertexFourByTwoActiveCycleRepairKey, sixVertexPairFineUnionKey] using h
    unfold sixVertexPairUnionVertical
    exact_mod_cast hnat

theorem sixVertexFourByTwoActiveObstructionMiddle_pos :
    0 < sixVertexFourByTwoSectorOne.val := by
  norm_num [sixVertexFourByTwoSectorOne]

theorem sixVertexFourByTwoActiveObstructionMiddle_lt :
    sixVertexFourByTwoSectorOne.val < sixVertexFourByTwoTorus.width := by
  norm_num [sixVertexFourByTwoSectorOne, sixVertexFourByTwoTorus]

theorem sixVertexFourByTwoActiveObstructionDeficitCapacity_pos :
    0 < sixVertexHorizontalActualDeficitFineUnionCapacity
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionMiddle_pos sixVertexFourByTwoActiveObstructionMiddle_lt
      sixVertexFourByTwoActiveObstructionGrade sixVertexFourByTwoActiveObstructionKey := by
  change 0 < Fintype.card
    {source : SixVertexHorizontalActualDeficitTokens
        sixVertexFourByTwoTorus sixVertexFourByTwoActiveObstructionGrade
        sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorTwo
        sixVertexFourByTwoSectorOne sixVertexFourByTwoSectorOne //
      sixVertexHorizontalActualDeficitFineUnionKey source =
        sixVertexFourByTwoActiveObstructionKey}
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨sixVertexFourByTwoActiveObstructionToken, rfl⟩⟩

theorem sixVertexFourByTwoActiveObstructionSurplusKeyFiber_isEmpty :
    IsEmpty
      (SixVertexHorizontalActualSurplusFineUnionKeyFiber
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
        sixVertexFourByTwoActiveObstructionMiddle_pos sixVertexFourByTwoActiveObstructionMiddle_lt
        sixVertexFourByTwoActiveObstructionGrade sixVertexFourByTwoActiveObstructionKey) := by
  constructor
  rintro ⟨target, hkey⟩
  have hkey' :
      sixVertexPairFineUnionKey
          ((sixVertexHorizontalActualSurplusConfigurationPair target).1.1.1,
            (sixVertexHorizontalActualSurplusConfigurationPair target).1.2.1) =
        sixVertexPairFineUnionKey
          (sixVertexFourByTwoLowArrows,
            sixVertexFourByTwoHighArrows) := by
    change sixVertexPairFineUnionKey
        ((sixVertexHorizontalActualSurplusConfigurationPair target).1.1.1,
          (sixVertexHorizontalActualSurplusConfigurationPair target).1.2.1) =
      sixVertexPairFineUnionKey
        ((sixVertexHorizontalActualDeficitConfigurationPair
          sixVertexFourByTwoActiveObstructionToken).1.1.1,
          (sixVertexHorizontalActualDeficitConfigurationPair
            sixVertexFourByTwoActiveObstructionToken).1.2.1) at hkey
    rw [sixVertexFourByTwoActiveObstructionConfigurationPair_eq] at hkey
    exact hkey
  have hhorizontal := congrArg SixVertexPairFineUnionKey.horizontal hkey'
  have hvertical := congrArg SixVertexPairFineUnionKey.vertical hkey'
  apply sixVertexFourByTwo_no_unionEqual_middlePair
    (sixVertexHorizontalActualSurplusConfigurationPair target).1.1.1
    (sixVertexHorizontalActualSurplusConfigurationPair target).1.2.1
  · exact (sixVertexHorizontalActualSurplusConfigurationPair target).1.1.2.1
  · exact (sixVertexHorizontalActualSurplusConfigurationPair target).1.2.2.1
  · exact (sixVertexHorizontalActualSurplusConfigurationPair target).1.1.2.2
  · funext v
    have h := congrFun hhorizontal v
    have hnat :
        (sixVertexFourByTwoLowArrows.horizontal v).toNat +
            (sixVertexFourByTwoHighArrows.horizontal v).toNat =
          (((sixVertexHorizontalActualSurplusConfigurationPair
            target).1.1.1.horizontal v).toNat +
            ((sixVertexHorizontalActualSurplusConfigurationPair
              target).1.2.1.horizontal v).toNat) := by
      simpa [sixVertexPairFineUnionKey] using h.symm
    unfold sixVertexPairUnionHorizontal
    exact_mod_cast hnat
  · funext v
    have h := congrFun hvertical v
    have hnat :
        (sixVertexFourByTwoLowArrows.vertical v).toNat +
            (sixVertexFourByTwoHighArrows.vertical v).toNat =
          (((sixVertexHorizontalActualSurplusConfigurationPair
            target).1.1.1.vertical v).toNat +
            ((sixVertexHorizontalActualSurplusConfigurationPair
              target).1.2.1.vertical v).toNat) := by
      simpa [sixVertexPairFineUnionKey] using h.symm
    unfold sixVertexPairUnionVertical
    exact_mod_cast hnat



theorem sixVertexFourByTwo_not_reflexiveActiveFiberEmbeddings :
    ¬ SixVertexHorizontalTwoCycleReflexiveActiveFiberEmbeddings
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionMiddle_pos
      sixVertexFourByTwoActiveObstructionMiddle_lt := by
  intro hembeddings
  obtain ⟨embedding⟩ := hembeddings sixVertexFourByTwoActiveObstructionGrade
    sixVertexFourByTwoActiveObstructionKey sixVertexFourByTwoActiveObstructionDeficitCapacity_pos
  let source : SixVertexHorizontalActualDeficitFineUnionKeyFiber
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionMiddle_pos sixVertexFourByTwoActiveObstructionMiddle_lt
      sixVertexFourByTwoActiveObstructionGrade sixVertexFourByTwoActiveObstructionKey :=
    ⟨sixVertexFourByTwoActiveObstructionToken, rfl⟩
  exact sixVertexFourByTwoActiveObstructionSurplusKeyFiber_isEmpty.false (embedding source)

end

end StatMech.FrontierD
