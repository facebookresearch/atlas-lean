/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexPairUnionMatchingNoGo










namespace StatMech.FrontierD

noncomputable section

local instance sixVertexTwoCycleRepairIceRuleDecidable
    {T : EvenTorus} (omega : SixVertexArrows T) :
    Decidable omega.IceRule :=
  inferInstanceAs (Decidable (forall v, omega.incomingCount v = 2))

def sixVertexFourByTwoCycleMiddleFirst :
    SixVertexArrows sixVertexFourByTwoTorus where
  horizontal v := decide
    ((v.2.val = 0 /\ v.1.val ≠ 1) \/
      (v.2.val = 1 /\ v.1.val = 1))
  vertical v := decide
    ((v.2.val = 0 /\ v.1.val = 1) \/
      (v.2.val = 1 /\ v.1.val = 2))

def sixVertexFourByTwoCycleMiddleSecond :
    SixVertexArrows sixVertexFourByTwoTorus where
  horizontal v := decide
    ((v.2.val = 0 /\ v.1.val ≤ 2) \/
      (v.2.val = 1 /\ v.1.val = 3))
  vertical v := decide
    ((v.2.val = 0 /\ v.1.val = 3) \/
      (v.2.val = 1 /\ v.1.val = 0))

theorem sixVertexFourByTwoCycleMiddleFirst_ice :
    sixVertexFourByTwoCycleMiddleFirst.IceRule := by
  decide +revert

theorem sixVertexFourByTwoCycleMiddleSecond_ice :
    sixVertexFourByTwoCycleMiddleSecond.IceRule := by
  decide +revert

theorem sixVertexFourByTwoCycleMiddleFirst_seamCount :
    sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByTwoTorus
        sixVertexFourByTwoCycleMiddleFirst
        (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 := by
  decide +revert

theorem sixVertexFourByTwoCycleMiddleSecond_seamCount :
    sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByTwoTorus
        sixVertexFourByTwoCycleMiddleSecond
        (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 := by
  decide +revert


def sixVertexFourByTwoBottomHorizontalCycle :
    SixVertexDirectedSimpleCycle sixVertexFourByTwoTorus where
  length := 4
  length_pos := by norm_num
  edge i := .horizontal (sixVertexFourByTwoVertex i 0) true
  head_eq_next_tail := by
    intro i
    fin_cases i <;>
      norm_num [SixVertexDirectedTorusEdge.head,
        SixVertexDirectedTorusEdge.tail, sixVertexFourByTwoVertex,
        finitePeriodicSucc, sixVertexFourByTwoTorus]
  tail_injective := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [SixVertexDirectedTorusEdge.tail,
        sixVertexFourByTwoVertex]
  physical_injective := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [SixVertexDirectedTorusEdge.physical,
        sixVertexFourByTwoVertex]

def sixVertexFourByTwoBottomCycleFamily :
    SixVertexAtMostTwoCycleFamily sixVertexFourByTwoTorus where
  count := 1
  count_le_two := by norm_num
  cycle _ := sixVertexFourByTwoBottomHorizontalCycle
  tail_disjoint := by
    intro i j hij
    fin_cases i
    fin_cases j
    simp at hij

theorem sixVertexFourByTwo_cycleMiddle_related :
    sixVertexPairAtMostTwoCycleRelated
      (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows)
      (sixVertexFourByTwoCycleMiddleFirst,
        sixVertexFourByTwoCycleMiddleSecond) := by
  refine ⟨sixVertexFourByTwoBottomCycleFamily, true, ?_, ?_⟩
  · funext v
    rcases v with ⟨x, y⟩
    fin_cases x <;> fin_cases y <;> decide +revert
  · funext v
    rcases v with ⟨x, y⟩
    fin_cases x <;> fin_cases y <;> decide +revert

theorem sixVertexFourByTwo_cycleMiddle_fineProfile :
    sixVertexHorizontalPairBoundedFineRowProfile
        (sixVertexFourByTwoLowArrows.horizontal,
          sixVertexFourByTwoHighArrows.horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile
        (sixVertexFourByTwoCycleMiddleFirst.horizontal,
          sixVertexFourByTwoCycleMiddleSecond.horizontal) := by
  decide +revert

theorem sixVertexFourByTwo_cycleMiddle_fineRelated :
    sixVertexPairAtMostTwoCycleFineRelated
      (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows)
      (sixVertexFourByTwoCycleMiddleFirst,
        sixVertexFourByTwoCycleMiddleSecond) :=
  ⟨sixVertexFourByTwo_cycleMiddle_related,
    sixVertexFourByTwo_cycleMiddle_fineProfile⟩



theorem sixVertexFourByTwo_exists_cycleSupported_middlePair :
    exists alpha beta : SixVertexArrows sixVertexFourByTwoTorus,
      alpha.IceRule /\ beta.IceRule /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByTwoTorus alpha
            (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByTwoTorus beta
            (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 /\
      sixVertexPairAtMostTwoCycleFineRelated
        (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows)
        (alpha, beta) := by
  exact ⟨sixVertexFourByTwoCycleMiddleFirst,
    sixVertexFourByTwoCycleMiddleSecond,
    sixVertexFourByTwoCycleMiddleFirst_ice,
    sixVertexFourByTwoCycleMiddleSecond_ice,
    sixVertexFourByTwoCycleMiddleFirst_seamCount,
    sixVertexFourByTwoCycleMiddleSecond_seamCount,
    sixVertexFourByTwo_cycleMiddle_fineRelated⟩


def sixVertexFourByTwoArrowsOfMasks
    (horizontalMask verticalMask : Nat) :
    SixVertexArrows sixVertexFourByTwoTorus where
  horizontal v := horizontalMask.testBit (v.2.val * 4 + v.1.val)
  vertical v := verticalMask.testBit (v.2.val * 4 + v.1.val)

def sixVertexFourByTwoExceptionalSourceFirst (i : Fin 4) :
    SixVertexArrows sixVertexFourByTwoTorus :=
  sixVertexFourByTwoArrowsOfMasks
    (if i.val % 2 = 0 then 0x00 else 0xff) 0x00

def sixVertexFourByTwoExceptionalSourceSecond (i : Fin 4) :
    SixVertexArrows sixVertexFourByTwoTorus :=
  sixVertexFourByTwoArrowsOfMasks
    (if i.val < 2 then 0x5a else 0xa5)
    (if i.val < 2 then 0xa5 else 0x5a)

def sixVertexFourByTwoExceptionalTargetFirst (i : Fin 4) :
    SixVertexArrows sixVertexFourByTwoTorus :=
  sixVertexFourByTwoArrowsOfMasks
    (if i.val = 0 then 0x1e else if i.val = 1 then 0xd2
      else if i.val = 2 then 0x2d else 0xe1)
    (if i.val = 0 then 0x21 else if i.val = 1 then 0x24
      else if i.val = 2 then 0x42 else 0x12)

def sixVertexFourByTwoExceptionalTargetSecond (i : Fin 4) :
    SixVertexArrows sixVertexFourByTwoTorus :=
  sixVertexFourByTwoArrowsOfMasks
    (if i.val = 0 then 0x4b else if i.val = 1 then 0x78
      else if i.val = 2 then 0x87 else 0xb4)
    (if i.val = 0 then 0x84 else if i.val = 1 then 0x81
      else if i.val = 2 then 0x18 else 0x48)

def sixVertexFourByTwoExceptionalCycleSign (i : Fin 4) : Bool :=
  decide (i.val % 2 = 0)

theorem sixVertexFourByTwoExceptional_valid (i : Fin 4) :
    (sixVertexFourByTwoExceptionalSourceFirst i).IceRule /\
      (sixVertexFourByTwoExceptionalSourceSecond i).IceRule /\
      (sixVertexFourByTwoExceptionalTargetFirst i).IceRule /\
      (sixVertexFourByTwoExceptionalTargetSecond i).IceRule /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByTwoTorus
            (sixVertexFourByTwoExceptionalSourceFirst i)
            (svFinLast sixVertexFourByTwoTorus.height_pos)) = 0 /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByTwoTorus
            (sixVertexFourByTwoExceptionalSourceSecond i)
            (svFinLast sixVertexFourByTwoTorus.height_pos)) = 2 /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByTwoTorus
            (sixVertexFourByTwoExceptionalTargetFirst i)
            (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByTwoTorus
            (sixVertexFourByTwoExceptionalTargetSecond i)
            (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 := by
  fin_cases i <;> decide +revert

theorem sixVertexFourByTwoExceptional_related (i : Fin 4) :
    sixVertexPairAtMostTwoCycleRelated
      (sixVertexFourByTwoExceptionalSourceFirst i,
        sixVertexFourByTwoExceptionalSourceSecond i)
      (sixVertexFourByTwoExceptionalTargetFirst i,
        sixVertexFourByTwoExceptionalTargetSecond i) := by
  refine ⟨sixVertexFourByTwoBottomCycleFamily,
    sixVertexFourByTwoExceptionalCycleSign i, ?_, ?_⟩
  · funext v
    rcases v with ⟨x, y⟩
    fin_cases i <;> fin_cases x <;> fin_cases y <;> decide +revert
  · funext v
    rcases v with ⟨x, y⟩
    fin_cases i <;> fin_cases x <;> fin_cases y <;> decide +revert

theorem sixVertexFourByTwoExceptional_fineProfile (i : Fin 4) :
    sixVertexHorizontalPairBoundedFineRowProfile
        ((sixVertexFourByTwoExceptionalSourceFirst i).horizontal,
          (sixVertexFourByTwoExceptionalSourceSecond i).horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile
        ((sixVertexFourByTwoExceptionalTargetFirst i).horizontal,
          (sixVertexFourByTwoExceptionalTargetSecond i).horizontal) := by
  fin_cases i <;> decide +revert




theorem sixVertexFourByTwoExceptional_fineRelated (i : Fin 4) :
    sixVertexPairAtMostTwoCycleFineRelated
      (sixVertexFourByTwoExceptionalSourceFirst i,
        sixVertexFourByTwoExceptionalSourceSecond i)
      (sixVertexFourByTwoExceptionalTargetFirst i,
        sixVertexFourByTwoExceptionalTargetSecond i) :=
  ⟨sixVertexFourByTwoExceptional_related i,
    sixVertexFourByTwoExceptional_fineProfile i⟩

end

end StatMech.FrontierD
