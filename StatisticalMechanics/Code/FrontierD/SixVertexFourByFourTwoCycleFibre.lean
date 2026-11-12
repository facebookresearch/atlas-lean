/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexFourByTwoTwoCycleHall
import Code.FrontierD.SixVertexFourByFourRowCycleBase









namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByFourVertex (x y : Nat) :
    sixVertexFourByFourTorus.Vertex :=
  (⟨x % 4, Nat.mod_lt _ (by norm_num)⟩,
    ⟨y % 4, Nat.mod_lt _ (by norm_num)⟩)

def sixVertexFourByFourArrowsOfMasks
    (horizontalMask verticalMask : Nat) :
    SixVertexArrows sixVertexFourByFourTorus where
  horizontal v := horizontalMask.testBit (v.2.val * 4 + v.1.val)
  vertical v := verticalMask.testBit (v.2.val * 4 + v.1.val)

def sixVertexFourByFourReverseRow : Fin 4 -> Fin 4 := ![0, 3, 2, 1]


def sixVertexFourByFourVerticalColumnCycle
    (x : Fin 4) (positive : Bool) :
    SixVertexDirectedSimpleCycle sixVertexFourByFourTorus where
  length := 4
  length_pos := by norm_num
  edge i := if positive then
      .vertical (x, i) true
    else
      .vertical (x, sixVertexFourByFourReverseRow i) false
  head_eq_next_tail := by
    intro i
    fin_cases positive <;> fin_cases i <;>
      apply Prod.ext <;> apply Fin.ext <;>
      norm_num [SixVertexDirectedTorusEdge.head,
          SixVertexDirectedTorusEdge.tail,
          sixVertexFourByFourReverseRow, finitePeriodicSucc,
          sixVertexFourByFourTorus]
  tail_injective := by
    intro i j hij
    fin_cases positive <;> fin_cases i <;> fin_cases j <;>
      simp_all [SixVertexDirectedTorusEdge.tail,
        sixVertexFourByFourReverseRow, finitePeriodicSucc,
        sixVertexFourByFourTorus]
  physical_injective := by
    intro i j hij
    fin_cases positive <;> fin_cases i <;> fin_cases j <;>
      simp_all [SixVertexDirectedTorusEdge.physical,
        sixVertexFourByFourReverseRow]



def sixVertexFourByFourOppositeVerticalColumnFamily
    (positiveColumn negativeColumn : Fin 4)
    (hne : positiveColumn ≠ negativeColumn) :
    SixVertexAtMostTwoCycleFamily sixVertexFourByFourTorus where
  count := 2
  count_le_two := by norm_num
  cycle i := if i = 0 then
      sixVertexFourByFourVerticalColumnCycle positiveColumn true
    else
      sixVertexFourByFourVerticalColumnCycle negativeColumn false
  tail_disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · simp at hij
    · intro a b
      simp [sixVertexFourByFourVerticalColumnCycle,
        SixVertexDirectedTorusEdge.tail,
        sixVertexFourByFourReverseRow]
      intro hcolumns
      exact (hne hcolumns).elim
    · intro a b
      simp [sixVertexFourByFourVerticalColumnCycle,
        SixVertexDirectedTorusEdge.tail,
        sixVertexFourByFourReverseRow]
      intro hcolumns
      exact (hne hcolumns.symm).elim
    · simp at hij

theorem sixVertexFourByFourOppositeVerticalColumnFamily_horizontalFlow
    (firstColumn secondColumn : Fin 4) (hne : firstColumn ≠ secondColumn)
    (v : sixVertexFourByFourTorus.Vertex) :
    (sixVertexFourByFourOppositeVerticalColumnFamily
      firstColumn secondColumn hne).horizontalFlow v = 0 := by
  rcases v with ⟨x, y⟩
  unfold SixVertexAtMostTwoCycleFamily.horizontalFlow
  simp only [sixVertexFourByFourOppositeVerticalColumnFamily]
  change (∑ i : Fin 2,
      (if i = 0 then
        sixVertexFourByFourVerticalColumnCycle firstColumn true
      else sixVertexFourByFourVerticalColumnCycle secondColumn false).horizontalFlow
        (x, y)) = 0
  rw [Fin.sum_univ_two]
  simp only [if_neg (by decide : (1 : Fin 2) ≠ 0), ite_true]
  unfold SixVertexDirectedSimpleCycle.horizontalFlow
  simp only [sixVertexFourByFourVerticalColumnCycle]
  simp only [ite_true, Bool.false_eq_true, if_false]
  change (∑ i : Fin 4,
      (SixVertexDirectedTorusEdge.vertical (firstColumn, i) true).horizontalFlow
        (x, y)) +
    (∑ i : Fin 4,
      (SixVertexDirectedTorusEdge.vertical
        (secondColumn, sixVertexFourByFourReverseRow i) false).horizontalFlow
          (x, y)) = 0
  rw [Fin.sum_univ_four, Fin.sum_univ_four]
  simp [SixVertexDirectedTorusEdge.horizontalFlow]

set_option maxHeartbeats 1000000 in

theorem sixVertexFourByFourOppositeVerticalColumnFamily_verticalFlow
    (firstColumn secondColumn : Fin 4) (hne : firstColumn ≠ secondColumn)
    (x y : Fin 4) :
    (sixVertexFourByFourOppositeVerticalColumnFamily
      firstColumn secondColumn hne).verticalFlow (x, y) =
      (if x = firstColumn then 1 else if x = secondColumn then -1 else 0) := by
  unfold SixVertexAtMostTwoCycleFamily.verticalFlow
  simp only [sixVertexFourByFourOppositeVerticalColumnFamily]
  change (∑ i : Fin 2,
      (if i = 0 then
        sixVertexFourByFourVerticalColumnCycle firstColumn true
      else sixVertexFourByFourVerticalColumnCycle secondColumn false).verticalFlow
        (x, y)) = _
  rw [Fin.sum_univ_two]
  simp only [if_neg (by decide : (1 : Fin 2) ≠ 0), ite_true]
  unfold SixVertexDirectedSimpleCycle.verticalFlow
  simp only [sixVertexFourByFourVerticalColumnCycle]
  simp only [ite_true, Bool.false_eq_true, if_false]
  change (∑ i : Fin 4,
      (SixVertexDirectedTorusEdge.vertical (firstColumn, i) true).verticalFlow
        ((x, y) : sixVertexFourByFourTorus.Vertex)) +
    (∑ i : Fin 4,
      (SixVertexDirectedTorusEdge.vertical
        (secondColumn, sixVertexFourByFourReverseRow i) false).verticalFlow
          ((x, y) : sixVertexFourByFourTorus.Vertex)) = _
  rw [Fin.sum_univ_four, Fin.sum_univ_four]
  fin_cases firstColumn <;> fin_cases secondColumn <;>
    fin_cases x <;> fin_cases y <;>
    simp_all [SixVertexDirectedTorusEdge.verticalFlow,
      sixVertexFourByFourReverseRow]

def sixVertexFourByFourAuditedSourceFirst :
    SixVertexArrows sixVertexFourByFourTorus :=
  sixVertexFourByFourArrowsOfMasks 0x003c 0x4441

def sixVertexFourByFourAuditedSourceSecond :
    SixVertexArrows sixVertexFourByFourTorus :=
  sixVertexFourByFourArrowsOfMasks 0x0609 0xdd77

def sixVertexFourByFourAuditedTargetFirst :
    SixVertexArrows sixVertexFourByFourTorus :=
  sixVertexFourByFourArrowsOfMasks 0x003c 0x6663

def sixVertexFourByFourAuditedTargetSecond :
    SixVertexArrows sixVertexFourByFourTorus :=
  sixVertexFourByFourArrowsOfMasks 0x0609 0x9933

local instance sixVertexFourByFourIceRuleDecidable
    (omega : SixVertexArrows sixVertexFourByFourTorus) :
    Decidable omega.IceRule :=
  inferInstanceAs (Decidable (forall v, omega.incomingCount v = 2))

theorem sixVertexFourByFourAudited_valid :
    sixVertexFourByFourAuditedSourceFirst.IceRule /\
      sixVertexFourByFourAuditedSourceSecond.IceRule /\
      sixVertexFourByFourAuditedTargetFirst.IceRule /\
      sixVertexFourByFourAuditedTargetSecond.IceRule /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByFourTorus
            sixVertexFourByFourAuditedSourceFirst
            (svFinLast sixVertexFourByFourTorus.height_pos)) = 1 /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByFourTorus
            sixVertexFourByFourAuditedSourceSecond
            (svFinLast sixVertexFourByFourTorus.height_pos)) = 3 /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByFourTorus
            sixVertexFourByFourAuditedTargetFirst
            (svFinLast sixVertexFourByFourTorus.height_pos)) = 2 /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByFourTorus
            sixVertexFourByFourAuditedTargetSecond
            (svFinLast sixVertexFourByFourTorus.height_pos)) = 2 := by
  decide +revert



theorem sixVertexFourByFourAudited_twoCycleRelated :
    sixVertexPairAtMostTwoCycleRelated
      (sixVertexFourByFourAuditedSourceFirst,
        sixVertexFourByFourAuditedSourceSecond)
      (sixVertexFourByFourAuditedTargetFirst,
        sixVertexFourByFourAuditedTargetSecond) := by
  let family := sixVertexFourByFourOppositeVerticalColumnFamily
    (1 : Fin 4) (2 : Fin 4) (by decide)
  refine ⟨family, true, ?_, ?_⟩
  · funext v
    rcases v with ⟨x, y⟩
    fin_cases x <;> fin_cases y <;> decide +revert
  · funext v
    rcases v with ⟨x, y⟩
    fin_cases x <;> fin_cases y <;> decide +revert

theorem sixVertexFourByFourAudited_fineRelated :
    sixVertexPairAtMostTwoCycleFineRelated
      (sixVertexFourByFourAuditedSourceFirst,
        sixVertexFourByFourAuditedSourceSecond)
      (sixVertexFourByFourAuditedTargetFirst,
        sixVertexFourByFourAuditedTargetSecond) :=
  ⟨sixVertexFourByFourAudited_twoCycleRelated, rfl⟩


abbrev SixVertexFourByFourAuditedHorizontalParameters :=
  Fin 16 × Fin 16 × Fin 16 × Fin 4

def sixVertexFourByFourAuditedRowZero : Fin 16 -> Nat × Nat := ![
  (3, 3), (3, 6), (3, 9), (3, 12),
  (6, 3), (6, 6), (6, 9), (6, 12),
  (9, 3), (9, 6), (9, 9), (9, 12),
  (12, 3), (12, 6), (12, 9), (12, 12)
]

def sixVertexFourByFourAuditedRowMiddle : Fin 16 -> Nat × Nat := ![
  (0, 3), (0, 6), (0, 9), (0, 12),
  (3, 0), (3, 15), (6, 0), (6, 15),
  (9, 0), (9, 15), (12, 0), (12, 15),
  (15, 3), (15, 6), (15, 9), (15, 12)
]

def sixVertexFourByFourAuditedRowLast : Fin 4 -> Nat × Nat := ![
  (0, 0), (0, 15), (15, 0), (15, 15)
]

def sixVertexFourByFourMaskOfRowMasks (rows : Fin 4 -> Nat) : Nat :=
  Nat.ofBits fun i : Fin 16 =>
    let yx := (finProdFinEquiv (m := 4) (n := 4)).symm i
    (rows yx.1).testBit yx.2.val

theorem sixVertexFourByFourMaskOfRowMasks_apply
    (rows : Fin 4 -> Nat) (x y : Fin 4) :
    (sixVertexFourByFourMaskOfRowMasks rows).testBit (y.val * 4 + x.val) =
      (rows y).testBit x.val := by
  let i : Fin 16 := finProdFinEquiv (m := 4) (n := 4) (y, x)
  change (Nat.ofBits _).testBit (y.val * 4 + x.val) = _
  have hval : y.val * 4 + x.val = i.val := by
    simp [i, finProdFinEquiv]
    omega
  rw [hval, Nat.testBit_ofBits_lt _ i.val i.isLt]
  change ((rows ((finProdFinEquiv (m := 4) (n := 4)).symm i).1).testBit
        ((finProdFinEquiv (m := 4) (n := 4)).symm i).2.val) = _
  rw [(finProdFinEquiv (m := 4) (n := 4)).symm_apply_apply]

@[simp] theorem sixVertexFourByFourMaskOfRowMasks_testBit_zero
    (rows : Fin 4 -> Nat) (x : Fin 4) :
    (sixVertexFourByFourMaskOfRowMasks rows).testBit x.val =
      (rows 0).testBit x.val := by
  simpa using sixVertexFourByFourMaskOfRowMasks_apply rows x 0

@[simp] theorem sixVertexFourByFourMaskOfRowMasks_testBit_one
    (rows : Fin 4 -> Nat) (x : Fin 4) :
    (sixVertexFourByFourMaskOfRowMasks rows).testBit (4 + x.val) =
      (rows 1).testBit x.val := by
  simpa [Nat.add_comm] using sixVertexFourByFourMaskOfRowMasks_apply rows x 1

@[simp] theorem sixVertexFourByFourMaskOfRowMasks_testBit_two
    (rows : Fin 4 -> Nat) (x : Fin 4) :
    (sixVertexFourByFourMaskOfRowMasks rows).testBit (8 + x.val) =
      (rows 2).testBit x.val := by
  simpa [Nat.add_comm] using sixVertexFourByFourMaskOfRowMasks_apply rows x 2

@[simp] theorem sixVertexFourByFourMaskOfRowMasks_testBit_three
    (rows : Fin 4 -> Nat) (x : Fin 4) :
    (sixVertexFourByFourMaskOfRowMasks rows).testBit (12 + x.val) =
      (rows 3).testBit x.val := by
  simpa [Nat.add_comm] using sixVertexFourByFourMaskOfRowMasks_apply rows x 3

def sixVertexFourByFourAuditedHorizontalMasks
    (p : SixVertexFourByFourAuditedHorizontalParameters) : Nat × Nat :=
  let rowZero := sixVertexFourByFourAuditedRowZero p.1
  let rowOne := sixVertexFourByFourAuditedRowMiddle p.2.1
  let rowTwo := sixVertexFourByFourAuditedRowMiddle p.2.2.1
  let rowThree := sixVertexFourByFourAuditedRowLast p.2.2.2
  (sixVertexFourByFourMaskOfRowMasks
      ![rowZero.1, rowOne.1, rowTwo.1, rowThree.1],
    sixVertexFourByFourMaskOfRowMasks
      ![rowZero.2, rowOne.2, rowTwo.2, rowThree.2])

def sixVertexFourByFourSectorOneSeamMask : Fin 4 -> Nat := ![1, 2, 4, 8]

def sixVertexFourByFourSectorThreeSeamMask : Fin 4 -> Nat := ![7, 11, 13, 14]

def sixVertexFourByFourRowOfMask (mask : Nat) : SixVertexRow 4 :=
  fun x => mask.testBit x.val

def sixVertexFourByFourNextVerticalRow
    (horizontal below : SixVertexRow 4) : SixVertexRow 4 :=
  fun x => decide
    ((horizontal (SixVertexArrows.cyclicPred (by norm_num) x)).toNat +
        (!horizontal x).toNat + (below x).toNat = 2)

def sixVertexFourByFourEvenUpCount (row : SixVertexRow 4) : Nat :=
  (row 0).toNat + (row 2).toNat

def sixVertexFourByFourAllowedHorizontalMask : Fin 6 -> Nat :=
  ![0, 3, 6, 9, 12, 15]

theorem sixVertexFourByFourEvenUpCount_preserved
    (i : Fin 6) (previous current : SixVertexRow 4)
    (hice : svHorizontalIce (by norm_num) previous current
      (sixVertexFourByFourRowOfMask
        (sixVertexFourByFourAllowedHorizontalMask i))) :
    sixVertexFourByFourEvenUpCount previous =
      sixVertexFourByFourEvenUpCount current := by
  unfold svHorizontalIce svHorizontalIncomingCount at hice
  unfold sixVertexFourByFourEvenUpCount at ⊢
  unfold sixVertexFourByFourRowOfMask at hice
  unfold sixVertexFourByFourAllowedHorizontalMask at hice
  fin_cases i <;> decide +revert

theorem sixVertexFourByFourNextVerticalRow_ice_of_upCount_eq
    (i : Fin 6) (below : SixVertexRow 4)
    (hcount : sixVertexUpCount
      (sixVertexFourByFourNextVerticalRow
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourAllowedHorizontalMask i)) below) =
      sixVertexUpCount below) :
    svHorizontalIce (by norm_num) below
      (sixVertexFourByFourNextVerticalRow
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourAllowedHorizontalMask i)) below)
      (sixVertexFourByFourRowOfMask
        (sixVertexFourByFourAllowedHorizontalMask i)) := by
  unfold svHorizontalIce svHorizontalIncomingCount
  fin_cases i <;> revert below <;> decide

theorem sixVertexFourByFourFirstRowZero_even
    (p0 : Fin 16) (seam : Fin 4)
    (hcount : sixVertexUpCount
      (sixVertexFourByFourNextVerticalRow
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourAuditedRowZero p0).1)
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourSectorOneSeamMask seam))) = 1) :
    sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourNextVerticalRow
          (sixVertexFourByFourRowOfMask
            (sixVertexFourByFourAuditedRowZero p0).1)
          (sixVertexFourByFourRowOfMask
            (sixVertexFourByFourSectorOneSeamMask seam))) =
      sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourSectorOneSeamMask seam)) := by
  fin_cases p0 <;> fin_cases seam <;> revert hcount <;> decide

theorem sixVertexFourByFourSecondRowZero_even
    (p0 : Fin 16) (seam : Fin 4)
    (hcount : sixVertexUpCount
      (sixVertexFourByFourNextVerticalRow
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourAuditedRowZero p0).2)
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourSectorThreeSeamMask seam))) = 3) :
    sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourNextVerticalRow
          (sixVertexFourByFourRowOfMask
            (sixVertexFourByFourAuditedRowZero p0).2)
          (sixVertexFourByFourRowOfMask
            (sixVertexFourByFourSectorThreeSeamMask seam))) =
      sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourSectorThreeSeamMask seam)) := by
  fin_cases p0 <;> fin_cases seam <;> revert hcount <;> decide

def sixVertexFourByFourAllowedHorizontalIndex (mask : Nat) : Fin 6 :=
  if mask = 0 then 0 else if mask = 3 then 1 else if mask = 6 then 2
  else if mask = 9 then 3 else if mask = 12 then 4 else 5

@[simp] theorem sixVertexFourByFourAllowedHorizontalIndex_rowZero_first
    (p : Fin 16) :
    sixVertexFourByFourAllowedHorizontalMask
        (sixVertexFourByFourAllowedHorizontalIndex
          (sixVertexFourByFourAuditedRowZero p).1) =
      (sixVertexFourByFourAuditedRowZero p).1 := by
  fin_cases p <;> decide

@[simp] theorem sixVertexFourByFourAllowedHorizontalIndex_rowZero_second
    (p : Fin 16) :
    sixVertexFourByFourAllowedHorizontalMask
        (sixVertexFourByFourAllowedHorizontalIndex
          (sixVertexFourByFourAuditedRowZero p).2) =
      (sixVertexFourByFourAuditedRowZero p).2 := by
  fin_cases p <;> decide

@[simp] theorem sixVertexFourByFourAllowedHorizontalIndex_rowMiddle_first
    (p : Fin 16) :
    sixVertexFourByFourAllowedHorizontalMask
        (sixVertexFourByFourAllowedHorizontalIndex
          (sixVertexFourByFourAuditedRowMiddle p).1) =
      (sixVertexFourByFourAuditedRowMiddle p).1 := by
  fin_cases p <;> decide

@[simp] theorem sixVertexFourByFourAllowedHorizontalIndex_rowMiddle_second
    (p : Fin 16) :
    sixVertexFourByFourAllowedHorizontalMask
        (sixVertexFourByFourAllowedHorizontalIndex
          (sixVertexFourByFourAuditedRowMiddle p).2) =
      (sixVertexFourByFourAuditedRowMiddle p).2 := by
  fin_cases p <;> decide

@[simp] theorem sixVertexFourByFourAllowedHorizontalIndex_rowLast_first
    (p : Fin 4) :
    sixVertexFourByFourAllowedHorizontalMask
        (sixVertexFourByFourAllowedHorizontalIndex
          (sixVertexFourByFourAuditedRowLast p).1) =
      (sixVertexFourByFourAuditedRowLast p).1 := by
  fin_cases p <;> decide

@[simp] theorem sixVertexFourByFourAllowedHorizontalIndex_rowLast_second
    (p : Fin 4) :
    sixVertexFourByFourAllowedHorizontalMask
        (sixVertexFourByFourAllowedHorizontalIndex
          (sixVertexFourByFourAuditedRowLast p).2) =
      (sixVertexFourByFourAuditedRowLast p).2 := by
  fin_cases p <;> decide

def sixVertexFourByFourAuditedParamHorizontalRowsFirst
    (p : SixVertexFourByFourAuditedHorizontalParameters) :
    Fin 4 -> SixVertexRow 4 := ![
  sixVertexFourByFourRowOfMask (sixVertexFourByFourAllowedHorizontalMask
    (sixVertexFourByFourAllowedHorizontalIndex
      (sixVertexFourByFourAuditedRowZero p.1).1)),
  sixVertexFourByFourRowOfMask (sixVertexFourByFourAllowedHorizontalMask
    (sixVertexFourByFourAllowedHorizontalIndex
      (sixVertexFourByFourAuditedRowMiddle p.2.1).1)),
  sixVertexFourByFourRowOfMask (sixVertexFourByFourAllowedHorizontalMask
    (sixVertexFourByFourAllowedHorizontalIndex
      (sixVertexFourByFourAuditedRowMiddle p.2.2.1).1)),
  sixVertexFourByFourRowOfMask (sixVertexFourByFourAllowedHorizontalMask
    (sixVertexFourByFourAllowedHorizontalIndex
      (sixVertexFourByFourAuditedRowLast p.2.2.2).1))
]

def sixVertexFourByFourAuditedParamHorizontalRowsSecond
    (p : SixVertexFourByFourAuditedHorizontalParameters) :
    Fin 4 -> SixVertexRow 4 := ![
  sixVertexFourByFourRowOfMask (sixVertexFourByFourAllowedHorizontalMask
    (sixVertexFourByFourAllowedHorizontalIndex
      (sixVertexFourByFourAuditedRowZero p.1).2)),
  sixVertexFourByFourRowOfMask (sixVertexFourByFourAllowedHorizontalMask
    (sixVertexFourByFourAllowedHorizontalIndex
      (sixVertexFourByFourAuditedRowMiddle p.2.1).2)),
  sixVertexFourByFourRowOfMask (sixVertexFourByFourAllowedHorizontalMask
    (sixVertexFourByFourAllowedHorizontalIndex
      (sixVertexFourByFourAuditedRowMiddle p.2.2.1).2)),
  sixVertexFourByFourRowOfMask (sixVertexFourByFourAllowedHorizontalMask
    (sixVertexFourByFourAllowedHorizontalIndex
      (sixVertexFourByFourAuditedRowLast p.2.2.2).2))
]

theorem sixVertexFourByFourAuditedParamHorizontalRowsFirst_allowed
    (p : SixVertexFourByFourAuditedHorizontalParameters) (y : Fin 4) :
    ∃ i, sixVertexFourByFourAuditedParamHorizontalRowsFirst p y =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourAllowedHorizontalMask i) := by
  fin_cases y <;> exact ⟨_, rfl⟩

theorem sixVertexFourByFourAuditedParamHorizontalRowsSecond_allowed
    (p : SixVertexFourByFourAuditedHorizontalParameters) (y : Fin 4) :
    ∃ i, sixVertexFourByFourAuditedParamHorizontalRowsSecond p y =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourAllowedHorizontalMask i) := by
  fin_cases y <;> exact ⟨_, rfl⟩

def sixVertexFourByFourAuditedParamVerticalRowsFirst
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam : Fin 4) :
    Fin 4 -> SixVertexRow 4 :=
  let horizontal := sixVertexFourByFourAuditedParamHorizontalRowsFirst p
  let seamRow :=
    sixVertexFourByFourRowOfMask (sixVertexFourByFourSectorOneSeamMask seam)
  let verticalZero :=
    sixVertexFourByFourNextVerticalRow (horizontal 0) seamRow
  let verticalOne :=
    sixVertexFourByFourNextVerticalRow (horizontal 1) verticalZero
  let verticalTwo :=
    sixVertexFourByFourNextVerticalRow (horizontal 2) verticalOne
  let verticalThree :=
    sixVertexFourByFourNextVerticalRow (horizontal 3) verticalTwo
  ![verticalZero, verticalOne, verticalTwo, verticalThree]

def sixVertexFourByFourAuditedParamVerticalRowsSecond
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam : Fin 4) :
    Fin 4 -> SixVertexRow 4 :=
  let horizontal := sixVertexFourByFourAuditedParamHorizontalRowsSecond p
  let seamRow :=
    sixVertexFourByFourRowOfMask (sixVertexFourByFourSectorThreeSeamMask seam)
  let verticalZero :=
    sixVertexFourByFourNextVerticalRow (horizontal 0) seamRow
  let verticalOne :=
    sixVertexFourByFourNextVerticalRow (horizontal 1) verticalZero
  let verticalTwo :=
    sixVertexFourByFourNextVerticalRow (horizontal 2) verticalOne
  let verticalThree :=
    sixVertexFourByFourNextVerticalRow (horizontal 3) verticalTwo
  ![verticalZero, verticalOne, verticalTwo, verticalThree]

def sixVertexFourByFourVerticalMaskOfRows
    (rows : Fin 4 -> SixVertexRow 4) : Nat :=
  Nat.ofBits fun i : Fin 16 =>
    let yx := (finProdFinEquiv (m := 4) (n := 4)).symm i
    rows yx.1 yx.2

theorem sixVertexFourByFourVerticalMaskOfRows_apply
    (rows : Fin 4 -> SixVertexRow 4) (x y : Fin 4) :
    (sixVertexFourByFourVerticalMaskOfRows rows).testBit (y.val * 4 + x.val) =
      rows y x := by
  let i : Fin 16 := finProdFinEquiv (m := 4) (n := 4) (y, x)
  change (Nat.ofBits _).testBit (y.val * 4 + x.val) = _
  have hval : y.val * 4 + x.val = i.val := by
    simp [i, finProdFinEquiv]
    omega
  rw [hval, Nat.testBit_ofBits_lt _ i.val i.isLt]
  change rows ((finProdFinEquiv (m := 4) (n := 4)).symm i).1
      ((finProdFinEquiv (m := 4) (n := 4)).symm i).2 = _
  rw [(finProdFinEquiv (m := 4) (n := 4)).symm_apply_apply]

def sixVertexFourByFourVerticalNext
    (horizontalMask : Nat) (x y : Fin 4) (below : Bool) : Bool :=
  decide
    ((horizontalMask.testBit
          (y.val * 4 + (SixVertexArrows.cyclicPred (by norm_num) x).val)).toNat +
        (!horizontalMask.testBit (y.val * 4 + x.val)).toNat +
        below.toNat = 2)

def sixVertexFourByFourCompletedVerticalColumn
    (horizontalMask seamMask : Nat) (x : Fin 4) : Fin 4 -> Bool :=
  let seam := seamMask.testBit x.val
  let v0 := sixVertexFourByFourVerticalNext horizontalMask x 0 seam
  let v1 := sixVertexFourByFourVerticalNext horizontalMask x 1 v0
  let v2 := sixVertexFourByFourVerticalNext horizontalMask x 2 v1
  let v3 := sixVertexFourByFourVerticalNext horizontalMask x 3 v2
  ![v0, v1, v2, v3]

def sixVertexFourByFourCompletedVerticalMask
    (horizontalMask seamMask : Nat) : Nat :=
  Nat.ofBits fun i : Fin 16 =>
    let yx := (finProdFinEquiv (m := 4) (n := 4)).symm i
    sixVertexFourByFourCompletedVerticalColumn
      horizontalMask seamMask yx.2 yx.1

def sixVertexFourByFourCompletedVerticalRow
    (horizontalMask seamMask : Nat) (y : Fin 4) : SixVertexRow 4 :=
  fun x => sixVertexFourByFourCompletedVerticalColumn horizontalMask seamMask x y

theorem sixVertexFourByFourCompletedVerticalMask_row
    (horizontalMask seamMask : Nat) (x y : Fin 4) :
    (sixVertexFourByFourArrowsOfMasks horizontalMask
      (sixVertexFourByFourCompletedVerticalMask horizontalMask seamMask)).vertical
        (x, y) =
      sixVertexFourByFourCompletedVerticalRow horizontalMask seamMask y x := by
  unfold sixVertexFourByFourArrowsOfMasks
  unfold sixVertexFourByFourCompletedVerticalMask
  unfold sixVertexFourByFourCompletedVerticalRow
  let i : Fin 16 := finProdFinEquiv (m := 4) (n := 4) (y, x)
  change (Nat.ofBits _).testBit (y.val * 4 + x.val) = _
  have hval : y.val * 4 + x.val = i.val := by
    simp [i, finProdFinEquiv]
    omega
  rw [hval, Nat.testBit_ofBits_lt _ i.val i.isLt]
  change sixVertexFourByFourCompletedVerticalColumn horizontalMask seamMask
      ((finProdFinEquiv (m := 4) (n := 4)).symm i).2
      ((finProdFinEquiv (m := 4) (n := 4)).symm i).1 = _
  rw [(finProdFinEquiv (m := 4) (n := 4)).symm_apply_apply]

theorem sixVertexFourByFourCompletedVerticalColumn_auditedFirst
    (p : SixVertexFourByFourAuditedHorizontalParameters)
    (seam x y : Fin 4) :
    sixVertexFourByFourCompletedVerticalColumn
        (sixVertexFourByFourAuditedHorizontalMasks p).1
        (sixVertexFourByFourSectorOneSeamMask seam) x y =
      sixVertexFourByFourAuditedParamVerticalRowsFirst p seam y x := by
  fin_cases y <;>
    simp [sixVertexFourByFourCompletedVerticalColumn,
      sixVertexFourByFourVerticalNext,
      sixVertexFourByFourAuditedHorizontalMasks,
      sixVertexFourByFourAuditedParamVerticalRowsFirst,
      sixVertexFourByFourAuditedParamHorizontalRowsFirst,
      sixVertexFourByFourNextVerticalRow,
      sixVertexFourByFourRowOfMask] <;> rfl

theorem sixVertexFourByFourCompletedVerticalColumn_auditedSecond
    (p : SixVertexFourByFourAuditedHorizontalParameters)
    (seam x y : Fin 4) :
    sixVertexFourByFourCompletedVerticalColumn
        (sixVertexFourByFourAuditedHorizontalMasks p).2
        (sixVertexFourByFourSectorThreeSeamMask seam) x y =
      sixVertexFourByFourAuditedParamVerticalRowsSecond p seam y x := by
  fin_cases y <;>
    simp [sixVertexFourByFourCompletedVerticalColumn,
      sixVertexFourByFourVerticalNext,
      sixVertexFourByFourAuditedHorizontalMasks,
      sixVertexFourByFourAuditedParamVerticalRowsSecond,
      sixVertexFourByFourAuditedParamHorizontalRowsSecond,
      sixVertexFourByFourNextVerticalRow,
      sixVertexFourByFourRowOfMask] <;> rfl

theorem sixVertexFourByFour_rowIce
    (omega : SixVertexArrows sixVertexFourByFourTorus)
    (hice : omega.IceRule) (y : Fin 4) :
    svHorizontalIce sixVertexFourByFourTorus.width_pos
      (svTorusVerticalRows sixVertexFourByFourTorus omega
        (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y))
      (svTorusVerticalRows sixVertexFourByFourTorus omega y)
      (svTorusHorizontalRows sixVertexFourByFourTorus omega y) := by
  intro x
  simpa [svHorizontalIncomingCount, svTorusVerticalRows,
    svTorusHorizontalRows, SixVertexArrows.incomingCount,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    using hice (x, y)

theorem sixVertexFourByFour_verticalRowCount_eq_last
    (omega : SixVertexArrows sixVertexFourByFourTorus)
    (hice : omega.IceRule) (y : Fin 4) :
    sixVertexUpCount (svTorusVerticalRows sixVertexFourByFourTorus omega y) =
      sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus omega
          (svFinLast sixVertexFourByFourTorus.height_pos)) := by
  have h0 := svHorizontalIce_upCount_eq sixVertexFourByFourTorus.width_pos
    (sixVertexFourByFour_rowIce omega hice 0)
  have h1 := svHorizontalIce_upCount_eq sixVertexFourByFourTorus.width_pos
    (sixVertexFourByFour_rowIce omega hice 1)
  have h2 := svHorizontalIce_upCount_eq sixVertexFourByFourTorus.width_pos
    (sixVertexFourByFour_rowIce omega hice 2)
  have h3 := svHorizontalIce_upCount_eq sixVertexFourByFourTorus.width_pos
    (sixVertexFourByFour_rowIce omega hice 3)
  fin_cases y <;>
    simp [SixVertexArrows.cyclicPred, svFinLast,
      sixVertexFourByFourTorus] at h0 h1 h2 h3 ⊢ <;>
    omega

def sixVertexFourByFourAuditedParamSourceFirst
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam : Fin 4) :
    SixVertexArrows sixVertexFourByFourTorus :=
  { horizontal := fun v =>
      sixVertexFourByFourAuditedParamHorizontalRowsFirst p v.2 v.1
    vertical := fun v =>
      sixVertexFourByFourAuditedParamVerticalRowsFirst p seam v.2 v.1 }

def sixVertexFourByFourAuditedParamSourceSecond
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam : Fin 4) :
    SixVertexArrows sixVertexFourByFourTorus :=
  { horizontal := fun v =>
      sixVertexFourByFourAuditedParamHorizontalRowsSecond p v.2 v.1
    vertical := fun v =>
      sixVertexFourByFourAuditedParamVerticalRowsSecond p seam v.2 v.1 }

theorem sixVertexFourByFourAuditedParamSourceFirst_eq_completedMasks
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam : Fin 4) :
    sixVertexFourByFourAuditedParamSourceFirst p seam =
      sixVertexFourByFourArrowsOfMasks
        (sixVertexFourByFourAuditedHorizontalMasks p).1
        (sixVertexFourByFourCompletedVerticalMask
          (sixVertexFourByFourAuditedHorizontalMasks p).1
          (sixVertexFourByFourSectorOneSeamMask seam)) := by
  apply SixVertexArrows.ext
  · funext v
    rcases v with ⟨x, y⟩
    fin_cases y <;>
      simp [sixVertexFourByFourAuditedParamSourceFirst,
        sixVertexFourByFourArrowsOfMasks,
        sixVertexFourByFourAuditedHorizontalMasks,
        sixVertexFourByFourAuditedParamHorizontalRowsFirst] <;> rfl
  · funext v
    rcases v with ⟨x, y⟩
    symm
    calc
      _ = sixVertexFourByFourCompletedVerticalRow
            (sixVertexFourByFourAuditedHorizontalMasks p).1
            (sixVertexFourByFourSectorOneSeamMask seam) y x :=
        sixVertexFourByFourCompletedVerticalMask_row _ _ x y
      _ = _ := sixVertexFourByFourCompletedVerticalColumn_auditedFirst
        p seam x y

theorem sixVertexFourByFourAuditedParamSourceSecond_eq_completedMasks
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam : Fin 4) :
    sixVertexFourByFourAuditedParamSourceSecond p seam =
      sixVertexFourByFourArrowsOfMasks
        (sixVertexFourByFourAuditedHorizontalMasks p).2
        (sixVertexFourByFourCompletedVerticalMask
          (sixVertexFourByFourAuditedHorizontalMasks p).2
          (sixVertexFourByFourSectorThreeSeamMask seam)) := by
  apply SixVertexArrows.ext
  · funext v
    rcases v with ⟨x, y⟩
    fin_cases y <;>
      simp [sixVertexFourByFourAuditedParamSourceSecond,
        sixVertexFourByFourArrowsOfMasks,
        sixVertexFourByFourAuditedHorizontalMasks,
        sixVertexFourByFourAuditedParamHorizontalRowsSecond] <;> rfl
  · funext v
    rcases v with ⟨x, y⟩
    symm
    calc
      _ = sixVertexFourByFourCompletedVerticalRow
            (sixVertexFourByFourAuditedHorizontalMasks p).2
            (sixVertexFourByFourSectorThreeSeamMask seam) y x :=
        sixVertexFourByFourCompletedVerticalMask_row _ _ x y
      _ = _ := sixVertexFourByFourCompletedVerticalColumn_auditedSecond
        p seam x y

theorem sixVertexFourByFourAuditedParamSourceFirst_verticalRowCount
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam y : Fin 4)
    (hice : (sixVertexFourByFourAuditedParamSourceFirst p seam).IceRule)
    (hsector : sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByFourTorus
        (sixVertexFourByFourAuditedParamSourceFirst p seam)
        (svFinLast sixVertexFourByFourTorus.height_pos)) = 1) :
    sixVertexUpCount
      (sixVertexFourByFourAuditedParamVerticalRowsFirst p seam y) = 1 := by
  have hcount := sixVertexFourByFour_verticalRowCount_eq_last
    (sixVertexFourByFourAuditedParamSourceFirst p seam) hice y
  exact (by
    simpa [svTorusVerticalRows,
      sixVertexFourByFourAuditedParamSourceFirst] using hcount.trans hsector)

theorem sixVertexFourByFourAuditedParamSourceSecond_verticalRowCount
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam y : Fin 4)
    (hice : (sixVertexFourByFourAuditedParamSourceSecond p seam).IceRule)
    (hsector : sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByFourTorus
        (sixVertexFourByFourAuditedParamSourceSecond p seam)
        (svFinLast sixVertexFourByFourTorus.height_pos)) = 3) :
    sixVertexUpCount
      (sixVertexFourByFourAuditedParamVerticalRowsSecond p seam y) = 3 := by
  have hcount := sixVertexFourByFour_verticalRowCount_eq_last
    (sixVertexFourByFourAuditedParamSourceSecond p seam) hice y
  exact (by
    simpa [svTorusVerticalRows,
      sixVertexFourByFourAuditedParamSourceSecond] using hcount.trans hsector)

theorem sixVertexFourByFourAuditedParamSourceFirst_evenStep
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam y : Fin 4)
    (hice : (sixVertexFourByFourAuditedParamSourceFirst p seam).IceRule) :
    sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourAuditedParamVerticalRowsFirst p seam
          (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y)) =
      sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourAuditedParamVerticalRowsFirst p seam y) := by
  obtain ⟨i, hi⟩ :=
    sixVertexFourByFourAuditedParamHorizontalRowsFirst_allowed p y
  have hrow := sixVertexFourByFour_rowIce
    (sixVertexFourByFourAuditedParamSourceFirst p seam) hice y
  change svHorizontalIce sixVertexFourByFourTorus.width_pos
      (sixVertexFourByFourAuditedParamVerticalRowsFirst p seam
        (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y))
      (sixVertexFourByFourAuditedParamVerticalRowsFirst p seam y)
      (sixVertexFourByFourAuditedParamHorizontalRowsFirst p y) at hrow
  rw [hi] at hrow
  exact sixVertexFourByFourEvenUpCount_preserved i _ _ hrow

theorem sixVertexFourByFourAuditedParamSourceSecond_evenStep
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam y : Fin 4)
    (hice : (sixVertexFourByFourAuditedParamSourceSecond p seam).IceRule) :
    sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourAuditedParamVerticalRowsSecond p seam
          (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y)) =
      sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourAuditedParamVerticalRowsSecond p seam y) := by
  obtain ⟨i, hi⟩ :=
    sixVertexFourByFourAuditedParamHorizontalRowsSecond_allowed p y
  have hrow := sixVertexFourByFour_rowIce
    (sixVertexFourByFourAuditedParamSourceSecond p seam) hice y
  change svHorizontalIce sixVertexFourByFourTorus.width_pos
      (sixVertexFourByFourAuditedParamVerticalRowsSecond p seam
        (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y))
      (sixVertexFourByFourAuditedParamVerticalRowsSecond p seam y)
      (sixVertexFourByFourAuditedParamHorizontalRowsSecond p y) at hrow
  rw [hi] at hrow
  exact sixVertexFourByFourEvenUpCount_preserved i _ _ hrow

theorem sixVertexFourByFourAuditedParamSourceFirst_even
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam y : Fin 4)
    (hice : (sixVertexFourByFourAuditedParamSourceFirst p seam).IceRule)
    (hsector : sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByFourTorus
        (sixVertexFourByFourAuditedParamSourceFirst p seam)
        (svFinLast sixVertexFourByFourTorus.height_pos)) = 1) :
    sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourAuditedParamVerticalRowsFirst p seam y) =
      sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourSectorOneSeamMask seam)) := by
  have hcountZero :=
    sixVertexFourByFourAuditedParamSourceFirst_verticalRowCount
      p seam 0 hice hsector
  have hcountZero' : sixVertexUpCount
      (sixVertexFourByFourNextVerticalRow
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourAuditedRowZero p.1).1)
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourSectorOneSeamMask seam))) = 1 := by
    simpa [sixVertexFourByFourAuditedParamVerticalRowsFirst,
      sixVertexFourByFourAuditedParamHorizontalRowsFirst] using hcountZero
  have hzero :
      sixVertexFourByFourEvenUpCount
          (sixVertexFourByFourAuditedParamVerticalRowsFirst p seam 0) =
        sixVertexFourByFourEvenUpCount
          (sixVertexFourByFourRowOfMask
            (sixVertexFourByFourSectorOneSeamMask seam)) := by
    simpa [sixVertexFourByFourAuditedParamVerticalRowsFirst,
      sixVertexFourByFourAuditedParamHorizontalRowsFirst] using
      sixVertexFourByFourFirstRowZero_even p.1 seam hcountZero'
  have h01 := sixVertexFourByFourAuditedParamSourceFirst_evenStep
    p seam 1 hice
  have h12 := sixVertexFourByFourAuditedParamSourceFirst_evenStep
    p seam 2 hice
  have h23 := sixVertexFourByFourAuditedParamSourceFirst_evenStep
    p seam 3 hice
  simp [SixVertexArrows.cyclicPred] at h01 h12 h23
  fin_cases y
  · exact hzero
  · exact h01.symm.trans hzero
  · exact h12.symm.trans (h01.symm.trans hzero)
  · exact h23.symm.trans (h12.symm.trans (h01.symm.trans hzero))

def sixVertexFourByFourAuditedRepairColumns
    (firstSeam secondSeam : Fin 4) : Fin 4 × Fin 4 :=
  (![1, 0, 1, 0] firstSeam,
    if firstSeam.val % 2 = 0 then ![2, 1, 2, 1] secondSeam
    else ![0, 3, 0, 3] secondSeam)

theorem sixVertexFourByFourAuditedParamSourceSecond_even
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam y : Fin 4)
    (hice : (sixVertexFourByFourAuditedParamSourceSecond p seam).IceRule)
    (hsector : sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByFourTorus
        (sixVertexFourByFourAuditedParamSourceSecond p seam)
        (svFinLast sixVertexFourByFourTorus.height_pos)) = 3) :
    sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourAuditedParamVerticalRowsSecond p seam y) =
      sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourSectorThreeSeamMask seam)) := by
  have hcountZero :=
    sixVertexFourByFourAuditedParamSourceSecond_verticalRowCount
      p seam 0 hice hsector
  have hcountZero' : sixVertexUpCount
      (sixVertexFourByFourNextVerticalRow
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourAuditedRowZero p.1).2)
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourSectorThreeSeamMask seam))) = 3 := by
    simpa [sixVertexFourByFourAuditedParamVerticalRowsSecond,
      sixVertexFourByFourAuditedParamHorizontalRowsSecond] using hcountZero
  have hzero :
      sixVertexFourByFourEvenUpCount
          (sixVertexFourByFourAuditedParamVerticalRowsSecond p seam 0) =
        sixVertexFourByFourEvenUpCount
          (sixVertexFourByFourRowOfMask
            (sixVertexFourByFourSectorThreeSeamMask seam)) := by
    simpa [sixVertexFourByFourAuditedParamVerticalRowsSecond,
      sixVertexFourByFourAuditedParamHorizontalRowsSecond] using
      sixVertexFourByFourSecondRowZero_even p.1 seam hcountZero'
  have h01 := sixVertexFourByFourAuditedParamSourceSecond_evenStep
    p seam 1 hice
  have h12 := sixVertexFourByFourAuditedParamSourceSecond_evenStep
    p seam 2 hice
  have h23 := sixVertexFourByFourAuditedParamSourceSecond_evenStep
    p seam 3 hice
  simp [SixVertexArrows.cyclicPred] at h01 h12 h23
  fin_cases y
  · exact hzero
  · exact h01.symm.trans hzero
  · exact h12.symm.trans (h01.symm.trans hzero)
  · exact h23.symm.trans (h12.symm.trans (h01.symm.trans hzero))

theorem sixVertexFourByFourSelectedFirst_false
    (row : SixVertexRow 4) (seam : Fin 4)
    (hcount : sixVertexUpCount row = 1)
    (heven : sixVertexFourByFourEvenUpCount row =
      sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourSectorOneSeamMask seam))) :
    row (![1, 0, 1, 0] seam) = false := by
  fin_cases seam <;> revert row <;> decide

theorem sixVertexFourByFourSelectedSecond_true
    (row : SixVertexRow 4) (firstSeam secondSeam : Fin 4)
    (hcount : sixVertexUpCount row = 3)
    (heven : sixVertexFourByFourEvenUpCount row =
      sixVertexFourByFourEvenUpCount
        (sixVertexFourByFourRowOfMask
          (sixVertexFourByFourSectorThreeSeamMask secondSeam))) :
    row (sixVertexFourByFourAuditedRepairColumns firstSeam secondSeam).2 =
      true := by
  fin_cases firstSeam <;> fin_cases secondSeam <;> revert row <;> decide

def sixVertexFourByFourColumnMask : Fin 4 -> Nat := ![
  0x1111, 0x2222, 0x4444, 0x8888
]

def sixVertexFourByFourToggleVerticalColumn
    (column : Fin 4) (omega : SixVertexArrows sixVertexFourByFourTorus) :
    SixVertexArrows sixVertexFourByFourTorus where
  horizontal := omega.horizontal
  vertical v := if v.1 = column then !omega.vertical v else omega.vertical v

theorem sixVertexFourByFourToggleVerticalColumn_iceRule
    (omega : SixVertexArrows sixVertexFourByFourTorus)
    (column : Fin 4) (value : Bool)
    (hcolumn : forall y, omega.vertical (column, y) = value)
    (hice : omega.IceRule) :
    (sixVertexFourByFourToggleVerticalColumn column omega).IceRule := by
  intro v
  rcases v with ⟨x, y⟩
  by_cases hx : x = column
  · subst x
    simpa [sixVertexFourByFourToggleVerticalColumn,
      SixVertexArrows.incomingCount, hcolumn,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using hice (column, y)
  · simpa [sixVertexFourByFourToggleVerticalColumn,
      SixVertexArrows.incomingCount, hx]
      using hice (x, y)

theorem sixVertexFourByFourToggleVerticalColumn_upCount_false
    (omega : SixVertexArrows sixVertexFourByFourTorus)
    (column y : Fin 4)
    (hcolumn : omega.vertical (column, y) = false) :
    sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus
          (sixVertexFourByFourToggleVerticalColumn column omega) y) =
      sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus omega y) + 1 := by
  rw [← sum_bool_toNat_eq_sixVertexUpCount,
    ← sum_bool_toNat_eq_sixVertexUpCount]
  change (∑ x : Fin 4,
      ((sixVertexFourByFourToggleVerticalColumn column omega).vertical
        (x, y)).toNat) =
    (∑ x : Fin 4, (omega.vertical (x, y)).toNat) + 1
  rw [Fin.sum_univ_four, Fin.sum_univ_four]
  fin_cases column <;>
    simp at hcolumn <;>
    simp [sixVertexFourByFourToggleVerticalColumn, hcolumn] <;>
    omega

theorem sixVertexFourByFourToggleVerticalColumn_upCount_true
    (omega : SixVertexArrows sixVertexFourByFourTorus)
    (column y : Fin 4)
    (hcolumn : omega.vertical (column, y) = true) :
    sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByFourTorus omega y) =
      sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus
          (sixVertexFourByFourToggleVerticalColumn column omega) y) + 1 := by
  rw [← sum_bool_toNat_eq_sixVertexUpCount,
    ← sum_bool_toNat_eq_sixVertexUpCount]
  change (∑ x : Fin 4, (omega.vertical (x, y)).toNat) =
    (∑ x : Fin 4,
      ((sixVertexFourByFourToggleVerticalColumn column omega).vertical
        (x, y)).toNat) + 1
  rw [Fin.sum_univ_four, Fin.sum_univ_four]
  fin_cases column <;>
    simp at hcolumn <;>
    simp [sixVertexFourByFourToggleVerticalColumn, hcolumn] <;>
    omega

theorem sixVertexFourByFourTogglePair_fineRelated
    (first second : SixVertexArrows sixVertexFourByFourTorus)
    (firstColumn secondColumn : Fin 4)
    (hfirst : forall y, first.vertical (firstColumn, y) = false)
    (hsecond : forall y, second.vertical (secondColumn, y) = true) :
    sixVertexPairAtMostTwoCycleFineRelated
      (first, second)
      (sixVertexFourByFourToggleVerticalColumn firstColumn first,
        sixVertexFourByFourToggleVerticalColumn secondColumn second) := by
  constructor
  · by_cases hcolumns : firstColumn = secondColumn
    · subst secondColumn
      apply sixVertexPairAtMostTwoCycleRelated_of_union_eq
      · funext v
        rfl
      · funext v
        rcases v with ⟨x, y⟩
        by_cases hx : x = firstColumn
        · subst x
          simp [sixVertexPairUnionVertical,
            sixVertexFourByFourToggleVerticalColumn,
            hfirst, hsecond]
        ·
          simp [sixVertexPairUnionVertical,
            sixVertexFourByFourToggleVerticalColumn, hx]
    · let family := sixVertexFourByFourOppositeVerticalColumnFamily
          firstColumn secondColumn hcolumns
      refine ⟨family, true, ?_, ?_⟩
      · funext v
        rw [show family.horizontalFlow v = 0 by
          exact sixVertexFourByFourOppositeVerticalColumnFamily_horizontalFlow
            firstColumn secondColumn hcolumns v]
        simp [sixVertexPairUnionHorizontalDelta,
          sixVertexPairUnionHorizontal,
          sixVertexFourByFourToggleVerticalColumn]
      · funext v
        rcases v with ⟨x, y⟩
        rw [show family.verticalFlow (x, y) =
            (if x = firstColumn then 1
              else if x = secondColumn then -1 else 0) by
          exact sixVertexFourByFourOppositeVerticalColumnFamily_verticalFlow
            firstColumn secondColumn hcolumns x y]
        have hcolumnsSymm : secondColumn ≠ firstColumn := Ne.symm hcolumns
        by_cases hxFirst : x = firstColumn
        · subst x
          simp only [sixVertexPairUnionVerticalDelta,
            sixVertexPairUnionVertical,
            sixVertexFourByFourToggleVerticalColumn]
          simp only [ite_true]
          split <;> simp_all
        · by_cases hxSecond : x = secondColumn
          · subst x
            simp only [sixVertexPairUnionVerticalDelta,
              sixVertexPairUnionVertical,
              sixVertexFourByFourToggleVerticalColumn]
            simp only [ite_true]
            split <;> simp_all
          · simp only [sixVertexPairUnionVerticalDelta,
              sixVertexPairUnionVertical,
              sixVertexFourByFourToggleVerticalColumn]
            simp [hxFirst, hxSecond]
  · rfl

def sixVertexFourByFourAuditedParamTargetFirst
    (p : SixVertexFourByFourAuditedHorizontalParameters)
    (firstSeam : Fin 4) (column : Fin 4) :
    SixVertexArrows sixVertexFourByFourTorus :=
  sixVertexFourByFourToggleVerticalColumn
    column
    (sixVertexFourByFourAuditedParamSourceFirst p firstSeam)

def sixVertexFourByFourAuditedParamTargetSecond
    (p : SixVertexFourByFourAuditedHorizontalParameters)
    (secondSeam : Fin 4) (column : Fin 4) :
    SixVertexArrows sixVertexFourByFourTorus :=
  sixVertexFourByFourToggleVerticalColumn
    column
    (sixVertexFourByFourAuditedParamSourceSecond p secondSeam)

def SixVertexFourByFourValidColumnRepair
    (p : SixVertexFourByFourAuditedHorizontalParameters)
    (firstSeam secondSeam : Fin 4) (columns : Fin 4 × Fin 4) : Prop :=
  (sixVertexFourByFourAuditedParamTargetFirst
      p firstSeam columns.1).IceRule /\
    (sixVertexFourByFourAuditedParamTargetSecond
      p secondSeam columns.2).IceRule /\
    sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus
          (sixVertexFourByFourAuditedParamTargetFirst
            p firstSeam columns.1)
          (svFinLast sixVertexFourByFourTorus.height_pos)) = 2 /\
    sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus
          (sixVertexFourByFourAuditedParamTargetSecond
            p secondSeam columns.2)
          (svFinLast sixVertexFourByFourTorus.height_pos)) = 2

def SixVertexFourByFourAuditedParamMatchingStatement
    (p : SixVertexFourByFourAuditedHorizontalParameters)
    (firstSeam secondSeam : Fin 4) : Prop :=
  (sixVertexFourByFourAuditedParamSourceFirst p firstSeam).IceRule ->
  (sixVertexFourByFourAuditedParamSourceSecond p secondSeam).IceRule ->
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByFourTorus
            (sixVertexFourByFourAuditedParamSourceFirst p firstSeam)
            (svFinLast sixVertexFourByFourTorus.height_pos)) = 1 ->
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByFourTorus
            (sixVertexFourByFourAuditedParamSourceSecond p secondSeam)
            (svFinLast sixVertexFourByFourTorus.height_pos)) = 3 ->
    SixVertexFourByFourValidColumnRepair p firstSeam secondSeam
      (sixVertexFourByFourAuditedRepairColumns firstSeam secondSeam)

def SixVertexFourByFourAuditedSelectedColumnsConstantStatement
    (p : SixVertexFourByFourAuditedHorizontalParameters)
    (firstSeam secondSeam : Fin 4) : Prop :=
  (sixVertexFourByFourAuditedParamSourceFirst p firstSeam).IceRule ->
  (sixVertexFourByFourAuditedParamSourceSecond p secondSeam).IceRule ->
  sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByFourTorus
        (sixVertexFourByFourAuditedParamSourceFirst p firstSeam)
        (svFinLast sixVertexFourByFourTorus.height_pos)) = 1 ->
  sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByFourTorus
        (sixVertexFourByFourAuditedParamSourceSecond p secondSeam)
        (svFinLast sixVertexFourByFourTorus.height_pos)) = 3 ->
  (forall y,
      (sixVertexFourByFourAuditedParamSourceFirst p firstSeam).vertical
        ((sixVertexFourByFourAuditedRepairColumns firstSeam secondSeam).1, y) =
          false) /\
    (forall y,
      (sixVertexFourByFourAuditedParamSourceSecond p secondSeam).vertical
        ((sixVertexFourByFourAuditedRepairColumns firstSeam secondSeam).2, y) =
          true)

theorem sixVertexFourByFourAudited_selectedColumns_constant
    (p : SixVertexFourByFourAuditedHorizontalParameters)
    (firstSeam secondSeam : Fin 4) :
    SixVertexFourByFourAuditedSelectedColumnsConstantStatement
      p firstSeam secondSeam := by
  unfold SixVertexFourByFourAuditedSelectedColumnsConstantStatement
  intro hfirst hsecond hfirstSector hsecondSector
  constructor
  · intro y
    change sixVertexFourByFourAuditedParamVerticalRowsFirst p firstSeam y
        (sixVertexFourByFourAuditedRepairColumns firstSeam secondSeam).1 = false
    have hcount := sixVertexFourByFourAuditedParamSourceFirst_verticalRowCount
      p firstSeam y hfirst hfirstSector
    have heven := sixVertexFourByFourAuditedParamSourceFirst_even
      p firstSeam y hfirst hfirstSector
    simpa [sixVertexFourByFourAuditedRepairColumns] using
      sixVertexFourByFourSelectedFirst_false
        (sixVertexFourByFourAuditedParamVerticalRowsFirst p firstSeam y)
        firstSeam hcount heven
  · intro y
    change sixVertexFourByFourAuditedParamVerticalRowsSecond p secondSeam y
        (sixVertexFourByFourAuditedRepairColumns firstSeam secondSeam).2 = true
    have hcount := sixVertexFourByFourAuditedParamSourceSecond_verticalRowCount
      p secondSeam y hsecond hsecondSector
    have heven := sixVertexFourByFourAuditedParamSourceSecond_even
      p secondSeam y hsecond hsecondSector
    exact sixVertexFourByFourSelectedSecond_true
      (sixVertexFourByFourAuditedParamVerticalRowsSecond p secondSeam y)
      firstSeam secondSeam hcount heven

theorem sixVertexFourByFourAuditedParamMatching_valid
    (p : SixVertexFourByFourAuditedHorizontalParameters)
    (firstSeam secondSeam : Fin 4) :
    SixVertexFourByFourAuditedParamMatchingStatement p firstSeam secondSeam := by
  intro hfirst hsecond hfirstSector hsecondSector
  have hcolumns := sixVertexFourByFourAudited_selectedColumns_constant
    p firstSeam secondSeam hfirst hsecond hfirstSector hsecondSector
  unfold SixVertexFourByFourValidColumnRepair
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sixVertexFourByFourToggleVerticalColumn_iceRule _ _ false
      hcolumns.1 hfirst
  · exact sixVertexFourByFourToggleVerticalColumn_iceRule _ _ true
      hcolumns.2 hsecond
  · have hup := sixVertexFourByFourToggleVerticalColumn_upCount_false
      (sixVertexFourByFourAuditedParamSourceFirst p firstSeam)
      (sixVertexFourByFourAuditedRepairColumns firstSeam secondSeam).1
      (svFinLast sixVertexFourByFourTorus.height_pos)
      (hcolumns.1 (svFinLast sixVertexFourByFourTorus.height_pos))
    change sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus
          (sixVertexFourByFourToggleVerticalColumn
            (sixVertexFourByFourAuditedRepairColumns
              firstSeam secondSeam).1
            (sixVertexFourByFourAuditedParamSourceFirst p firstSeam))
          (svFinLast sixVertexFourByFourTorus.height_pos)) = 2
    calc
      _ = sixVertexUpCount
            (svTorusVerticalRows sixVertexFourByFourTorus
              (sixVertexFourByFourAuditedParamSourceFirst p firstSeam)
              (svFinLast sixVertexFourByFourTorus.height_pos)) + 1 := hup
      _ = 2 := by rw [hfirstSector]
  · have hup := sixVertexFourByFourToggleVerticalColumn_upCount_true
      (sixVertexFourByFourAuditedParamSourceSecond p secondSeam)
      (sixVertexFourByFourAuditedRepairColumns firstSeam secondSeam).2
      (svFinLast sixVertexFourByFourTorus.height_pos)
      (hcolumns.2 (svFinLast sixVertexFourByFourTorus.height_pos))
    change sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus
          (sixVertexFourByFourToggleVerticalColumn
            (sixVertexFourByFourAuditedRepairColumns
              firstSeam secondSeam).2
            (sixVertexFourByFourAuditedParamSourceSecond p secondSeam))
          (svFinLast sixVertexFourByFourTorus.height_pos)) = 2
    have htargetPlus : sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus
          (sixVertexFourByFourToggleVerticalColumn
            (sixVertexFourByFourAuditedRepairColumns
              firstSeam secondSeam).2
            (sixVertexFourByFourAuditedParamSourceSecond p secondSeam))
          (svFinLast sixVertexFourByFourTorus.height_pos)) + 1 = 3 :=
      hup.symm.trans hsecondSector
    omega

structure SixVertexFourByFourAuditedCoordinates where
  firstSeam : Fin 4
  secondSeam : Fin 4
  middle : Fin 8
  last : Fin 4
deriving DecidableEq, Fintype

def sixVertexFourByFourAuditedCoordinateRowZero
    (firstSeam secondSeam : Fin 4) : Fin 16 :=
  ![![1, 0, 2, 3], ![5, 4, 6, 7],
    ![13, 12, 14, 15], ![9, 8, 10, 11]] firstSeam secondSeam

def sixVertexFourByFourAuditedMiddleA (secondSeam : Fin 4) : Fin 16 :=
  ![2, 3, 1, 0] secondSeam

def sixVertexFourByFourAuditedMiddleB (firstSeam : Fin 4) : Fin 16 :=
  ![10, 8, 4, 6] firstSeam

def sixVertexFourByFourAuditedMiddleBNext (firstSeam : Fin 4) : Fin 16 :=
  ![11, 9, 5, 7] firstSeam

def sixVertexFourByFourAuditedMiddleC (secondSeam : Fin 4) : Fin 16 :=
  ![14, 15, 13, 12] secondSeam

def sixVertexFourByFourAuditedMiddlePair
    (firstSeam secondSeam : Fin 4) : Fin 8 -> Fin 16 × Fin 16 := ![
  (sixVertexFourByFourAuditedMiddleA secondSeam,
    sixVertexFourByFourAuditedMiddleB firstSeam),
  (sixVertexFourByFourAuditedMiddleA secondSeam,
    sixVertexFourByFourAuditedMiddleBNext firstSeam),
  (sixVertexFourByFourAuditedMiddleB firstSeam,
    sixVertexFourByFourAuditedMiddleA secondSeam),
  (sixVertexFourByFourAuditedMiddleB firstSeam,
    sixVertexFourByFourAuditedMiddleC secondSeam),
  (sixVertexFourByFourAuditedMiddleBNext firstSeam,
    sixVertexFourByFourAuditedMiddleA secondSeam),
  (sixVertexFourByFourAuditedMiddleBNext firstSeam,
    sixVertexFourByFourAuditedMiddleC secondSeam),
  (sixVertexFourByFourAuditedMiddleC secondSeam,
    sixVertexFourByFourAuditedMiddleB firstSeam),
  (sixVertexFourByFourAuditedMiddleC secondSeam,
    sixVertexFourByFourAuditedMiddleBNext firstSeam)
]

def sixVertexFourByFourAuditedCoordinateParameters
    (c : SixVertexFourByFourAuditedCoordinates) :
    SixVertexFourByFourAuditedHorizontalParameters :=
  let middle := sixVertexFourByFourAuditedMiddlePair
    c.firstSeam c.secondSeam c.middle
  (sixVertexFourByFourAuditedCoordinateRowZero c.firstSeam c.secondSeam,
    middle.1, middle.2, c.last)

def sixVertexFourByFourAuditedCoordinateSourcePair
    (c : SixVertexFourByFourAuditedCoordinates) :
    SixVertexArrows sixVertexFourByFourTorus ×
      SixVertexArrows sixVertexFourByFourTorus :=
  (sixVertexFourByFourAuditedParamSourceFirst
      (sixVertexFourByFourAuditedCoordinateParameters c) c.firstSeam,
    sixVertexFourByFourAuditedParamSourceSecond
      (sixVertexFourByFourAuditedCoordinateParameters c) c.secondSeam)

def SixVertexFourByFourAuditedCoordinateSourcePairValid
    (c : SixVertexFourByFourAuditedCoordinates) : Prop :=
    (sixVertexFourByFourAuditedCoordinateSourcePair c).1.IceRule /\
      (sixVertexFourByFourAuditedCoordinateSourcePair c).2.IceRule /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByFourTorus
            (sixVertexFourByFourAuditedCoordinateSourcePair c).1
            (svFinLast sixVertexFourByFourTorus.height_pos)) = 1 /\
      sixVertexUpCount
          (svTorusVerticalRows sixVertexFourByFourTorus
            (sixVertexFourByFourAuditedCoordinateSourcePair c).2
            (svFinLast sixVertexFourByFourTorus.height_pos)) = 3

def SixVertexFourByFourAuditedCoordinateRowsInvariant
    (c : SixVertexFourByFourAuditedCoordinates) : Prop :=
  let p := sixVertexFourByFourAuditedCoordinateParameters c
  (forall y, sixVertexUpCount
      (sixVertexFourByFourAuditedParamVerticalRowsFirst p c.firstSeam y) = 1) /\
    (forall y, sixVertexUpCount
      (sixVertexFourByFourAuditedParamVerticalRowsSecond p c.secondSeam y) = 3) /\
    sixVertexFourByFourAuditedParamVerticalRowsFirst p c.firstSeam 3 =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourSectorOneSeamMask c.firstSeam) /\
    sixVertexFourByFourAuditedParamVerticalRowsSecond p c.secondSeam 3 =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourSectorThreeSeamMask c.secondSeam)

set_option maxHeartbeats 4000000 in

set_option maxRecDepth 100000 in
theorem sixVertexFourByFourAuditedCoordinateRows_invariant
    (c : SixVertexFourByFourAuditedCoordinates) :
    SixVertexFourByFourAuditedCoordinateRowsInvariant c := by
  unfold SixVertexFourByFourAuditedCoordinateRowsInvariant
  rcases c with ⟨firstSeam, secondSeam, middle, last⟩
  fin_cases firstSeam <;> fin_cases secondSeam <;>
    fin_cases middle <;> fin_cases last <;> decide

theorem sixVertexFourByFour_iceRule_of_rowIce
    (omega : SixVertexArrows sixVertexFourByFourTorus)
    (hrow : forall y, svHorizontalIce sixVertexFourByFourTorus.width_pos
      (svTorusVerticalRows sixVertexFourByFourTorus omega
        (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y))
      (svTorusVerticalRows sixVertexFourByFourTorus omega y)
      (svTorusHorizontalRows sixVertexFourByFourTorus omega y)) :
    omega.IceRule := by
  intro v
  rcases v with ⟨x, y⟩
  simpa [svHorizontalIce, svHorizontalIncomingCount,
    svTorusVerticalRows, svTorusHorizontalRows,
    SixVertexArrows.incomingCount, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm] using hrow y x

theorem sixVertexFourByFourAuditedCoordinateFirst_rowIce
    (c : SixVertexFourByFourAuditedCoordinates) (y : Fin 4) :
    let p := sixVertexFourByFourAuditedCoordinateParameters c
    svHorizontalIce sixVertexFourByFourTorus.width_pos
      (sixVertexFourByFourAuditedParamVerticalRowsFirst p c.firstSeam
        (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y))
      (sixVertexFourByFourAuditedParamVerticalRowsFirst p c.firstSeam y)
      (sixVertexFourByFourAuditedParamHorizontalRowsFirst p y) := by
  dsimp only
  let p := sixVertexFourByFourAuditedCoordinateParameters c
  have hinvariant := sixVertexFourByFourAuditedCoordinateRows_invariant c
  change SixVertexFourByFourAuditedCoordinateRowsInvariant c at hinvariant
  dsimp only [SixVertexFourByFourAuditedCoordinateRowsInvariant] at hinvariant
  rcases hinvariant with ⟨hfirst, _, hclose, _⟩
  change (forall y, sixVertexUpCount
      (sixVertexFourByFourAuditedParamVerticalRowsFirst p c.firstSeam y) = 1)
    at hfirst
  change sixVertexFourByFourAuditedParamVerticalRowsFirst p c.firstSeam 3 =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourSectorOneSeamMask c.firstSeam) at hclose
  obtain ⟨i, hi⟩ :=
    sixVertexFourByFourAuditedParamHorizontalRowsFirst_allowed p y
  have hnext :
      sixVertexFourByFourAuditedParamVerticalRowsFirst p c.firstSeam y =
        sixVertexFourByFourNextVerticalRow
          (sixVertexFourByFourAuditedParamHorizontalRowsFirst p y)
          (sixVertexFourByFourAuditedParamVerticalRowsFirst p c.firstSeam
            (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y)) := by
    fin_cases y
    · change sixVertexFourByFourAuditedParamVerticalRowsFirst
          p c.firstSeam 0 =
        sixVertexFourByFourNextVerticalRow
          (sixVertexFourByFourAuditedParamHorizontalRowsFirst p 0)
          (sixVertexFourByFourAuditedParamVerticalRowsFirst p c.firstSeam 3)
      rw [hclose]
      rfl
    · rfl
    · rfl
    · rfl
  rw [hi] at hnext ⊢
  rw [hnext]
  apply sixVertexFourByFourNextVerticalRow_ice_of_upCount_eq i
  rw [← hnext, hfirst y, hfirst
      (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y)]

theorem sixVertexFourByFourAuditedCoordinateSecond_rowIce
    (c : SixVertexFourByFourAuditedCoordinates) (y : Fin 4) :
    let p := sixVertexFourByFourAuditedCoordinateParameters c
    svHorizontalIce sixVertexFourByFourTorus.width_pos
      (sixVertexFourByFourAuditedParamVerticalRowsSecond p c.secondSeam
        (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y))
      (sixVertexFourByFourAuditedParamVerticalRowsSecond p c.secondSeam y)
      (sixVertexFourByFourAuditedParamHorizontalRowsSecond p y) := by
  dsimp only
  let p := sixVertexFourByFourAuditedCoordinateParameters c
  have hinvariant := sixVertexFourByFourAuditedCoordinateRows_invariant c
  change SixVertexFourByFourAuditedCoordinateRowsInvariant c at hinvariant
  dsimp only [SixVertexFourByFourAuditedCoordinateRowsInvariant] at hinvariant
  rcases hinvariant with ⟨_, hsecond, _, hclose⟩
  change (forall y, sixVertexUpCount
      (sixVertexFourByFourAuditedParamVerticalRowsSecond p c.secondSeam y) = 3)
    at hsecond
  change sixVertexFourByFourAuditedParamVerticalRowsSecond p c.secondSeam 3 =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourSectorThreeSeamMask c.secondSeam) at hclose
  obtain ⟨i, hi⟩ :=
    sixVertexFourByFourAuditedParamHorizontalRowsSecond_allowed p y
  have hnext :
      sixVertexFourByFourAuditedParamVerticalRowsSecond p c.secondSeam y =
        sixVertexFourByFourNextVerticalRow
          (sixVertexFourByFourAuditedParamHorizontalRowsSecond p y)
          (sixVertexFourByFourAuditedParamVerticalRowsSecond p c.secondSeam
            (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y)) := by
    fin_cases y
    · change sixVertexFourByFourAuditedParamVerticalRowsSecond
          p c.secondSeam 0 =
        sixVertexFourByFourNextVerticalRow
          (sixVertexFourByFourAuditedParamHorizontalRowsSecond p 0)
          (sixVertexFourByFourAuditedParamVerticalRowsSecond p c.secondSeam 3)
      rw [hclose]
      rfl
    · rfl
    · rfl
    · rfl
  rw [hi] at hnext ⊢
  rw [hnext]
  apply sixVertexFourByFourNextVerticalRow_ice_of_upCount_eq i
  rw [← hnext, hsecond y, hsecond
      (SixVertexArrows.cyclicPred sixVertexFourByFourTorus.height_pos y)]

theorem sixVertexFourByFourAuditedCoordinateSourcePair_valid
    (c : SixVertexFourByFourAuditedCoordinates) :
    SixVertexFourByFourAuditedCoordinateSourcePairValid c := by
  let p := sixVertexFourByFourAuditedCoordinateParameters c
  have hinvariant := sixVertexFourByFourAuditedCoordinateRows_invariant c
  change SixVertexFourByFourAuditedCoordinateRowsInvariant c at hinvariant
  dsimp only [SixVertexFourByFourAuditedCoordinateRowsInvariant] at hinvariant
  rcases hinvariant with ⟨hfirstCount, hsecondCount, _, _⟩
  unfold SixVertexFourByFourAuditedCoordinateSourcePairValid
  change (sixVertexFourByFourAuditedParamSourceFirst p c.firstSeam).IceRule /\
    (sixVertexFourByFourAuditedParamSourceSecond p c.secondSeam).IceRule /\ _ /\ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply sixVertexFourByFour_iceRule_of_rowIce
    intro y
    simpa [svTorusVerticalRows, svTorusHorizontalRows,
      sixVertexFourByFourAuditedParamSourceFirst] using
      sixVertexFourByFourAuditedCoordinateFirst_rowIce c y
  · apply sixVertexFourByFour_iceRule_of_rowIce
    intro y
    simpa [svTorusVerticalRows, svTorusHorizontalRows,
      sixVertexFourByFourAuditedParamSourceSecond] using
      sixVertexFourByFourAuditedCoordinateSecond_rowIce c y
  · simpa [svTorusVerticalRows,
      sixVertexFourByFourAuditedParamSourceFirst] using hfirstCount 3
  · simpa [svTorusVerticalRows,
      sixVertexFourByFourAuditedParamSourceSecond] using hsecondCount 3

end

end StatMech.FrontierD
