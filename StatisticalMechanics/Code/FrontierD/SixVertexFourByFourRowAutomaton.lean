/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexFourByFourTwoCycleMatching









namespace StatMech.FrontierD

def sixVertexFourByFourAuditedOppositeSeam : Fin 4 -> Fin 4 := ![2, 3, 0, 1]

def sixVertexFourByFourAuditedFirstStateRow (state : Fin 4) : SixVertexRow 4 :=
  sixVertexFourByFourRowOfMask
    (sixVertexFourByFourSectorOneSeamMask state)

def sixVertexFourByFourAuditedSecondStateRow (state : Fin 4) : SixVertexRow 4 :=
  sixVertexFourByFourRowOfMask
    (sixVertexFourByFourSectorThreeSeamMask state)

def sixVertexFourByFourAuditedFirstMiddleRow (middle : Fin 16) : SixVertexRow 4 :=
  sixVertexFourByFourRowOfMask
    (sixVertexFourByFourAuditedRowMiddle middle).1

def sixVertexFourByFourAuditedSecondMiddleRow (middle : Fin 16) : SixVertexRow 4 :=
  sixVertexFourByFourRowOfMask
    (sixVertexFourByFourAuditedRowMiddle middle).2

theorem sixVertexFourByFourAudited_nextVerticalRow_eq_of_ice
    (below current horizontal : SixVertexRow 4)
    (hice : svHorizontalIce (by norm_num) below current horizontal) :
    sixVertexFourByFourNextVerticalRow horizontal below = current := by
  funext x
  have hx := hice x
  unfold svHorizontalIce svHorizontalIncomingCount at hx
  unfold sixVertexFourByFourNextVerticalRow
  generalize horizontal (SixVertexArrows.cyclicPred (by norm_num) x) = a at hx ⊢
  generalize horizontal x = b at hx ⊢
  generalize below x = c at hx ⊢
  generalize current x = d at hx ⊢
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

def sixVertexFourByFourAuditedFirstStateDecode (row : SixVertexRow 4) : Option (Fin 4) :=
  let code := Nat.ofBits row
  if code = 1 then some 0
  else if code = 2 then some 1
  else if code = 4 then some 2
  else if code = 8 then some 3
  else none

def sixVertexFourByFourAuditedSecondStateDecode (row : SixVertexRow 4) : Option (Fin 4) :=
  let code := Nat.ofBits row
  if code = 7 then some 0
  else if code = 11 then some 1
  else if code = 13 then some 2
  else if code = 14 then some 3
  else none

theorem sixVertexFourByFourAudited_firstStateCode_iff (row : SixVertexRow 4) :
    sixVertexUpCount row = 1 <->
      Nat.ofBits row = 1 \/ Nat.ofBits row = 2 \/
        Nat.ofBits row = 4 \/ Nat.ofBits row = 8 := by
  revert row
  decide

theorem sixVertexFourByFourAudited_secondStateCode_iff (row : SixVertexRow 4) :
    sixVertexUpCount row = 3 <->
      Nat.ofBits row = 7 \/ Nat.ofBits row = 11 \/
        Nat.ofBits row = 13 \/ Nat.ofBits row = 14 := by
  revert row
  decide

theorem sixVertexFourByFourAudited_firstStateDecode_spec (row : SixVertexRow 4) :
    match sixVertexFourByFourAuditedFirstStateDecode row with
    | some state => Nat.ofBits row = Nat.ofBits (sixVertexFourByFourAuditedFirstStateRow state)
    | none => sixVertexUpCount row ≠ 1 := by
  have hcode := sixVertexFourByFourAudited_firstStateCode_iff row
  simp only [sixVertexFourByFourAuditedFirstStateDecode]
  split_ifs with h1 h2 h3 h4 <;>
    simp_all [sixVertexFourByFourAuditedFirstStateRow,
      sixVertexFourByFourSectorOneSeamMask] <;> decide

theorem sixVertexFourByFourAudited_secondStateDecode_spec (row : SixVertexRow 4) :
    match sixVertexFourByFourAuditedSecondStateDecode row with
    | some state => Nat.ofBits row = Nat.ofBits (sixVertexFourByFourAuditedSecondStateRow state)
    | none => sixVertexUpCount row ≠ 3 := by
  have hcode := sixVertexFourByFourAudited_secondStateCode_iff row
  simp only [sixVertexFourByFourAuditedSecondStateDecode]
  split_ifs with h1 h2 h3 h4 <;>
    simp_all [sixVertexFourByFourAuditedSecondStateRow,
      sixVertexFourByFourSectorThreeSeamMask] <;> decide

def sixVertexFourByFourAuditedFirstTransition (state : Fin 4) (middle : Fin 16) : Option (Fin 4) :=
  sixVertexFourByFourAuditedFirstStateDecode
    (sixVertexFourByFourNextVerticalRow
      (sixVertexFourByFourAuditedFirstMiddleRow middle) (sixVertexFourByFourAuditedFirstStateRow state))

def sixVertexFourByFourAuditedSecondTransition (state : Fin 4) (middle : Fin 16) : Option (Fin 4) :=
  sixVertexFourByFourAuditedSecondStateDecode
    (sixVertexFourByFourNextVerticalRow
      (sixVertexFourByFourAuditedSecondMiddleRow middle) (sixVertexFourByFourAuditedSecondStateRow state))

def sixVertexFourByFourAuditedFirstTransitionTable : Fin 4 -> Fin 16 -> Option (Fin 4) := ![
  ![some 0, some 0, some 0, some 0, some 2, some 2, none, none,
    none, none, none, none, some 0, some 0, some 0, some 0],
  ![some 1, some 1, some 1, some 1, none, none, some 3, some 3,
    none, none, none, none, some 1, some 1, some 1, some 1],
  ![some 2, some 2, some 2, some 2, none, none, none, none,
    none, none, some 0, some 0, some 2, some 2, some 2, some 2],
  ![some 3, some 3, some 3, some 3, none, none, none, none,
    some 1, some 1, none, none, some 3, some 3, some 3, some 3]
]

def sixVertexFourByFourAuditedSecondTransitionTable : Fin 4 -> Fin 16 -> Option (Fin 4) := ![
  ![none, some 2, none, none, some 0, some 0, some 0, some 0,
    some 0, some 0, some 0, some 0, none, some 2, none, none],
  ![some 3, none, none, none, some 1, some 1, some 1, some 1,
    some 1, some 1, some 1, some 1, some 3, none, none, none],
  ![none, none, some 0, none, some 2, some 2, some 2, some 2,
    some 2, some 2, some 2, some 2, none, none, some 0, none],
  ![none, none, none, some 1, some 3, some 3, some 3, some 3,
    some 3, some 3, some 3, some 3, none, none, none, some 1]
]

theorem sixVertexFourByFourAudited_firstTransition_table (state : Fin 4) (middle : Fin 16) :
    sixVertexFourByFourAuditedFirstTransition state middle =
      sixVertexFourByFourAuditedFirstTransitionTable state middle := by
  fin_cases state <;> fin_cases middle <;> decide

theorem sixVertexFourByFourAudited_secondTransition_table (state : Fin 4) (middle : Fin 16) :
    sixVertexFourByFourAuditedSecondTransition state middle =
      sixVertexFourByFourAuditedSecondTransitionTable state middle := by
  fin_cases state <;> fin_cases middle <;> decide

theorem sixVertexFourByFourAudited_firstRowZero_opposite (firstSeam secondSeam : Fin 4) :
    sixVertexFourByFourAuditedFirstStateDecode
        (sixVertexFourByFourNextVerticalRow
          (sixVertexFourByFourRowOfMask
            (sixVertexFourByFourAuditedRowZero
              (sixVertexFourByFourAuditedCoordinateRowZero
                firstSeam secondSeam)).1)
          (sixVertexFourByFourAuditedFirstStateRow firstSeam)) =
      some (sixVertexFourByFourAuditedOppositeSeam firstSeam) := by
  fin_cases firstSeam <;> fin_cases secondSeam <;> decide

theorem sixVertexFourByFourAudited_secondRowZero_opposite (firstSeam secondSeam : Fin 4) :
    sixVertexFourByFourAuditedSecondStateDecode
        (sixVertexFourByFourNextVerticalRow
          (sixVertexFourByFourRowOfMask
            (sixVertexFourByFourAuditedRowZero
              (sixVertexFourByFourAuditedCoordinateRowZero
                firstSeam secondSeam)).2)
          (sixVertexFourByFourAuditedSecondStateRow secondSeam)) =
      some (sixVertexFourByFourAuditedOppositeSeam secondSeam) := by
  fin_cases firstSeam <;> fin_cases secondSeam <;> decide

def sixVertexFourByFourAuditedMiddlePathAllowed
    (firstSeam secondSeam : Fin 4) (firstMiddle secondMiddle : Fin 16) : Prop :=
  (sixVertexFourByFourAuditedFirstTransition (sixVertexFourByFourAuditedOppositeSeam firstSeam) firstMiddle >>= fun s =>
      sixVertexFourByFourAuditedFirstTransition s secondMiddle) = some firstSeam /\
    (sixVertexFourByFourAuditedSecondTransition (sixVertexFourByFourAuditedOppositeSeam secondSeam) firstMiddle >>= fun s =>
      sixVertexFourByFourAuditedSecondTransition s secondMiddle) = some secondSeam

local instance sixVertexFourByFourAuditedMiddlePathAllowedDecidable firstSeam secondSeam
    firstMiddle secondMiddle :
    Decidable (sixVertexFourByFourAuditedMiddlePathAllowed firstSeam secondSeam
      firstMiddle secondMiddle) := by
  unfold sixVertexFourByFourAuditedMiddlePathAllowed
  infer_instance

def sixVertexFourByFourAuditedFirstInnerB (seam : Fin 4) (middle : Fin 16) : Bool :=
  decide (middle = sixVertexFourByFourAuditedMiddleB seam ||
    middle = sixVertexFourByFourAuditedMiddleBNext seam)

def sixVertexFourByFourAuditedFirstOuterB (middle : Fin 16) : Bool :=
  decide (middle.val < 4 || 12 <= middle.val)

def sixVertexFourByFourAuditedSecondInnerB (seam : Fin 4) (middle : Fin 16) : Bool :=
  decide (middle = sixVertexFourByFourAuditedMiddleA seam ||
    middle = sixVertexFourByFourAuditedMiddleC seam)

def sixVertexFourByFourAuditedSecondOuterB (middle : Fin 16) : Bool :=
  decide (4 <= middle.val && middle.val < 12)

def sixVertexFourByFourAuditedFirstCrossB
    (seam : Fin 4) (firstMiddle secondMiddle : Fin 16) : Bool :=
  (sixVertexFourByFourAuditedFirstOuterB firstMiddle && sixVertexFourByFourAuditedFirstInnerB seam secondMiddle) ||
    (sixVertexFourByFourAuditedFirstInnerB seam firstMiddle && sixVertexFourByFourAuditedFirstOuterB secondMiddle)

def sixVertexFourByFourAuditedSecondCrossB
    (seam : Fin 4) (firstMiddle secondMiddle : Fin 16) : Bool :=
  (sixVertexFourByFourAuditedSecondInnerB seam firstMiddle && sixVertexFourByFourAuditedSecondOuterB secondMiddle) ||
    (sixVertexFourByFourAuditedSecondOuterB firstMiddle && sixVertexFourByFourAuditedSecondInnerB seam secondMiddle)

theorem sixVertexFourByFourAudited_firstPath_iff_cross
    (seam : Fin 4) (firstMiddle secondMiddle : Fin 16) :
    (sixVertexFourByFourAuditedFirstTransition (sixVertexFourByFourAuditedOppositeSeam seam) firstMiddle >>= fun s =>
        sixVertexFourByFourAuditedFirstTransition s secondMiddle) = some seam <->
      sixVertexFourByFourAuditedFirstCrossB seam firstMiddle secondMiddle = true := by
  fin_cases seam <;> decide +revert

theorem sixVertexFourByFourAudited_secondPath_iff_cross
    (seam : Fin 4) (firstMiddle secondMiddle : Fin 16) :
    (sixVertexFourByFourAuditedSecondTransition (sixVertexFourByFourAuditedOppositeSeam seam) firstMiddle >>= fun s =>
        sixVertexFourByFourAuditedSecondTransition s secondMiddle) = some seam <->
      sixVertexFourByFourAuditedSecondCrossB seam firstMiddle secondMiddle = true := by
  fin_cases seam <;> decide +revert

theorem sixVertexFourByFourAudited_crosses_iff_template
    (firstSeam secondSeam : Fin 4) (firstMiddle secondMiddle : Fin 16) :
    sixVertexFourByFourAuditedFirstCrossB firstSeam firstMiddle secondMiddle = true /\
        sixVertexFourByFourAuditedSecondCrossB secondSeam firstMiddle secondMiddle = true <->
      exists middle : Fin 8,
        (firstMiddle, secondMiddle) =
          sixVertexFourByFourAuditedMiddlePair
            firstSeam secondSeam middle := by
  fin_cases firstSeam <;> fin_cases secondSeam <;> decide +revert

theorem sixVertexFourByFourAudited_middlePathAllowed_iff_template
    (firstSeam secondSeam : Fin 4) (firstMiddle secondMiddle : Fin 16) :
    sixVertexFourByFourAuditedMiddlePathAllowed firstSeam secondSeam firstMiddle secondMiddle <->
      exists middle : Fin 8,
        (firstMiddle, secondMiddle) =
          sixVertexFourByFourAuditedMiddlePair
            firstSeam secondSeam middle := by
  unfold sixVertexFourByFourAuditedMiddlePathAllowed
  rw [sixVertexFourByFourAudited_firstPath_iff_cross, sixVertexFourByFourAudited_secondPath_iff_cross]
  exact sixVertexFourByFourAudited_crosses_iff_template _ _ _ _

end StatMech.FrontierD
