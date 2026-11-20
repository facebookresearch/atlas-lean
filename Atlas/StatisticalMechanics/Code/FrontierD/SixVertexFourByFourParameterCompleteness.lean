/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexFourByFourRowAutomaton









namespace StatMech.FrontierD

theorem sixVertexFourByFourAudited_rowOfBits_injective :
    Function.Injective (Nat.ofBits : SixVertexRow 4 -> Nat) := by
  intro a b h
  funext x
  have hx := congrArg (fun n : Nat => n.testBit x.val) h
  simpa [Nat.testBit_ofBits_lt _ x.val x.isLt] using hx

theorem sixVertexFourByFourAudited_firstRowZero_reverse
    (firstSeam secondSeam state : Fin 4) :
    sixVertexFourByFourAuditedFirstStateDecode
        (sixVertexFourByFourNextVerticalRow
          (sixVertexFourByFourRowOfMask
            (sixVertexFourByFourAuditedRowZero
              (sixVertexFourByFourAuditedCoordinateRowZero
                firstSeam secondSeam)).1)
          (sixVertexFourByFourAuditedFirstStateRow state)) =
      some (sixVertexFourByFourAuditedOppositeSeam firstSeam) <->
    state = firstSeam := by
  fin_cases firstSeam <;> fin_cases secondSeam <;> fin_cases state <;> decide

theorem sixVertexFourByFourAudited_secondRowZero_reverse
    (firstSeam secondSeam state : Fin 4) :
    sixVertexFourByFourAuditedSecondStateDecode
        (sixVertexFourByFourNextVerticalRow
          (sixVertexFourByFourRowOfMask
            (sixVertexFourByFourAuditedRowZero
              (sixVertexFourByFourAuditedCoordinateRowZero
                firstSeam secondSeam)).2)
          (sixVertexFourByFourAuditedSecondStateRow state)) =
      some (sixVertexFourByFourAuditedOppositeSeam secondSeam) <->
    state = secondSeam := by
  fin_cases firstSeam <;> fin_cases secondSeam <;> fin_cases state <;> decide

theorem sixVertexFourByFourAudited_nextVerticalRow_constant
    (value : Bool) (below : SixVertexRow 4) :
    sixVertexFourByFourNextVerticalRow
        (fun _ => value) below = below := by
  funext x
  unfold sixVertexFourByFourNextVerticalRow
  generalize below x = b
  cases value <;> cases b <;> simp

def sixVertexFourByFourAuditedDecodedSeams : Fin 16 -> Fin 4 × Fin 4 := ![
  (0, 1), (0, 0), (0, 2), (0, 3),
  (1, 1), (1, 0), (1, 2), (1, 3),
  (3, 1), (3, 0), (3, 2), (3, 3),
  (2, 1), (2, 0), (2, 2), (2, 3)
]

theorem sixVertexFourByFourAudited_decodedSeams_inverse (rowZero : Fin 16) :
    sixVertexFourByFourAuditedCoordinateRowZero
        (sixVertexFourByFourAuditedDecodedSeams rowZero).1 (sixVertexFourByFourAuditedDecodedSeams rowZero).2 =
      rowZero := by
  fin_cases rowZero <;> decide

theorem sixVertexFourByFourAudited_firstDecode_exists_of_count
    (row : SixVertexRow 4) (hcount : sixVertexUpCount row = 1) :
    exists state, sixVertexFourByFourAuditedFirstStateDecode row = some state := by
  cases hdecode : sixVertexFourByFourAuditedFirstStateDecode row with
  | some state => exact ⟨state, rfl⟩
  | none =>
      have hspec := sixVertexFourByFourAudited_firstStateDecode_spec row
      rw [hdecode] at hspec
      exact (hspec hcount).elim

theorem sixVertexFourByFourAudited_secondDecode_exists_of_count
    (row : SixVertexRow 4) (hcount : sixVertexUpCount row = 3) :
    exists state, sixVertexFourByFourAuditedSecondStateDecode row = some state := by
  cases hdecode : sixVertexFourByFourAuditedSecondStateDecode row with
  | some state => exact ⟨state, rfl⟩
  | none =>
      have hspec := sixVertexFourByFourAudited_secondStateDecode_spec row
      rw [hdecode] at hspec
      exact (hspec hcount).elim

theorem sixVertexFourByFourAudited_firstRow_eq_of_decode
    (row : SixVertexRow 4) (state : Fin 4)
    (hdecode : sixVertexFourByFourAuditedFirstStateDecode row = some state) :
    row = sixVertexFourByFourAuditedFirstStateRow state := by
  have hspec := sixVertexFourByFourAudited_firstStateDecode_spec row
  rw [hdecode] at hspec
  exact sixVertexFourByFourAudited_rowOfBits_injective hspec

theorem sixVertexFourByFourAudited_secondRow_eq_of_decode
    (row : SixVertexRow 4) (state : Fin 4)
    (hdecode : sixVertexFourByFourAuditedSecondStateDecode row = some state) :
    row = sixVertexFourByFourAuditedSecondStateRow state := by
  have hspec := sixVertexFourByFourAudited_secondStateDecode_spec row
  rw [hdecode] at hspec
  exact sixVertexFourByFourAudited_rowOfBits_injective hspec

@[simp] theorem sixVertexFourByFourAudited_firstDecode_state (state : Fin 4) :
    sixVertexFourByFourAuditedFirstStateDecode
        (sixVertexFourByFourAuditedFirstStateRow state) = some state := by
  fin_cases state <;> decide

@[simp] theorem sixVertexFourByFourAudited_secondDecode_state (state : Fin 4) :
    sixVertexFourByFourAuditedSecondStateDecode
        (sixVertexFourByFourAuditedSecondStateRow state) = some state := by
  fin_cases state <;> decide

@[simp] theorem sixVertexFourByFourAudited_nextVerticalRow_zero (below : SixVertexRow 4) :
    sixVertexFourByFourNextVerticalRow
        (sixVertexFourByFourRowOfMask 0) below = below := by
  rw [show sixVertexFourByFourRowOfMask 0 = fun _ => false by
    funext x
    fin_cases x <;> decide]
  exact sixVertexFourByFourAudited_nextVerticalRow_constant false below

@[simp] theorem sixVertexFourByFourAudited_nextVerticalRow_fifteen (below : SixVertexRow 4) :
    sixVertexFourByFourNextVerticalRow
        (sixVertexFourByFourRowOfMask 15) below = below := by
  rw [show sixVertexFourByFourRowOfMask 15 = fun _ => true by
    funext x
    fin_cases x <;> decide]
  exact sixVertexFourByFourAudited_nextVerticalRow_constant true below

theorem sixVertexFourByFourAudited_firstVerticalRow_three_eq_two
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam : Fin 4) :
    sixVertexFourByFourAuditedParamVerticalRowsFirst p seam 3 =
      sixVertexFourByFourAuditedParamVerticalRowsFirst p seam 2 := by
  rcases p with ⟨rowZero, firstMiddle, secondMiddle, last⟩
  fin_cases last <;>
    simp [sixVertexFourByFourAuditedParamVerticalRowsFirst,
      sixVertexFourByFourAuditedParamHorizontalRowsFirst,
      sixVertexFourByFourAuditedRowLast,
      sixVertexFourByFourAllowedHorizontalIndex,
      sixVertexFourByFourAllowedHorizontalMask]

theorem sixVertexFourByFourAudited_secondVerticalRow_three_eq_two
    (p : SixVertexFourByFourAuditedHorizontalParameters) (seam : Fin 4) :
    sixVertexFourByFourAuditedParamVerticalRowsSecond p seam 3 =
      sixVertexFourByFourAuditedParamVerticalRowsSecond p seam 2 := by
  rcases p with ⟨rowZero, firstMiddle, secondMiddle, last⟩
  fin_cases last <;>
    simp [sixVertexFourByFourAuditedParamVerticalRowsSecond,
      sixVertexFourByFourAuditedParamHorizontalRowsSecond,
      sixVertexFourByFourAuditedRowLast,
      sixVertexFourByFourAllowedHorizontalIndex,
      sixVertexFourByFourAllowedHorizontalMask]

def sixVertexFourByFourAuditedParameterSourcePair
    (p : SixVertexFourByFourAuditedHorizontalParameters) :
    SixVertexArrows sixVertexFourByFourTorus ×
      SixVertexArrows sixVertexFourByFourTorus :=
  let seams := sixVertexFourByFourAuditedDecodedSeams p.1
  (sixVertexFourByFourAuditedParamSourceFirst p seams.1,
    sixVertexFourByFourAuditedParamSourceSecond p seams.2)

def SixVertexFourByFourAuditedParameterValid
    (p : SixVertexFourByFourAuditedHorizontalParameters) : Prop :=
  (sixVertexFourByFourAuditedParameterSourcePair p).1.IceRule /\
    (sixVertexFourByFourAuditedParameterSourcePair p).2.IceRule /\
    sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus
          (sixVertexFourByFourAuditedParameterSourcePair p).1
          (svFinLast sixVertexFourByFourTorus.height_pos)) = 1 /\
    sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus
          (sixVertexFourByFourAuditedParameterSourcePair p).2
          (svFinLast sixVertexFourByFourTorus.height_pos)) = 3

theorem sixVertexFourByFourAudited_firstMiddlePath_of_valid
    (p : SixVertexFourByFourAuditedHorizontalParameters)
    (firstSeam secondSeam : Fin 4)
    (hrowZero : sixVertexFourByFourAuditedCoordinateRowZero
      firstSeam secondSeam = p.1)
    (hice : (sixVertexFourByFourAuditedParamSourceFirst p firstSeam).IceRule)
    (hsector : sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByFourTorus
        (sixVertexFourByFourAuditedParamSourceFirst p firstSeam)
        (svFinLast sixVertexFourByFourTorus.height_pos)) = 1) :
    (sixVertexFourByFourAuditedFirstTransition
          (sixVertexFourByFourAuditedOppositeSeam firstSeam) p.2.1 >>= fun s =>
        sixVertexFourByFourAuditedFirstTransition s p.2.2.1) =
      some firstSeam := by
  let rows := sixVertexFourByFourAuditedParamVerticalRowsFirst p firstSeam
  have hcount (y : Fin 4) : sixVertexUpCount (rows y) = 1 := by
    exact sixVertexFourByFourAuditedParamSourceFirst_verticalRowCount
      p firstSeam y hice hsector
  have hdecodeZero :
      sixVertexFourByFourAuditedFirstStateDecode (rows 0) =
        some (sixVertexFourByFourAuditedOppositeSeam firstSeam) := by
    simpa [rows, sixVertexFourByFourAuditedParamVerticalRowsFirst,
      sixVertexFourByFourAuditedParamHorizontalRowsFirst, hrowZero] using
      sixVertexFourByFourAudited_firstRowZero_opposite firstSeam secondSeam
  have hrowZeroState := sixVertexFourByFourAudited_firstRow_eq_of_decode _ _ hdecodeZero
  obtain ⟨stateOne, hdecodeOne⟩ :=
    sixVertexFourByFourAudited_firstDecode_exists_of_count (rows 1) (hcount 1)
  obtain ⟨stateTwo, hdecodeTwo⟩ :=
    sixVertexFourByFourAudited_firstDecode_exists_of_count (rows 2) (hcount 2)
  obtain ⟨stateThree, hdecodeThree⟩ :=
    sixVertexFourByFourAudited_firstDecode_exists_of_count (rows 3) (hcount 3)
  have hrowOneState := sixVertexFourByFourAudited_firstRow_eq_of_decode _ _ hdecodeOne
  have hrowTwoState := sixVertexFourByFourAudited_firstRow_eq_of_decode _ _ hdecodeTwo
  have hrowThreeState := sixVertexFourByFourAudited_firstRow_eq_of_decode _ _ hdecodeThree
  have htransitionOne :
      sixVertexFourByFourAuditedFirstTransition
          (sixVertexFourByFourAuditedOppositeSeam firstSeam) p.2.1 =
        some stateOne := by
    unfold sixVertexFourByFourAuditedFirstTransition
    rw [← hrowZeroState]
    simpa [rows, sixVertexFourByFourAuditedParamVerticalRowsFirst,
      sixVertexFourByFourAuditedParamHorizontalRowsFirst,
      sixVertexFourByFourAuditedFirstMiddleRow] using hdecodeOne
  have htransitionTwo :
      sixVertexFourByFourAuditedFirstTransition stateOne p.2.2.1 =
        some stateTwo := by
    unfold sixVertexFourByFourAuditedFirstTransition
    rw [← hrowOneState]
    simpa [rows, sixVertexFourByFourAuditedParamVerticalRowsFirst,
      sixVertexFourByFourAuditedParamHorizontalRowsFirst,
      sixVertexFourByFourAuditedFirstMiddleRow] using hdecodeTwo
  have hrowIceZero := sixVertexFourByFour_rowIce
    (sixVertexFourByFourAuditedParamSourceFirst p firstSeam) hice 0
  change svHorizontalIce sixVertexFourByFourTorus.width_pos
      (rows 3) (rows 0)
      (sixVertexFourByFourAuditedParamHorizontalRowsFirst p 0) at hrowIceZero
  have hnextZero := sixVertexFourByFourAudited_nextVerticalRow_eq_of_ice
    (rows 3) (rows 0)
      (sixVertexFourByFourAuditedParamHorizontalRowsFirst p 0) hrowIceZero
  have hrowZeroReverse :
      sixVertexFourByFourAuditedFirstStateDecode
          (sixVertexFourByFourNextVerticalRow
            (sixVertexFourByFourRowOfMask
              (sixVertexFourByFourAuditedRowZero
                (sixVertexFourByFourAuditedCoordinateRowZero
                  firstSeam secondSeam)).1)
            (sixVertexFourByFourAuditedFirstStateRow stateThree)) =
        some (sixVertexFourByFourAuditedOppositeSeam firstSeam) := by
    rw [← hrowThreeState]
    have hdecodeNext := congrArg
      sixVertexFourByFourAuditedFirstStateDecode hnextZero
    rw [hdecodeZero] at hdecodeNext
    simpa [sixVertexFourByFourAuditedParamHorizontalRowsFirst,
      hrowZero] using hdecodeNext
  have hstateThree : stateThree = firstSeam :=
    (sixVertexFourByFourAudited_firstRowZero_reverse firstSeam secondSeam stateThree).mp
      hrowZeroReverse
  have hlast := sixVertexFourByFourAudited_firstVerticalRow_three_eq_two p firstSeam
  have hstateTwoThree : stateTwo = stateThree := by
    have hdecodeLast := congrArg
      sixVertexFourByFourAuditedFirstStateDecode hlast
    change rows 3 = rows 2 at hlast
    rw [hdecodeThree, hdecodeTwo] at hdecodeLast
    exact (Option.some.inj hdecodeLast).symm
  rw [htransitionOne]
  change sixVertexFourByFourAuditedFirstTransition stateOne p.2.2.1 =
    some firstSeam
  rw [htransitionTwo]
  exact congrArg some (hstateTwoThree.trans hstateThree)

theorem sixVertexFourByFourAudited_secondMiddlePath_of_valid
    (p : SixVertexFourByFourAuditedHorizontalParameters)
    (firstSeam secondSeam : Fin 4)
    (hrowZero : sixVertexFourByFourAuditedCoordinateRowZero
      firstSeam secondSeam = p.1)
    (hice : (sixVertexFourByFourAuditedParamSourceSecond p secondSeam).IceRule)
    (hsector : sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByFourTorus
        (sixVertexFourByFourAuditedParamSourceSecond p secondSeam)
        (svFinLast sixVertexFourByFourTorus.height_pos)) = 3) :
    (sixVertexFourByFourAuditedSecondTransition
          (sixVertexFourByFourAuditedOppositeSeam secondSeam) p.2.1 >>= fun s =>
        sixVertexFourByFourAuditedSecondTransition s p.2.2.1) =
      some secondSeam := by
  let rows := sixVertexFourByFourAuditedParamVerticalRowsSecond p secondSeam
  have hcount (y : Fin 4) : sixVertexUpCount (rows y) = 3 := by
    exact sixVertexFourByFourAuditedParamSourceSecond_verticalRowCount
      p secondSeam y hice hsector
  have hdecodeZero :
      sixVertexFourByFourAuditedSecondStateDecode (rows 0) =
        some (sixVertexFourByFourAuditedOppositeSeam secondSeam) := by
    simpa [rows, sixVertexFourByFourAuditedParamVerticalRowsSecond,
      sixVertexFourByFourAuditedParamHorizontalRowsSecond, hrowZero] using
      sixVertexFourByFourAudited_secondRowZero_opposite firstSeam secondSeam
  have hrowZeroState := sixVertexFourByFourAudited_secondRow_eq_of_decode _ _ hdecodeZero
  obtain ⟨stateOne, hdecodeOne⟩ :=
    sixVertexFourByFourAudited_secondDecode_exists_of_count (rows 1) (hcount 1)
  obtain ⟨stateTwo, hdecodeTwo⟩ :=
    sixVertexFourByFourAudited_secondDecode_exists_of_count (rows 2) (hcount 2)
  obtain ⟨stateThree, hdecodeThree⟩ :=
    sixVertexFourByFourAudited_secondDecode_exists_of_count (rows 3) (hcount 3)
  have hrowOneState := sixVertexFourByFourAudited_secondRow_eq_of_decode _ _ hdecodeOne
  have hrowTwoState := sixVertexFourByFourAudited_secondRow_eq_of_decode _ _ hdecodeTwo
  have hrowThreeState := sixVertexFourByFourAudited_secondRow_eq_of_decode _ _ hdecodeThree
  have htransitionOne :
      sixVertexFourByFourAuditedSecondTransition
          (sixVertexFourByFourAuditedOppositeSeam secondSeam) p.2.1 =
        some stateOne := by
    unfold sixVertexFourByFourAuditedSecondTransition
    rw [← hrowZeroState]
    simpa [rows, sixVertexFourByFourAuditedParamVerticalRowsSecond,
      sixVertexFourByFourAuditedParamHorizontalRowsSecond,
      sixVertexFourByFourAuditedSecondMiddleRow] using hdecodeOne
  have htransitionTwo :
      sixVertexFourByFourAuditedSecondTransition stateOne p.2.2.1 =
        some stateTwo := by
    unfold sixVertexFourByFourAuditedSecondTransition
    rw [← hrowOneState]
    simpa [rows, sixVertexFourByFourAuditedParamVerticalRowsSecond,
      sixVertexFourByFourAuditedParamHorizontalRowsSecond,
      sixVertexFourByFourAuditedSecondMiddleRow] using hdecodeTwo
  have hrowIceZero := sixVertexFourByFour_rowIce
    (sixVertexFourByFourAuditedParamSourceSecond p secondSeam) hice 0
  change svHorizontalIce sixVertexFourByFourTorus.width_pos
      (rows 3) (rows 0)
      (sixVertexFourByFourAuditedParamHorizontalRowsSecond p 0) at hrowIceZero
  have hnextZero := sixVertexFourByFourAudited_nextVerticalRow_eq_of_ice
    (rows 3) (rows 0)
      (sixVertexFourByFourAuditedParamHorizontalRowsSecond p 0) hrowIceZero
  have hrowZeroReverse :
      sixVertexFourByFourAuditedSecondStateDecode
          (sixVertexFourByFourNextVerticalRow
            (sixVertexFourByFourRowOfMask
              (sixVertexFourByFourAuditedRowZero
                (sixVertexFourByFourAuditedCoordinateRowZero
                  firstSeam secondSeam)).2)
            (sixVertexFourByFourAuditedSecondStateRow stateThree)) =
        some (sixVertexFourByFourAuditedOppositeSeam secondSeam) := by
    rw [← hrowThreeState]
    have hdecodeNext := congrArg
      sixVertexFourByFourAuditedSecondStateDecode hnextZero
    rw [hdecodeZero] at hdecodeNext
    simpa [sixVertexFourByFourAuditedParamHorizontalRowsSecond,
      hrowZero] using hdecodeNext
  have hstateThree : stateThree = secondSeam :=
    (sixVertexFourByFourAudited_secondRowZero_reverse firstSeam secondSeam stateThree).mp
      hrowZeroReverse
  have hlast := sixVertexFourByFourAudited_secondVerticalRow_three_eq_two p secondSeam
  have hstateTwoThree : stateTwo = stateThree := by
    have hdecodeLast := congrArg
      sixVertexFourByFourAuditedSecondStateDecode hlast
    change rows 3 = rows 2 at hlast
    rw [hdecodeThree, hdecodeTwo] at hdecodeLast
    exact (Option.some.inj hdecodeLast).symm
  rw [htransitionOne]
  change sixVertexFourByFourAuditedSecondTransition stateOne p.2.2.1 =
    some secondSeam
  rw [htransitionTwo]
  exact congrArg some (hstateTwoThree.trans hstateThree)

theorem sixVertexFourByFourAudited_parameterValid_uniqueCoordinate
    (p : SixVertexFourByFourAuditedHorizontalParameters)
    (hvalid : SixVertexFourByFourAuditedParameterValid p) :
    ∃! c : SixVertexFourByFourAuditedCoordinates,
      sixVertexFourByFourAuditedCoordinateParameters c = p := by
  let seams := sixVertexFourByFourAuditedDecodedSeams p.1
  have hrowZero : sixVertexFourByFourAuditedCoordinateRowZero
      seams.1 seams.2 = p.1 := by
    exact sixVertexFourByFourAudited_decodedSeams_inverse p.1
  unfold SixVertexFourByFourAuditedParameterValid sixVertexFourByFourAuditedParameterSourcePair at hvalid
  dsimp only at hvalid
  have hfirstPath := sixVertexFourByFourAudited_firstMiddlePath_of_valid
    p seams.1 seams.2 hrowZero hvalid.1 hvalid.2.2.1
  have hsecondPath := sixVertexFourByFourAudited_secondMiddlePath_of_valid
    p seams.1 seams.2 hrowZero hvalid.2.1 hvalid.2.2.2
  have hpath : sixVertexFourByFourAuditedMiddlePathAllowed
      seams.1 seams.2 p.2.1 p.2.2.1 := ⟨hfirstPath, hsecondPath⟩
  obtain ⟨middle, hmiddle⟩ :=
    (sixVertexFourByFourAudited_middlePathAllowed_iff_template
      seams.1 seams.2 p.2.1 p.2.2.1).mp hpath
  let c : SixVertexFourByFourAuditedCoordinates :=
    ⟨seams.1, seams.2, middle, p.2.2.2⟩
  have hc : sixVertexFourByFourAuditedCoordinateParameters c = p := by
    unfold sixVertexFourByFourAuditedCoordinateParameters c
    dsimp only
    apply Prod.ext
    · exact hrowZero
    · apply Prod.ext
      · change (sixVertexFourByFourAuditedMiddlePair
            seams.1 seams.2 middle).1 = p.2.1
        exact congrArg Prod.fst hmiddle.symm
      · apply Prod.ext
        · change (sixVertexFourByFourAuditedMiddlePair
              seams.1 seams.2 middle).2 = p.2.2.1
          exact congrArg Prod.snd hmiddle.symm
        · rfl
  refine ⟨c, hc, ?_⟩
  intro other hother
  exact sixVertexFourByFourAuditedCoordinateParameters_injective
    (hother.trans hc.symm)

theorem sixVertexFourByFourAudited_decodedSeams_coordinateRowZero
    (firstSeam secondSeam : Fin 4) :
    sixVertexFourByFourAuditedDecodedSeams
        (sixVertexFourByFourAuditedCoordinateRowZero firstSeam secondSeam) =
      (firstSeam, secondSeam) := by
  fin_cases firstSeam <;> fin_cases secondSeam <;> decide

theorem sixVertexFourByFourAudited_coordinateParameters_valid
    (c : SixVertexFourByFourAuditedCoordinates) :
    SixVertexFourByFourAuditedParameterValid
      (sixVertexFourByFourAuditedCoordinateParameters c) := by
  have hsource := sixVertexFourByFourAuditedCoordinateSourcePair_valid c
  simpa [SixVertexFourByFourAuditedParameterValid,
    sixVertexFourByFourAuditedParameterSourcePair,
    sixVertexFourByFourAuditedCoordinateSourcePair,
    sixVertexFourByFourAuditedCoordinateParameters,
    sixVertexFourByFourAudited_decodedSeams_coordinateRowZero] using hsource

noncomputable def sixVertexFourByFourAuditedValidParameterSet :
    Finset SixVertexFourByFourAuditedHorizontalParameters := by
  classical
  exact Finset.univ.filter SixVertexFourByFourAuditedParameterValid

theorem sixVertexFourByFourAudited_validParameterSet_eq_coordinateImage :
    sixVertexFourByFourAuditedValidParameterSet =
      sixVertexFourByFourAuditedCoordinateParameterImage := by
  classical
  ext p
  simp only [sixVertexFourByFourAuditedValidParameterSet,
    Finset.mem_filter, Finset.mem_univ, true_and,
    sixVertexFourByFourAuditedCoordinateParameterImage, Finset.mem_image]
  constructor
  · intro hvalid
    obtain ⟨c, hc, _⟩ :=
      sixVertexFourByFourAudited_parameterValid_uniqueCoordinate p hvalid
    exact ⟨c, hc⟩
  · rintro ⟨c, rfl⟩
    exact sixVertexFourByFourAudited_coordinateParameters_valid c

theorem sixVertexFourByFourAudited_validParameterSet_card :
    sixVertexFourByFourAuditedValidParameterSet.card = 512 := by
  rw [sixVertexFourByFourAudited_validParameterSet_eq_coordinateImage]
  exact sixVertexFourByFourAuditedCoordinateParameterImage_card



def SixVertexFourByFourAuditedValidParameter :=
  {p : SixVertexFourByFourAuditedHorizontalParameters //
    SixVertexFourByFourAuditedParameterValid p}

noncomputable def sixVertexFourByFourAuditedValidParameterCoordinate
    (p : SixVertexFourByFourAuditedValidParameter) :
    SixVertexFourByFourAuditedCoordinates :=
  Classical.choose
    (sixVertexFourByFourAudited_parameterValid_uniqueCoordinate p.1 p.2).exists

theorem sixVertexFourByFourAuditedValidParameterCoordinate_spec
    (p : SixVertexFourByFourAuditedValidParameter) :
    sixVertexFourByFourAuditedCoordinateParameters
        (sixVertexFourByFourAuditedValidParameterCoordinate p) = p.1 :=
  Classical.choose_spec
    (sixVertexFourByFourAudited_parameterValid_uniqueCoordinate p.1 p.2).exists

theorem sixVertexFourByFourAuditedValidParameterCoordinate_injective :
    Function.Injective sixVertexFourByFourAuditedValidParameterCoordinate := by
  intro p q hcoordinate
  apply Subtype.ext
  rw [← sixVertexFourByFourAuditedValidParameterCoordinate_spec p,
    ← sixVertexFourByFourAuditedValidParameterCoordinate_spec q,
    hcoordinate]

def sixVertexFourByFourAuditedValidParameterSourcePair
    (p : SixVertexFourByFourAuditedValidParameter) :
    SixVertexArrows sixVertexFourByFourTorus ×
      SixVertexArrows sixVertexFourByFourTorus :=
  sixVertexFourByFourAuditedParameterSourcePair p.1

noncomputable def sixVertexFourByFourAuditedValidParameterTargetPair
    (p : SixVertexFourByFourAuditedValidParameter) :
    SixVertexArrows sixVertexFourByFourTorus ×
      SixVertexArrows sixVertexFourByFourTorus :=
  sixVertexFourByFourAuditedCoordinateTargetPair
    (sixVertexFourByFourAuditedValidParameterCoordinate p)

theorem sixVertexFourByFourAuditedValidParameter_source_eq_coordinateSource
    (p : SixVertexFourByFourAuditedValidParameter) :
    sixVertexFourByFourAuditedValidParameterSourcePair p =
      sixVertexFourByFourAuditedCoordinateSourcePair
        (sixVertexFourByFourAuditedValidParameterCoordinate p) := by
  let c := sixVertexFourByFourAuditedValidParameterCoordinate p
  have hc := sixVertexFourByFourAuditedValidParameterCoordinate_spec p
  change sixVertexFourByFourAuditedCoordinateParameters c = p.1 at hc
  change sixVertexFourByFourAuditedParameterSourcePair p.1 =
    sixVertexFourByFourAuditedCoordinateSourcePair c
  rw [← hc]
  simp [sixVertexFourByFourAuditedParameterSourcePair,
    sixVertexFourByFourAuditedCoordinateSourcePair,
    sixVertexFourByFourAuditedCoordinateParameters,
    sixVertexFourByFourAudited_decodedSeams_coordinateRowZero]

theorem sixVertexFourByFourAuditedValidParameter_matching :
    Function.Injective sixVertexFourByFourAuditedValidParameterSourcePair /\
      Function.Injective sixVertexFourByFourAuditedValidParameterTargetPair /\
      forall p,
        SixVertexFourByFourAuditedParameterValid p.1 /\
          SixVertexFourByFourAuditedCoordinateTargetPairValid
            (sixVertexFourByFourAuditedValidParameterCoordinate p) /\
          sixVertexPairAtMostTwoCycleFineRelated
            (sixVertexFourByFourAuditedValidParameterSourcePair p)
            (sixVertexFourByFourAuditedValidParameterTargetPair p) := by
  constructor
  · intro p q hsource
    apply sixVertexFourByFourAuditedValidParameterCoordinate_injective
    apply sixVertexFourByFourAuditedCoordinateSourcePair_injective
    rw [← sixVertexFourByFourAuditedValidParameter_source_eq_coordinateSource p,
      ← sixVertexFourByFourAuditedValidParameter_source_eq_coordinateSource q]
    exact hsource
  constructor
  · intro p q htarget
    apply sixVertexFourByFourAuditedValidParameterCoordinate_injective
    apply sixVertexFourByFourAuditedCoordinateTargetPair_injective
    exact htarget
  · intro p
    constructor
    · exact p.2
    constructor
    · exact sixVertexFourByFourAuditedCoordinateTargetPair_valid _
    · rw [sixVertexFourByFourAuditedValidParameter_source_eq_coordinateSource]
      exact sixVertexFourByFourAuditedCoordinate_fineRelated _

end StatMech.FrontierD
