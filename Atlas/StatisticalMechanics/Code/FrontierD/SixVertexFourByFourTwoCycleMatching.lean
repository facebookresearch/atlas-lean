/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexFourByFourTwoCycleFibre









namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByFourAuditedCoordinateTargetPair
    (c : SixVertexFourByFourAuditedCoordinates) :
    SixVertexArrows sixVertexFourByFourTorus ×
      SixVertexArrows sixVertexFourByFourTorus :=
  let p := sixVertexFourByFourAuditedCoordinateParameters c
  let columns := sixVertexFourByFourAuditedRepairColumns
    c.firstSeam c.secondSeam
  (sixVertexFourByFourAuditedParamTargetFirst p c.firstSeam columns.1,
    sixVertexFourByFourAuditedParamTargetSecond p c.secondSeam columns.2)

def SixVertexFourByFourAuditedCoordinateTargetPairValid
    (c : SixVertexFourByFourAuditedCoordinates) : Prop :=
  (sixVertexFourByFourAuditedCoordinateTargetPair c).1.IceRule /\
    (sixVertexFourByFourAuditedCoordinateTargetPair c).2.IceRule /\
    sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus
          (sixVertexFourByFourAuditedCoordinateTargetPair c).1
          (svFinLast sixVertexFourByFourTorus.height_pos)) = 2 /\
    sixVertexUpCount
        (svTorusVerticalRows sixVertexFourByFourTorus
          (sixVertexFourByFourAuditedCoordinateTargetPair c).2
          (svFinLast sixVertexFourByFourTorus.height_pos)) = 2

theorem sixVertexFourByFourAuditedCoordinateTargetPair_valid
    (c : SixVertexFourByFourAuditedCoordinates) :
    SixVertexFourByFourAuditedCoordinateTargetPairValid c := by
  let p := sixVertexFourByFourAuditedCoordinateParameters c
  have hsource := sixVertexFourByFourAuditedCoordinateSourcePair_valid c
  unfold SixVertexFourByFourAuditedCoordinateSourcePairValid at hsource
  change (sixVertexFourByFourAuditedParamSourceFirst p c.firstSeam).IceRule /\
    (sixVertexFourByFourAuditedParamSourceSecond p c.secondSeam).IceRule /\ _ /\ _
    at hsource
  have hrepair := sixVertexFourByFourAuditedParamMatching_valid
    p c.firstSeam c.secondSeam hsource.1 hsource.2.1
      hsource.2.2.1 hsource.2.2.2
  unfold SixVertexFourByFourAuditedCoordinateTargetPairValid
  unfold SixVertexFourByFourValidColumnRepair at hrepair
  simpa [sixVertexFourByFourAuditedCoordinateTargetPair, p] using hrepair

theorem sixVertexFourByFourAuditedCoordinate_fineRelated
    (c : SixVertexFourByFourAuditedCoordinates) :
    sixVertexPairAtMostTwoCycleFineRelated
      (sixVertexFourByFourAuditedCoordinateSourcePair c)
      (sixVertexFourByFourAuditedCoordinateTargetPair c) := by
  let p := sixVertexFourByFourAuditedCoordinateParameters c
  have hsource := sixVertexFourByFourAuditedCoordinateSourcePair_valid c
  unfold SixVertexFourByFourAuditedCoordinateSourcePairValid at hsource
  change (sixVertexFourByFourAuditedParamSourceFirst p c.firstSeam).IceRule /\
    (sixVertexFourByFourAuditedParamSourceSecond p c.secondSeam).IceRule /\ _ /\ _
    at hsource
  have hcolumns := sixVertexFourByFourAudited_selectedColumns_constant
    p c.firstSeam c.secondSeam hsource.1 hsource.2.1
      hsource.2.2.1 hsource.2.2.2
  simpa [sixVertexFourByFourAuditedCoordinateSourcePair,
    sixVertexFourByFourAuditedCoordinateTargetPair,
    sixVertexFourByFourAuditedParamTargetFirst,
    sixVertexFourByFourAuditedParamTargetSecond, p] using
    sixVertexFourByFourTogglePair_fineRelated
      (sixVertexFourByFourAuditedParamSourceFirst p c.firstSeam)
      (sixVertexFourByFourAuditedParamSourceSecond p c.secondSeam)
      (sixVertexFourByFourAuditedRepairColumns
        c.firstSeam c.secondSeam).1
      (sixVertexFourByFourAuditedRepairColumns
        c.firstSeam c.secondSeam).2
      hcolumns.1 hcolumns.2

theorem sixVertexFourByFourRowOfMask_injective_of_lt
    {a b : Nat} (ha : a < 16) (hb : b < 16)
    (hrow : sixVertexFourByFourRowOfMask a =
      sixVertexFourByFourRowOfMask b) :
    a = b := by
  have hbits := congrArg Nat.ofBits hrow
  have haBits : Nat.ofBits (sixVertexFourByFourRowOfMask a) = a := by
    simpa [sixVertexFourByFourRowOfMask, Nat.mod_eq_of_lt ha] using
      (Nat.ofBits_testBit a 4)
  have hbBits : Nat.ofBits (sixVertexFourByFourRowOfMask b) = b := by
    simpa [sixVertexFourByFourRowOfMask, Nat.mod_eq_of_lt hb] using
      (Nat.ofBits_testBit b 4)
  exact haBits.symm.trans (hbits.trans hbBits)

theorem sixVertexFourByFourAuditedRowZero_lt (p : Fin 16) :
    (sixVertexFourByFourAuditedRowZero p).1 < 16 /\
      (sixVertexFourByFourAuditedRowZero p).2 < 16 := by
  fin_cases p <;> decide

theorem sixVertexFourByFourAuditedRowMiddle_lt (p : Fin 16) :
    (sixVertexFourByFourAuditedRowMiddle p).1 < 16 /\
      (sixVertexFourByFourAuditedRowMiddle p).2 < 16 := by
  fin_cases p <;> decide

theorem sixVertexFourByFourAuditedRowLast_lt (p : Fin 4) :
    (sixVertexFourByFourAuditedRowLast p).1 < 16 /\
      (sixVertexFourByFourAuditedRowLast p).2 < 16 := by
  fin_cases p <;> decide

theorem sixVertexFourByFourAuditedRowZero_injective :
    Function.Injective sixVertexFourByFourAuditedRowZero := by
  intro a b
  fin_cases a <;> fin_cases b <;>
    simp_all [sixVertexFourByFourAuditedRowZero]

theorem sixVertexFourByFourAuditedRowMiddle_injective :
    Function.Injective sixVertexFourByFourAuditedRowMiddle := by
  intro a b
  fin_cases a <;> fin_cases b <;>
    simp_all [sixVertexFourByFourAuditedRowMiddle]

theorem sixVertexFourByFourAuditedRowLast_injective :
    Function.Injective sixVertexFourByFourAuditedRowLast := by
  intro a b
  fin_cases a <;> fin_cases b <;>
    simp_all [sixVertexFourByFourAuditedRowLast]

theorem sixVertexFourByFourAuditedCoordinateRowZero_injective :
    Function.Injective (fun s : Fin 4 × Fin 4 =>
      sixVertexFourByFourAuditedCoordinateRowZero s.1 s.2) := by
  rintro ⟨first, second⟩ ⟨first', second'⟩
  fin_cases first <;> fin_cases second <;>
    fin_cases first' <;> fin_cases second' <;>
    simp_all [sixVertexFourByFourAuditedCoordinateRowZero]

set_option maxHeartbeats 2000000 in

theorem sixVertexFourByFourAuditedMiddlePair_injective
    (firstSeam secondSeam : Fin 4) :
    Function.Injective
      (sixVertexFourByFourAuditedMiddlePair firstSeam secondSeam) := by
  intro a b
  fin_cases firstSeam <;> fin_cases secondSeam <;>
    fin_cases a <;> fin_cases b <;>
    simp_all [sixVertexFourByFourAuditedMiddlePair,
      sixVertexFourByFourAuditedMiddleA,
      sixVertexFourByFourAuditedMiddleB,
      sixVertexFourByFourAuditedMiddleBNext,
      sixVertexFourByFourAuditedMiddleC]

def sixVertexFourByFourAuditedCoordinateHorizontalRows
    (c : SixVertexFourByFourAuditedCoordinates) :
    (Fin 4 -> SixVertexRow 4) × (Fin 4 -> SixVertexRow 4) :=
  let p := sixVertexFourByFourAuditedCoordinateParameters c
  (sixVertexFourByFourAuditedParamHorizontalRowsFirst p,
    sixVertexFourByFourAuditedParamHorizontalRowsSecond p)

theorem sixVertexFourByFourAuditedCoordinateHorizontalRows_injective :
    Function.Injective
      sixVertexFourByFourAuditedCoordinateHorizontalRows := by
  rintro ⟨firstSeam, secondSeam, middle, last⟩
    ⟨firstSeam', secondSeam', middle', last'⟩ hrows
  have hfirst := congrArg Prod.fst hrows
  have hsecond := congrArg Prod.snd hrows
  let p := sixVertexFourByFourAuditedCoordinateParameters
    ⟨firstSeam, secondSeam, middle, last⟩
  let p' := sixVertexFourByFourAuditedCoordinateParameters
    ⟨firstSeam', secondSeam', middle', last'⟩
  have hfirstZero : sixVertexFourByFourRowOfMask
      (sixVertexFourByFourAuditedRowZero p.1).1 =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourAuditedRowZero p'.1).1 := by
    simpa [sixVertexFourByFourAuditedCoordinateHorizontalRows,
      sixVertexFourByFourAuditedParamHorizontalRowsFirst, p, p'] using
      congrFun hfirst (0 : Fin 4)
  have hsecondZero : sixVertexFourByFourRowOfMask
      (sixVertexFourByFourAuditedRowZero p.1).2 =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourAuditedRowZero p'.1).2 := by
    simpa [sixVertexFourByFourAuditedCoordinateHorizontalRows,
      sixVertexFourByFourAuditedParamHorizontalRowsSecond, p, p'] using
      congrFun hsecond (0 : Fin 4)
  have hzero : p.1 = p'.1 :=
    sixVertexFourByFourAuditedRowZero_injective (Prod.ext
      (sixVertexFourByFourRowOfMask_injective_of_lt
        (sixVertexFourByFourAuditedRowZero_lt p.1).1
        (sixVertexFourByFourAuditedRowZero_lt p'.1).1 hfirstZero)
      (sixVertexFourByFourRowOfMask_injective_of_lt
        (sixVertexFourByFourAuditedRowZero_lt p.1).2
        (sixVertexFourByFourAuditedRowZero_lt p'.1).2 hsecondZero))
  have hseams : (firstSeam, secondSeam) = (firstSeam', secondSeam') :=
    sixVertexFourByFourAuditedCoordinateRowZero_injective hzero
  cases hseams
  have hfirstOne : sixVertexFourByFourRowOfMask
      (sixVertexFourByFourAuditedRowMiddle p.2.1).1 =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourAuditedRowMiddle p'.2.1).1 := by
    simpa [sixVertexFourByFourAuditedCoordinateHorizontalRows,
      sixVertexFourByFourAuditedParamHorizontalRowsFirst, p, p'] using
      congrFun hfirst (1 : Fin 4)
  have hsecondOne : sixVertexFourByFourRowOfMask
      (sixVertexFourByFourAuditedRowMiddle p.2.1).2 =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourAuditedRowMiddle p'.2.1).2 := by
    simpa [sixVertexFourByFourAuditedCoordinateHorizontalRows,
      sixVertexFourByFourAuditedParamHorizontalRowsSecond, p, p'] using
      congrFun hsecond (1 : Fin 4)
  have hone : p.2.1 = p'.2.1 :=
    sixVertexFourByFourAuditedRowMiddle_injective (Prod.ext
      (sixVertexFourByFourRowOfMask_injective_of_lt
        (sixVertexFourByFourAuditedRowMiddle_lt p.2.1).1
        (sixVertexFourByFourAuditedRowMiddle_lt p'.2.1).1 hfirstOne)
      (sixVertexFourByFourRowOfMask_injective_of_lt
        (sixVertexFourByFourAuditedRowMiddle_lt p.2.1).2
        (sixVertexFourByFourAuditedRowMiddle_lt p'.2.1).2 hsecondOne))
  have hfirstTwo : sixVertexFourByFourRowOfMask
      (sixVertexFourByFourAuditedRowMiddle p.2.2.1).1 =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourAuditedRowMiddle p'.2.2.1).1 := by
    simpa [sixVertexFourByFourAuditedCoordinateHorizontalRows,
      sixVertexFourByFourAuditedParamHorizontalRowsFirst, p, p'] using
      congrFun hfirst (2 : Fin 4)
  have hsecondTwo : sixVertexFourByFourRowOfMask
      (sixVertexFourByFourAuditedRowMiddle p.2.2.1).2 =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourAuditedRowMiddle p'.2.2.1).2 := by
    simpa [sixVertexFourByFourAuditedCoordinateHorizontalRows,
      sixVertexFourByFourAuditedParamHorizontalRowsSecond, p, p'] using
      congrFun hsecond (2 : Fin 4)
  have htwo : p.2.2.1 = p'.2.2.1 :=
    sixVertexFourByFourAuditedRowMiddle_injective (Prod.ext
      (sixVertexFourByFourRowOfMask_injective_of_lt
        (sixVertexFourByFourAuditedRowMiddle_lt p.2.2.1).1
        (sixVertexFourByFourAuditedRowMiddle_lt p'.2.2.1).1 hfirstTwo)
      (sixVertexFourByFourRowOfMask_injective_of_lt
        (sixVertexFourByFourAuditedRowMiddle_lt p.2.2.1).2
        (sixVertexFourByFourAuditedRowMiddle_lt p'.2.2.1).2 hsecondTwo))
  have hmiddlePair :
      sixVertexFourByFourAuditedMiddlePair firstSeam secondSeam middle =
        sixVertexFourByFourAuditedMiddlePair firstSeam secondSeam middle' :=
    Prod.ext hone htwo
  have hmiddle := sixVertexFourByFourAuditedMiddlePair_injective
    firstSeam secondSeam hmiddlePair
  subst middle'
  have hfirstThree : sixVertexFourByFourRowOfMask
      (sixVertexFourByFourAuditedRowLast p.2.2.2).1 =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourAuditedRowLast p'.2.2.2).1 := by
    simpa [sixVertexFourByFourAuditedCoordinateHorizontalRows,
      sixVertexFourByFourAuditedParamHorizontalRowsFirst, p, p'] using
      congrFun hfirst (3 : Fin 4)
  have hsecondThree : sixVertexFourByFourRowOfMask
      (sixVertexFourByFourAuditedRowLast p.2.2.2).2 =
      sixVertexFourByFourRowOfMask
        (sixVertexFourByFourAuditedRowLast p'.2.2.2).2 := by
    simpa [sixVertexFourByFourAuditedCoordinateHorizontalRows,
      sixVertexFourByFourAuditedParamHorizontalRowsSecond, p, p'] using
      congrFun hsecond (3 : Fin 4)
  have hlast : p.2.2.2 = p'.2.2.2 :=
    sixVertexFourByFourAuditedRowLast_injective (Prod.ext
      (sixVertexFourByFourRowOfMask_injective_of_lt
        (sixVertexFourByFourAuditedRowLast_lt p.2.2.2).1
        (sixVertexFourByFourAuditedRowLast_lt p'.2.2.2).1 hfirstThree)
      (sixVertexFourByFourRowOfMask_injective_of_lt
        (sixVertexFourByFourAuditedRowLast_lt p.2.2.2).2
        (sixVertexFourByFourAuditedRowLast_lt p'.2.2.2).2 hsecondThree))
  change last = last' at hlast
  subst last'
  rfl

theorem sixVertexFourByFourAuditedCoordinateTargetPair_injective :
    Function.Injective
      sixVertexFourByFourAuditedCoordinateTargetPair := by
  intro c d htarget
  apply sixVertexFourByFourAuditedCoordinateHorizontalRows_injective
  apply Prod.ext
  · funext y x
    have hhorizontal := congrFun
      (congrArg (fun pair => pair.1.horizontal) htarget) (x, y)
    simpa [sixVertexFourByFourAuditedCoordinateHorizontalRows,
      sixVertexFourByFourAuditedCoordinateTargetPair,
      sixVertexFourByFourAuditedParamTargetFirst,
      sixVertexFourByFourToggleVerticalColumn,
      sixVertexFourByFourAuditedParamSourceFirst] using hhorizontal
  · funext y x
    have hhorizontal := congrFun
      (congrArg (fun pair => pair.2.horizontal) htarget) (x, y)
    simpa [sixVertexFourByFourAuditedCoordinateHorizontalRows,
      sixVertexFourByFourAuditedCoordinateTargetPair,
      sixVertexFourByFourAuditedParamTargetSecond,
      sixVertexFourByFourToggleVerticalColumn,
      sixVertexFourByFourAuditedParamSourceSecond] using hhorizontal

theorem sixVertexFourByFourAuditedCoordinateSourcePair_injective :
    Function.Injective
      sixVertexFourByFourAuditedCoordinateSourcePair := by
  intro c d hsource
  apply sixVertexFourByFourAuditedCoordinateHorizontalRows_injective
  apply Prod.ext
  · funext y x
    have hhorizontal := congrFun
      (congrArg (fun pair => pair.1.horizontal) hsource) (x, y)
    simpa [sixVertexFourByFourAuditedCoordinateHorizontalRows,
      sixVertexFourByFourAuditedCoordinateSourcePair,
      sixVertexFourByFourAuditedParamSourceFirst] using hhorizontal
  · funext y x
    have hhorizontal := congrFun
      (congrArg (fun pair => pair.2.horizontal) hsource) (x, y)
    simpa [sixVertexFourByFourAuditedCoordinateHorizontalRows,
      sixVertexFourByFourAuditedCoordinateSourcePair,
      sixVertexFourByFourAuditedParamSourceSecond] using hhorizontal

theorem sixVertexFourByFourAuditedCoordinate_matching :
    Function.Injective sixVertexFourByFourAuditedCoordinateSourcePair /\
      Function.Injective sixVertexFourByFourAuditedCoordinateTargetPair /\
      forall c,
        SixVertexFourByFourAuditedCoordinateSourcePairValid c /\
          SixVertexFourByFourAuditedCoordinateTargetPairValid c /\
          sixVertexPairAtMostTwoCycleFineRelated
            (sixVertexFourByFourAuditedCoordinateSourcePair c)
            (sixVertexFourByFourAuditedCoordinateTargetPair c) := by
  constructor
  · exact sixVertexFourByFourAuditedCoordinateSourcePair_injective
  constructor
  · exact sixVertexFourByFourAuditedCoordinateTargetPair_injective
  · intro c
    constructor
    · exact sixVertexFourByFourAuditedCoordinateSourcePair_valid c
    constructor
    · exact sixVertexFourByFourAuditedCoordinateTargetPair_valid c
    · exact sixVertexFourByFourAuditedCoordinate_fineRelated c

theorem sixVertexFourByFourAuditedCoordinateParameters_injective :
    Function.Injective
      sixVertexFourByFourAuditedCoordinateParameters := by
  intro c d hparameters
  apply sixVertexFourByFourAuditedCoordinateHorizontalRows_injective
  simp only [sixVertexFourByFourAuditedCoordinateHorizontalRows]
  rw [hparameters]

def sixVertexFourByFourAuditedCoordinateParameterImage :
    Finset SixVertexFourByFourAuditedHorizontalParameters :=
  Finset.univ.image sixVertexFourByFourAuditedCoordinateParameters




def sixVertexFourByFourAuditedCoordinateParameterComplement :
    Finset SixVertexFourByFourAuditedHorizontalParameters :=
  Finset.univ \ sixVertexFourByFourAuditedCoordinateParameterImage

set_option maxRecDepth 100000 in
theorem sixVertexFourByFourAuditedCoordinates_card :
    Fintype.card SixVertexFourByFourAuditedCoordinates = 512 := by
  decide

set_option maxRecDepth 100000 in
theorem sixVertexFourByFourAuditedHorizontalParameters_card :
    Fintype.card SixVertexFourByFourAuditedHorizontalParameters = 16384 := by
  decide

theorem sixVertexFourByFourAuditedCoordinateParameterImage_card :
    sixVertexFourByFourAuditedCoordinateParameterImage.card = 512 := by
  rw [sixVertexFourByFourAuditedCoordinateParameterImage,
    Finset.card_image_iff.mpr
      sixVertexFourByFourAuditedCoordinateParameters_injective.injOn]
  exact sixVertexFourByFourAuditedCoordinates_card

theorem sixVertexFourByFourAuditedCoordinateParameterComplement_card :
    sixVertexFourByFourAuditedCoordinateParameterComplement.card = 15872 := by
  rw [sixVertexFourByFourAuditedCoordinateParameterComplement,
    Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ,
    sixVertexFourByFourAuditedCoordinateParameterImage_card,
    sixVertexFourByFourAuditedHorizontalParameters_card]

end

end StatMech.FrontierD
