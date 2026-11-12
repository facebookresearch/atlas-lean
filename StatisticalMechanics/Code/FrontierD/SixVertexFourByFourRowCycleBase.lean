/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Code.FrontierD.SixVertexConfigurationPhysicalRowCycle

namespace StatMech.FrontierD

noncomputable section

local instance svHorizontalIceDecidable
    {N : Nat} (hN : 0 < N) (x y horizontal : SixVertexRow N) :
    Decidable (svHorizontalIce hN x y horizontal) :=
  inferInstanceAs (Decidable (∀ i,
    svHorizontalIncomingCount hN x y horizontal i = 2))

local instance computableNatDecidableEq : DecidableEq Nat := Nat.decEq

def sixVertexFourByFourTorus : EvenTorus where
  width := 4
  height := 4
  width_pos := by norm_num
  height_pos := by norm_num
  width_even := by norm_num
  height_even := by norm_num

def sixVertexFourByFourSectorZero : Fin 5 := ⟨0, by norm_num⟩
def sixVertexFourByFourSectorOne : Fin 5 := ⟨1, by norm_num⟩
def sixVertexFourByFourSectorTwo : Fin 5 := ⟨2, by norm_num⟩
def sixVertexFourByFourSectorThree : Fin 5 := ⟨3, by norm_num⟩

def piFinFourEquiv (A : Type*) : (Fin 4 → A) ≃ A × A × A × A where
  toFun f := (f 0, f 1, f 2, f 3)
  invFun rows := ![rows.1, rows.2.1, rows.2.2.1, rows.2.2.2]
  left_inv f := by
    funext i
    fin_cases i <;> rfl
  right_inv rows := by
    rcases rows with ⟨row0, row1, row2, row3⟩
    rfl

def sixVertexHorizontalTransitionCountExecutable
    {T : EvenTorus} (previous current : SixVertexRow T.width) : Nat :=
  ((Finset.univ : Finset (SixVertexRow T.width)).filter fun horizontal =>
    svHorizontalIce T.width_pos
      previous current horizontal).card

def sixVertexHorizontalTransitionWitnessCountExecutable
    {T : EvenTorus} (vertical : Fin T.height → SixVertexRow T.width)
    (j : Fin T.height) : Nat :=
  sixVertexHorizontalTransitionCountExecutable
    (T := T) (vertical (SixVertexArrows.cyclicPred T.height_pos j))
      (vertical j)

def sixVertexFourRowOfIndex (index : Fin 16) : SixVertexRow 4 := fun i =>
  Nat.testBit index.val i.val

set_option maxRecDepth 100000 in
theorem sixVertexFourRowOfIndex_bijective :
    Function.Bijective sixVertexFourRowOfIndex := by
  decide +revert

def sixVertexFourRowIndexEquiv : Fin 16 ≃ SixVertexRow 4 :=
  Equiv.ofBijective sixVertexFourRowOfIndex
    sixVertexFourRowOfIndex_bijective

@[simp] theorem sixVertexFourRowIndexEquiv_apply (index : Fin 16) :
    sixVertexFourRowIndexEquiv index = sixVertexFourRowOfIndex index := rfl

set_option maxRecDepth 100000 in
def sixVertexFourHorizontalTransitionCountTable : Fin 256 → Nat := ![
  2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 2, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
  0, 1, 2, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 2, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0,
  0, 1, 1, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 1, 0, 2, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0,
  0, 0, 0, 1, 0, 1, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 1, 1, 0,
  0, 1, 1, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 1, 0, 1, 0, 0, 0, 2, 1, 0, 1, 0, 0, 0,
  0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 2, 0, 1, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 1, 0,
  0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 2, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 2, 1, 0,
  0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 2, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2
]

def sixVertexFourHorizontalTransitionCount
    (previous current : Fin 16) : Nat :=
  sixVertexFourHorizontalTransitionCountTable
    (finProdFinEquiv (previous, current))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem sixVertexFourHorizontalTransitionCount_certificate :
    ∀ previous current : Fin 16,
      sixVertexHorizontalTransitionCountExecutable
          (T := sixVertexFourByFourTorus)
          (sixVertexFourRowOfIndex previous)
          (sixVertexFourRowOfIndex current) =
        sixVertexFourHorizontalTransitionCount previous current := by
  decide +revert

def sixVertexMarkedSectorRowCycleGradeCountExecutable
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (totalC : Nat) : Nat :=
  ∑ vertical : Fin T.height → SixVertexRow T.width,
    if sixVertexUpCount (vertical (svFinLast T.height_pos)) = sector.val then
      if sixVertexVerticalRowsTotalC vertical = totalC then
        ∏ j, sixVertexHorizontalTransitionWitnessCountExecutable vertical j
      else 0
    else 0

def sixVertexFourByFourRowCycleGradeCountExecutable
    (sector : Fin 5) (totalC : Nat) : Nat :=
  ∑ row0 : SixVertexRow 4,
    ∑ row1 : SixVertexRow 4,
      ∑ row2 : SixVertexRow 4,
        ∑ row3 : SixVertexRow 4,
          let vertical : Fin 4 → SixVertexRow 4 := ![row0, row1, row2, row3]
          if sixVertexUpCount
              (vertical (svFinLast sixVertexFourByFourTorus.height_pos)) =
              sector.val then
            if sixVertexVerticalRowsTotalC
                (T := sixVertexFourByFourTorus) vertical = totalC then
              ∏ j,
                sixVertexHorizontalTransitionWitnessCountExecutable
                  (T := sixVertexFourByFourTorus) vertical j
            else 0
          else 0

def sixVertexFourByFourTupleGradeCountExecutable
    (sector : Fin 5) (totalC : Nat) : Nat :=
  ∑ rows : SixVertexRow 4 × SixVertexRow 4 ×
      SixVertexRow 4 × SixVertexRow 4,
    let vertical := (piFinFourEquiv (SixVertexRow 4)).symm rows
    if sixVertexUpCount
        (vertical (svFinLast sixVertexFourByFourTorus.height_pos)) =
        sector.val then
      if sixVertexVerticalRowsTotalC
          (T := sixVertexFourByFourTorus) vertical = totalC then
        ∏ j, sixVertexHorizontalTransitionWitnessCountExecutable
          (T := sixVertexFourByFourTorus) vertical j
      else 0
    else 0

theorem sixVertexFourByFourGradeCountExecutable_eq_tuple
    (sector : Fin 5) (totalC : Nat) :
    sixVertexMarkedSectorRowCycleGradeCountExecutable
        sixVertexFourByFourTorus sector totalC =
      sixVertexFourByFourTupleGradeCountExecutable sector totalC := by
  unfold sixVertexMarkedSectorRowCycleGradeCountExecutable
    sixVertexFourByFourTupleGradeCountExecutable
  apply Fintype.sum_equiv (piFinFourEquiv (SixVertexRow 4))
  intro vertical
  simp only [Equiv.symm_apply_apply]
  rfl

theorem sixVertexFourByFourTupleGradeCountExecutable_eq_rows
    (sector : Fin 5) (totalC : Nat) :
    sixVertexFourByFourTupleGradeCountExecutable sector totalC =
      sixVertexFourByFourRowCycleGradeCountExecutable sector totalC := by
  unfold sixVertexFourByFourTupleGradeCountExecutable
    sixVertexFourByFourRowCycleGradeCountExecutable
  simp only [Fintype.sum_prod_type, piFinFourEquiv, Equiv.coe_fn_symm_mk]

theorem sixVertexFourByFourGradeCountExecutable_eq_rows
    (sector : Fin 5) (totalC : Nat) :
    sixVertexMarkedSectorRowCycleGradeCountExecutable
        sixVertexFourByFourTorus sector totalC =
      sixVertexFourByFourRowCycleGradeCountExecutable sector totalC :=
  (sixVertexFourByFourGradeCountExecutable_eq_tuple sector totalC).trans
    (sixVertexFourByFourTupleGradeCountExecutable_eq_rows sector totalC)

def sixVertexFourByFourCachedGradeCount
    (sector : Fin 5) (totalC : Nat) : Nat :=
  ∑ index0 : Fin 16,
    ∑ index1 : Fin 16,
      ∑ index2 : Fin 16,
        ∑ index3 : Fin 16,
          let indices : Fin 4 → Fin 16 := ![index0, index1, index2, index3]
          let vertical : Fin 4 → SixVertexRow 4 := ![
            sixVertexFourRowOfIndex index0,
            sixVertexFourRowOfIndex index1,
            sixVertexFourRowOfIndex index2,
            sixVertexFourRowOfIndex index3]
          if sixVertexUpCount
              (vertical (svFinLast sixVertexFourByFourTorus.height_pos)) =
              sector.val then
            if sixVertexVerticalRowsTotalC
                (T := sixVertexFourByFourTorus) vertical = totalC then
              ∏ j, sixVertexFourHorizontalTransitionCount
                (indices (SixVertexArrows.cyclicPred
                  sixVertexFourByFourTorus.height_pos j))
                (indices j)
            else 0
          else 0

@[simp] theorem sixVertexFourByFourVertical_last
    (row0 row1 row2 row3 : SixVertexRow 4) :
    (![
      row0, row1, row2, row3] : Fin 4 → SixVertexRow 4)
        (svFinLast sixVertexFourByFourTorus.height_pos) = row3 := by
  rfl

theorem sixVertexFourByFourWitnessProduct_certificate
    (index0 index1 index2 index3 : Fin 16) :
    let vertical : Fin 4 → SixVertexRow 4 := ![
      sixVertexFourRowOfIndex index0,
      sixVertexFourRowOfIndex index1,
      sixVertexFourRowOfIndex index2,
      sixVertexFourRowOfIndex index3]
    (∏ j, sixVertexHorizontalTransitionWitnessCountExecutable
        (T := sixVertexFourByFourTorus) vertical j) =
      ∏ j, sixVertexFourHorizontalTransitionCount
        ((![index0, index1, index2, index3] : Fin 4 → Fin 16)
          (SixVertexArrows.cyclicPred
            sixVertexFourByFourTorus.height_pos j))
        ((![index0, index1, index2, index3] : Fin 4 → Fin 16) j) := by
  dsimp only
  apply Finset.prod_congr rfl
  intro j _
  fin_cases j <;>
    simp only [sixVertexHorizontalTransitionWitnessCountExecutable,
      sixVertexFourByFourTorus, SixVertexArrows.cyclicPred,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three] <;>
    apply sixVertexFourHorizontalTransitionCount_certificate

theorem sixVertexFourByFourRowCycleGradeCountExecutable_eq_cached
    (sector : Fin 5) (totalC : Nat) :
    sixVertexFourByFourRowCycleGradeCountExecutable sector totalC =
      sixVertexFourByFourCachedGradeCount sector totalC := by
  symm
  unfold sixVertexFourByFourCachedGradeCount
    sixVertexFourByFourRowCycleGradeCountExecutable
  apply Fintype.sum_equiv sixVertexFourRowIndexEquiv
  intro index0
  apply Fintype.sum_equiv sixVertexFourRowIndexEquiv
  intro index1
  apply Fintype.sum_equiv sixVertexFourRowIndexEquiv
  intro index2
  apply Fintype.sum_equiv sixVertexFourRowIndexEquiv
  intro index3
  simp only [sixVertexFourRowIndexEquiv_apply]
  simp only [sixVertexFourByFourVertical_last]
  apply if_congr Iff.rfl
  · apply if_congr Iff.rfl
    · exact (sixVertexFourByFourWitnessProduct_certificate
        index0 index1 index2 index3).symm
    · rfl
  · rfl

theorem sixVertexFourByFourGradeCountExecutable_eq_cached
    (sector : Fin 5) (totalC : Nat) :
    sixVertexMarkedSectorRowCycleGradeCountExecutable
        sixVertexFourByFourTorus sector totalC =
      sixVertexFourByFourCachedGradeCount sector totalC :=
  (sixVertexFourByFourGradeCountExecutable_eq_rows sector totalC).trans
    (sixVertexFourByFourRowCycleGradeCountExecutable_eq_cached sector totalC)

theorem sixVertexHorizontalTransitionWitnessCountExecutable_eq_card
    {T : EvenTorus} (vertical : Fin T.height → SixVertexRow T.width)
    (j : Fin T.height) :
    sixVertexHorizontalTransitionWitnessCountExecutable vertical j =
      Nat.card (SixVertexHorizontalTransitionWitness vertical j) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

theorem sixVertexMarkedSectorRowCycleGradeCountExecutable_eq
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (totalC : Nat) :
    sixVertexMarkedSectorRowCycleGradeCountExecutable T sector totalC =
      sixVertexMarkedSectorRowCycleGradeCount T sector totalC := by
  let p : (Fin T.height → SixVertexRow T.width) → Prop := fun vertical =>
    sixVertexUpCount (vertical (svFinLast T.height_pos)) = sector.val
  let f : (Fin T.height → SixVertexRow T.width) → Nat := fun vertical =>
    if sixVertexVerticalRowsTotalC vertical = totalC then
      ∏ j, sixVertexHorizontalTransitionWitnessCountExecutable vertical j
    else 0
  unfold sixVertexMarkedSectorRowCycleGradeCountExecutable
    sixVertexMarkedSectorRowCycleGradeCount
  simp only [← Nat.card_eq_fintype_card]
  change
    (∑ vertical : Fin T.height → SixVertexRow T.width,
      if p vertical then f vertical else 0) =
        ∑ vertical : Subtype p,
          if sixVertexVerticalRowsTotalC vertical.1 = totalC then
            ∏ j, Nat.card
              (SixVertexHorizontalTransitionWitness vertical.1 j)
          else 0
  calc
    _ = Finset.sum
        ((Finset.univ : Finset (Fin T.height → SixVertexRow T.width)).filter p)
        f := (Finset.sum_filter p f).symm
    _ = ∑ vertical : Subtype p, f vertical.1 :=
      Finset.sum_subtype
        ((Finset.univ : Finset (Fin T.height → SixVertexRow T.width)).filter p)
        (by intro vertical; simp [p]) f
    _ = _ := by
      apply Finset.sum_congr rfl
      intro vertical _
      by_cases hgrade : sixVertexVerticalRowsTotalC vertical.1 = totalC
      · simp only [f, hgrade, if_true]
        apply Finset.prod_congr rfl
        intro j _
        exact sixVertexHorizontalTransitionWitnessCountExecutable_eq_card
          vertical.1 j
      · simp only [f, hgrade, if_false]

end

end StatMech.FrontierD
