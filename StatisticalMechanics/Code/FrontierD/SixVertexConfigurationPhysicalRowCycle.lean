/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Code.FrontierD.SixVertexConfigurationPhysicalCommonFactor
import Code.FrontierD.SixVertexBalancedTransferBridge
import Code.FrontierD.SixVertexMarkedPairCTypeHall










open Finset

namespace StatMech.FrontierD

noncomputable section

theorem sixVertexIceRule_iff_horizontalRowTransitions
    {T : EvenTorus} (omega : SixVertexArrows T) :
    omega.IceRule ↔
      forall j : Fin T.height,
        svHorizontalIce T.width_pos
          (svTorusVerticalRows T omega
            (SixVertexArrows.cyclicPred T.height_pos j))
          (svTorusVerticalRows T omega j)
          (svTorusHorizontalRows T omega j) := by
  constructor
  · intro hice j i
    simpa [svHorizontalIncomingCount, svTorusVerticalRows,
      svTorusHorizontalRows, SixVertexArrows.incomingCount,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hice (i, j)
  · intro hrows vertex
    rcases vertex with ⟨i, j⟩
    simpa [svHorizontalIncomingCount, svTorusVerticalRows,
      svTorusHorizontalRows, SixVertexArrows.incomingCount,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hrows j i


abbrev SixVertexMarkedSectorRowCycle
    (T : EvenTorus) (sector : Fin (T.width + 1)) :=
  {rows : (Fin T.height → SixVertexRow T.width) ×
      (Fin T.height → SixVertexRow T.width) //
    (forall j,
      svHorizontalIce T.width_pos
        (rows.2 (SixVertexArrows.cyclicPred T.height_pos j))
        (rows.2 j) (rows.1 j)) ∧
      sixVertexUpCount (rows.2 (svFinLast T.height_pos)) = sector.val}

local instance instFintypeMarkedSectorRowCycle
    (T : EvenTorus) (sector : Fin (T.width + 1)) :
    Fintype (SixVertexMarkedSectorRowCycle T sector) :=
  Fintype.ofFinite _



def sixVertexMarkedSectorConfigurationEquivRowCycle
    (T : EvenTorus) (sector : Fin (T.width + 1)) :
    SixVertexMarkedSectorConfiguration T sector ≃
      SixVertexMarkedSectorRowCycle T sector where
  toFun omega :=
    ⟨svTorusRowsEquiv T omega.1,
      (sixVertexIceRule_iff_horizontalRowTransitions omega.1).mp omega.2.1,
      omega.2.2⟩
  invFun rows :=
    ⟨(svTorusRowsEquiv T).symm rows.1,
      (sixVertexIceRule_iff_horizontalRowTransitions
        ((svTorusRowsEquiv T).symm rows.1)).mpr (by
          simpa using rows.2.1),
      by simpa [svTorusVerticalRows] using rows.2.2⟩
  left_inv omega := by
    apply Subtype.ext
    exact (svTorusRowsEquiv T).symm_apply_apply omega.1
  right_inv rows := by
    apply Subtype.ext
    exact (svTorusRowsEquiv T).apply_symm_apply rows.1


def sixVertexMarkedSectorRowCycleTotalC
    {T : EvenTorus} {sector : Fin (T.width + 1)}
    (rows : SixVertexMarkedSectorRowCycle T sector) : Nat :=
  ∑ j, sixVertexRowDistance
    (rows.1.2 (SixVertexArrows.cyclicPred T.height_pos j))
    (rows.1.2 j)

theorem sixVertexArrows_isCType_iff_verticalRow_ne
    {T : EvenTorus} (omega : SixVertexArrows T) (homega : omega.IceRule)
    (i : Fin T.width) (j : Fin T.height) :
    omega.IsCType (i, j) ↔
      svTorusVerticalRows T omega
          (SixVertexArrows.cyclicPred T.height_pos j) i ≠
        svTorusVerticalRows T omega j i := by
  have hrow :=
    (sixVertexIceRule_iff_horizontalRowTransitions omega).mp homega j
  have hc := svHorizontalIsC_iff_ne T.width_pos hrow i
  simpa [SixVertexArrows.IsCType, svHorizontalIsC,
    svTorusHorizontalRows, svTorusVerticalRows] using hc

theorem sixVertexTorusCTypeCount_eq_rowCycleTotalC
    {T : EvenTorus} {sector : Fin (T.width + 1)}
    (omega : SixVertexMarkedSectorConfiguration T sector) :
    sixVertexTorusCTypeCount omega.1 =
      sixVertexMarkedSectorRowCycleTotalC
        (sixVertexMarkedSectorConfigurationEquivRowCycle T sector omega) := by
  classical
  unfold sixVertexTorusCTypeCount sixVertexMarkedSectorRowCycleTotalC
    sixVertexRowDistance
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [if_congr
    (sixVertexArrows_isCType_iff_verticalRow_ne omega.1 omega.2.1 i j)
    rfl rfl]
  rfl


abbrev SixVertexVerticalRowsInSector
    (T : EvenTorus) (sector : Fin (T.width + 1)) :=
  {vertical : Fin T.height → SixVertexRow T.width //
    sixVertexUpCount (vertical (svFinLast T.height_pos)) = sector.val}


abbrev SixVertexHorizontalTransitionWitness
    {T : EvenTorus} (vertical : Fin T.height → SixVertexRow T.width)
    (j : Fin T.height) :=
  {horizontal : SixVertexRow T.width //
    svHorizontalIce T.width_pos
      (vertical (SixVertexArrows.cyclicPred T.height_pos j))
      (vertical j) horizontal}



def sixVertexMarkedSectorRowCycleEquivVerticalTransitions
    (T : EvenTorus) (sector : Fin (T.width + 1)) :
    SixVertexMarkedSectorRowCycle T sector ≃
      Sigma fun vertical : SixVertexVerticalRowsInSector T sector =>
        forall j, SixVertexHorizontalTransitionWitness vertical.1 j where
  toFun rows :=
    ⟨⟨rows.1.2, rows.2.2⟩, fun j => ⟨rows.1.1 j, rows.2.1 j⟩⟩
  invFun data :=
    ⟨(fun j => (data.2 j).1, data.1.1),
      (fun j => (data.2 j).2), data.1.2⟩
  left_inv rows := by
    apply Subtype.ext
    apply Prod.ext <;> funext j <;> rfl
  right_inv data := by
    apply Sigma.ext
    · apply Subtype.ext
      rfl
    · rfl

def sixVertexVerticalRowsTotalC
    {T : EvenTorus} (vertical : Fin T.height → SixVertexRow T.width) : Nat :=
  ∑ j, sixVertexRowDistance
    (vertical (SixVertexArrows.cyclicPred T.height_pos j)) (vertical j)



def sixVertexMarkedSectorRowCycleGradeCount
    (T : EvenTorus) (sector : Fin (T.width + 1)) (totalC : Nat) : Nat :=
  ∑ vertical : SixVertexVerticalRowsInSector T sector,
    if sixVertexVerticalRowsTotalC vertical.1 = totalC then
      ∏ j, Fintype.card
        (SixVertexHorizontalTransitionWitness vertical.1 j)
    else 0

def sigmaSubtypeBaseComm {A : Type*} (B : A → Type*) (p : A → Prop) :
    (Sigma fun a : Subtype p => B a.1) ≃
      Sigma fun a : A => {_b : B a // p a} where
  toFun value := ⟨value.1.1, ⟨value.2, value.1.2⟩⟩
  invFun value := ⟨⟨value.1, value.2.2⟩, value.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

def subtypeSigmaBaseEquiv
    {X A : Type*} (B : A → Type*) (equiv : X ≃ Sigma B)
    (sourcePred : X → Prop) (basePred : A → Prop)
    (hpred : forall value, sourcePred value ↔ basePred (equiv value).1) :
    {value : X // sourcePred value} ≃
      Sigma fun a : A => {_b : B a // basePred a} :=
  (Equiv.subtypeEquiv equiv hpred).trans
    ((Equiv.subtypeSigmaEquiv B basePred).trans
      (sigmaSubtypeBaseComm B basePred))

def sixVertexMarkedSectorRowCycleGradeFiberEquiv
    (T : EvenTorus) (sector : Fin (T.width + 1)) (totalC : Nat) :
    {rows : SixVertexMarkedSectorRowCycle T sector //
      sixVertexMarkedSectorRowCycleTotalC rows = totalC} ≃
      Sigma fun vertical : SixVertexVerticalRowsInSector T sector =>
        {_witness : forall j,
            SixVertexHorizontalTransitionWitness vertical.1 j //
          sixVertexVerticalRowsTotalC vertical.1 = totalC} where
  toFun :=
    ((Equiv.subtypeEquiv
      (sixVertexMarkedSectorRowCycleEquivVerticalTransitions T sector)
      (fun _ => Iff.rfl)).trans
        ((Equiv.subtypeSigmaEquiv
          (fun vertical : SixVertexVerticalRowsInSector T sector =>
            forall j, SixVertexHorizontalTransitionWitness vertical.1 j)
          (fun vertical =>
            sixVertexVerticalRowsTotalC vertical.1 = totalC)).trans
          (sigmaSubtypeBaseComm
            (fun vertical : SixVertexVerticalRowsInSector T sector =>
              forall j, SixVertexHorizontalTransitionWitness vertical.1 j)
            (fun vertical =>
              sixVertexVerticalRowsTotalC vertical.1 = totalC)))).toFun
  invFun :=
    ((Equiv.subtypeEquiv
      (sixVertexMarkedSectorRowCycleEquivVerticalTransitions T sector)
      (fun _ => Iff.rfl)).trans
        ((Equiv.subtypeSigmaEquiv
          (fun vertical : SixVertexVerticalRowsInSector T sector =>
            forall j, SixVertexHorizontalTransitionWitness vertical.1 j)
          (fun vertical =>
            sixVertexVerticalRowsTotalC vertical.1 = totalC)).trans
          (sigmaSubtypeBaseComm
            (fun vertical : SixVertexVerticalRowsInSector T sector =>
              forall j, SixVertexHorizontalTransitionWitness vertical.1 j)
            (fun vertical =>
              sixVertexVerticalRowsTotalC vertical.1 = totalC)))).invFun
  left_inv := ((Equiv.subtypeEquiv
      (sixVertexMarkedSectorRowCycleEquivVerticalTransitions T sector)
      (fun _ => Iff.rfl)).trans
        ((Equiv.subtypeSigmaEquiv
          (fun vertical : SixVertexVerticalRowsInSector T sector =>
            forall j, SixVertexHorizontalTransitionWitness vertical.1 j)
          (fun vertical =>
            sixVertexVerticalRowsTotalC vertical.1 = totalC)).trans
          (sigmaSubtypeBaseComm
            (fun vertical : SixVertexVerticalRowsInSector T sector =>
              forall j, SixVertexHorizontalTransitionWitness vertical.1 j)
            (fun vertical =>
              sixVertexVerticalRowsTotalC vertical.1 = totalC)))).left_inv
  right_inv := ((Equiv.subtypeEquiv
      (sixVertexMarkedSectorRowCycleEquivVerticalTransitions T sector)
      (fun _ => Iff.rfl)).trans
        ((Equiv.subtypeSigmaEquiv
          (fun vertical : SixVertexVerticalRowsInSector T sector =>
            forall j, SixVertexHorizontalTransitionWitness vertical.1 j)
          (fun vertical =>
            sixVertexVerticalRowsTotalC vertical.1 = totalC)).trans
          (sigmaSubtypeBaseComm
            (fun vertical : SixVertexVerticalRowsInSector T sector =>
              forall j, SixVertexHorizontalTransitionWitness vertical.1 j)
            (fun vertical =>
              sixVertexVerticalRowsTotalC vertical.1 = totalC)))).right_inv

theorem card_sixVertexMarkedSectorRowCycleGradeFiber
    (T : EvenTorus) (sector : Fin (T.width + 1)) (totalC : Nat) :
    Fintype.card
        {rows : SixVertexMarkedSectorRowCycle T sector //
          sixVertexMarkedSectorRowCycleTotalC rows = totalC} =
      sixVertexMarkedSectorRowCycleGradeCount T sector totalC := by
  rw [Fintype.card_congr
    (sixVertexMarkedSectorRowCycleGradeFiberEquiv T sector totalC),
    Fintype.card_sigma]
  unfold sixVertexMarkedSectorRowCycleGradeCount
  apply Finset.sum_congr rfl
  intro vertical _
  by_cases hgrade : sixVertexVerticalRowsTotalC vertical.1 = totalC
  · rw [if_pos hgrade]
    simp only [Fintype.card_subtype, hgrade, Finset.filter_true,
      Finset.card_univ, Fintype.card_pi]
  · rw [if_neg hgrade]
    simp only [Fintype.card_subtype, hgrade, Finset.filter_false,
      Finset.card_empty]



def natGradedPairFiberEquivSigma
    {A B : Type*} (gradeA : A → Nat) (gradeB : B → Nat)
    (total : Nat) :
    {pair : A × B // gradeA pair.1 + gradeB pair.2 = total} ≃
      Sigma fun k : Fin (total + 1) =>
        {pair : A × B //
          gradeA pair.1 = k.val ∧
            gradeB pair.2 = total - k.val} where
  toFun pair :=
    ⟨⟨gradeA pair.1.1, by omega⟩,
      ⟨pair.1, rfl, by
        have hgrade := pair.2
        dsimp
        omega⟩⟩
  invFun data := ⟨data.2.1, by
      rw [data.2.2.1, data.2.2.2]
      omega⟩
  left_inv pair := by
    apply Subtype.ext
    rfl
  right_inv data := by
    rcases data with ⟨k, ⟨pair, hleft, hright⟩⟩
    apply Sigma.ext
    · apply Fin.ext
      exact hleft
    · apply (Subtype.heq_iff_coe_eq (fun value => by
          change
            (gradeA value.1 = gradeA pair.1 ∧
                gradeB value.2 = total - gradeA pair.1) ↔
              (gradeA value.1 = k.val ∧
                gradeB value.2 = total - k.val)
          rw [hleft])).2
      rfl

def natGradedPairFiberAtEquivProd
    {A B : Type*} (gradeA : A → Nat) (gradeB : B → Nat)
    (total : Nat) (k : Fin (total + 1)) :
    {pair : A × B //
      gradeA pair.1 = k.val ∧ gradeB pair.2 = total - k.val} ≃
      {a : A // gradeA a = k.val} ×
        {b : B // gradeB b = total - k.val} where
  toFun pair := (⟨pair.1.1, pair.2.1⟩, ⟨pair.1.2, pair.2.2⟩)
  invFun pair := ⟨(pair.1.1, pair.2.1), pair.1.2, pair.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem natCard_natGradedPairFiber
    {A B : Type*} [Finite A] [Finite B]
    (gradeA : A → Nat) (gradeB : B → Nat) (total : Nat) :
    Nat.card {pair : A × B // gradeA pair.1 + gradeB pair.2 = total} =
      ∑ k : Fin (total + 1),
        Nat.card {a : A // gradeA a = k.val} *
          Nat.card {b : B // gradeB b = total - k.val} := by
  rw [Nat.card_congr (natGradedPairFiberEquivSigma gradeA gradeB total),
    Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.card_congr
    (natGradedPairFiberAtEquivProd gradeA gradeB total k), Nat.card_prod]

def sigmaProdSigmaEquiv {A B : Type*} (F : A → Type*) (G : B → Type*) :
    (Sigma F × Sigma G) ≃
      Sigma fun pair : A × B => F pair.1 × G pair.2 where
  toFun value := ⟨(value.1.1, value.2.1), (value.1.2, value.2.2)⟩
  invFun value := (⟨value.1.1, value.2.1⟩, ⟨value.1.2, value.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl

def sixVertexMarkedSectorRowCyclePairEquivVerticalTransitions
    (T : EvenTorus) (left right : Fin (T.width + 1)) :
    (SixVertexMarkedSectorRowCycle T left ×
      SixVertexMarkedSectorRowCycle T right) ≃
      Sigma fun vertical :
          SixVertexVerticalRowsInSector T left ×
            SixVertexVerticalRowsInSector T right =>
        ((forall j,
            SixVertexHorizontalTransitionWitness vertical.1.1 j) ×
          (forall j,
            SixVertexHorizontalTransitionWitness vertical.2.1 j)) :=
  (Equiv.prodCongr
    (sixVertexMarkedSectorRowCycleEquivVerticalTransitions T left)
    (sixVertexMarkedSectorRowCycleEquivVerticalTransitions T right)).trans
      (sigmaProdSigmaEquiv _ _)

def sixVertexMarkedSectorRowCyclePairTotalC
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (pair : SixVertexMarkedSectorRowCycle T left ×
      SixVertexMarkedSectorRowCycle T right) : Nat :=
  sixVertexMarkedSectorRowCycleTotalC pair.1 +
    sixVertexMarkedSectorRowCycleTotalC pair.2

def sixVertexMarkedSectorRowCyclePairGradeCount
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (totalC : Nat) : Nat :=
  ∑ vertical : SixVertexVerticalRowsInSector T left ×
      SixVertexVerticalRowsInSector T right,
    if sixVertexVerticalRowsTotalC vertical.1.1 +
        sixVertexVerticalRowsTotalC vertical.2.1 = totalC then
      (∏ j, Fintype.card
        (SixVertexHorizontalTransitionWitness vertical.1.1 j)) *
      (∏ j, Fintype.card
        (SixVertexHorizontalTransitionWitness vertical.2.1 j))
    else 0

def sixVertexMarkedSectorRowCyclePairGradeFiberEquiv
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (totalC : Nat) :
    {pair : SixVertexMarkedSectorRowCycle T left ×
        SixVertexMarkedSectorRowCycle T right //
      sixVertexMarkedSectorRowCyclePairTotalC pair = totalC} ≃
      Sigma fun vertical :
          SixVertexVerticalRowsInSector T left ×
            SixVertexVerticalRowsInSector T right =>
        {_witness :
            ((forall j,
                SixVertexHorizontalTransitionWitness vertical.1.1 j) ×
              (forall j,
                SixVertexHorizontalTransitionWitness vertical.2.1 j)) //
          sixVertexVerticalRowsTotalC vertical.1.1 +
            sixVertexVerticalRowsTotalC vertical.2.1 = totalC} :=
  subtypeSigmaBaseEquiv _
    (sixVertexMarkedSectorRowCyclePairEquivVerticalTransitions
      T left right)
    (fun pair => sixVertexMarkedSectorRowCyclePairTotalC pair = totalC)
    (fun vertical => sixVertexVerticalRowsTotalC vertical.1.1 +
      sixVertexVerticalRowsTotalC vertical.2.1 = totalC)
    (fun _ => Iff.rfl)

theorem card_sixVertexMarkedSectorRowCyclePairGradeFiber
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (totalC : Nat) :
    Fintype.card
        {pair : SixVertexMarkedSectorRowCycle T left ×
            SixVertexMarkedSectorRowCycle T right //
          sixVertexMarkedSectorRowCyclePairTotalC pair = totalC} =
      sixVertexMarkedSectorRowCyclePairGradeCount T left right totalC := by
  rw [Fintype.card_congr
    (sixVertexMarkedSectorRowCyclePairGradeFiberEquiv
      T left right totalC), Fintype.card_sigma]
  unfold sixVertexMarkedSectorRowCyclePairGradeCount
  apply Finset.sum_congr rfl
  intro vertical _
  by_cases hgrade : sixVertexVerticalRowsTotalC vertical.1.1 +
      sixVertexVerticalRowsTotalC vertical.2.1 = totalC
  · rw [if_pos hgrade]
    simp only [Fintype.card_subtype, hgrade, Finset.filter_true,
      Finset.card_univ, Fintype.card_prod, Fintype.card_pi]
  · rw [if_neg hgrade]
    simp only [Fintype.card_subtype, hgrade, Finset.filter_false,
      Finset.card_empty]



theorem sixVertexMarkedSectorRowCyclePairGradeCount_eq_convolution
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (totalC : Nat) :
    sixVertexMarkedSectorRowCyclePairGradeCount T left right totalC =
      ∑ k : Fin (totalC + 1),
        sixVertexMarkedSectorRowCycleGradeCount T left k.val *
          sixVertexMarkedSectorRowCycleGradeCount
            T right (totalC - k.val) := by
  rw [← card_sixVertexMarkedSectorRowCyclePairGradeFiber]
  simp only [← Nat.card_eq_fintype_card]
  change Nat.card
      {pair : SixVertexMarkedSectorRowCycle T left ×
          SixVertexMarkedSectorRowCycle T right //
        sixVertexMarkedSectorRowCycleTotalC pair.1 +
          sixVertexMarkedSectorRowCycleTotalC pair.2 = totalC} = _
  rw [natCard_natGradedPairFiber]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.card_eq_fintype_card,
    card_sixVertexMarkedSectorRowCycleGradeFiber,
    Nat.card_eq_fintype_card,
    card_sixVertexMarkedSectorRowCycleGradeFiber]

def sixVertexMarkedSectorRowCycleDiagonalGradeCount
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (totalC : Nat) : Nat :=
  ∑ vertical : SixVertexVerticalRowsInSector T sector,
    if 2 * sixVertexVerticalRowsTotalC vertical.1 = totalC then
      ∏ j, Fintype.card
        (SixVertexHorizontalTransitionWitness vertical.1 j)
    else 0

def sixVertexMarkedSectorRowCycleDiagonalGradeFiberEquiv
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (totalC : Nat) :
    {rows : SixVertexMarkedSectorRowCycle T sector //
      2 * sixVertexMarkedSectorRowCycleTotalC rows = totalC} ≃
      Sigma fun vertical : SixVertexVerticalRowsInSector T sector =>
        {_witness : forall j,
            SixVertexHorizontalTransitionWitness vertical.1 j //
          2 * sixVertexVerticalRowsTotalC vertical.1 = totalC} :=
  subtypeSigmaBaseEquiv _
    (sixVertexMarkedSectorRowCycleEquivVerticalTransitions T sector)
    (fun rows => 2 * sixVertexMarkedSectorRowCycleTotalC rows = totalC)
    (fun vertical => 2 * sixVertexVerticalRowsTotalC vertical.1 = totalC)
    (fun _ => Iff.rfl)

theorem card_sixVertexMarkedSectorRowCycleDiagonalGradeFiber
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (totalC : Nat) :
    Fintype.card
        {rows : SixVertexMarkedSectorRowCycle T sector //
          2 * sixVertexMarkedSectorRowCycleTotalC rows = totalC} =
      sixVertexMarkedSectorRowCycleDiagonalGradeCount T sector totalC := by
  rw [Fintype.card_congr
    (sixVertexMarkedSectorRowCycleDiagonalGradeFiberEquiv
      T sector totalC), Fintype.card_sigma]
  unfold sixVertexMarkedSectorRowCycleDiagonalGradeCount
  apply Finset.sum_congr rfl
  intro vertical _
  by_cases hgrade : 2 * sixVertexVerticalRowsTotalC vertical.1 = totalC
  · rw [if_pos hgrade]
    simp only [Fintype.card_subtype, hgrade, Finset.filter_true,
      Finset.card_univ, Fintype.card_pi]
  · rw [if_neg hgrade]
    simp only [Fintype.card_subtype, hgrade, Finset.filter_false,
      Finset.card_empty]

abbrev SixVertexPhysicalRowCycleSource
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) :=
  SixVertexMarkedSectorRowCycle T ⟨middle.val - 1, by omega⟩ ×
    SixVertexMarkedSectorRowCycle T ⟨middle.val + 1, by omega⟩

abbrev SixVertexPhysicalRowCycleTarget
    (T : EvenTorus) (middle : Fin (T.width + 1)) :=
  SixVertexMarkedSectorRowCycle T middle ×
    SixVertexMarkedSectorRowCycle T middle

def sixVertexPhysicalRowCyclePairTotalC
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (pair : SixVertexMarkedSectorRowCycle T left ×
      SixVertexMarkedSectorRowCycle T right) : Nat :=
  sixVertexMarkedSectorRowCyclePairTotalC pair


structure SixVertexPhysicalRowCyclePairedBranchEmbeddings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) where
  branch : Bool →
    SixVertexPhysicalRowCycleSource T middle hmiddle_pos hmiddle_lt ↪
      SixVertexPhysicalRowCycleTarget T middle
  distinct : forall source, branch false source ≠ branch true source
  aggregateTotalC : forall source,
    2 * sixVertexPhysicalRowCyclePairTotalC source <=
      sixVertexPhysicalRowCyclePairTotalC (branch false source) +
        sixVertexPhysicalRowCyclePairTotalC (branch true source)

def sixVertexPhysicalSourceEquivRowCycles
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width} :
    SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt ≃
      SixVertexPhysicalRowCycleSource T middle hmiddle_pos hmiddle_lt :=
  Equiv.prodCongr
    (sixVertexMarkedSectorConfigurationEquivRowCycle T
      ⟨middle.val - 1, by omega⟩)
    (sixVertexMarkedSectorConfigurationEquivRowCycle T
      ⟨middle.val + 1, by omega⟩)

def sixVertexPhysicalTargetEquivRowCycles
    {T : EvenTorus} {middle : Fin (T.width + 1)} :
    SixVertexConfigurationPhysicalTarget T middle ≃
      SixVertexPhysicalRowCycleTarget T middle :=
  Equiv.prodCongr
    (sixVertexMarkedSectorConfigurationEquivRowCycle T middle)
    (sixVertexMarkedSectorConfigurationEquivRowCycle T middle)

theorem sixVertexPhysicalSourceEquivRowCycles_totalC
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt) :
    sixVertexPhysicalRowCyclePairTotalC
        (sixVertexPhysicalSourceEquivRowCycles source) =
      sixVertexConfigurationPairTotalCPhysical source := by
  simp [sixVertexPhysicalRowCyclePairTotalC,
    sixVertexMarkedSectorRowCyclePairTotalC,
    sixVertexConfigurationPairTotalCPhysical,
    sixVertexPhysicalSourceEquivRowCycles,
    sixVertexTorusCTypeCount_eq_rowCycleTotalC]

theorem sixVertexPhysicalTargetEquivRowCycles_totalC
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    (target : SixVertexConfigurationPhysicalTarget T middle) :
    sixVertexPhysicalRowCyclePairTotalC
        (sixVertexPhysicalTargetEquivRowCycles target) =
      sixVertexConfigurationPairTotalCPhysical target := by
  simp [sixVertexPhysicalRowCyclePairTotalC,
    sixVertexMarkedSectorRowCyclePairTotalC,
    sixVertexConfigurationPairTotalCPhysical,
    sixVertexPhysicalTargetEquivRowCycles,
    sixVertexTorusCTypeCount_eq_rowCycleTotalC]

@[simp] theorem sixVertexPhysicalTargetEquivRowCycles_symm_totalC
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    (target : SixVertexPhysicalRowCycleTarget T middle) :
    sixVertexConfigurationPairTotalCPhysical
        (sixVertexPhysicalTargetEquivRowCycles.symm target) =
      sixVertexPhysicalRowCyclePairTotalC target := by
  have h := sixVertexPhysicalTargetEquivRowCycles_totalC
    (sixVertexPhysicalTargetEquivRowCycles.symm target)
  simpa using h.symm


def SixVertexPhysicalRowCyclePairedBranchEmbeddings.toPhysical
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (rowEmbeddings : SixVertexPhysicalRowCyclePairedBranchEmbeddings
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexConfigurationPhysicalPairedBranchEmbeddings
      T middle hmiddle_pos hmiddle_lt where
  branch choice :=
    sixVertexPhysicalSourceEquivRowCycles.toEmbedding |>.trans
      (rowEmbeddings.branch choice) |>.trans
      sixVertexPhysicalTargetEquivRowCycles.symm.toEmbedding
  distinct source := by
    intro heq
    apply rowEmbeddings.distinct (sixVertexPhysicalSourceEquivRowCycles source)
    apply sixVertexPhysicalTargetEquivRowCycles.symm.injective
    exact heq
  aggregateTotalC source := by
    have h := rowEmbeddings.aggregateTotalC
      (sixVertexPhysicalSourceEquivRowCycles
        (hmiddle_pos := hmiddle_pos) (hmiddle_lt := hmiddle_lt) source)
    rw [sixVertexPhysicalSourceEquivRowCycles_totalC] at h
    simpa using h



abbrev SixVertexPhysicalRowCycleOffDiagonalTarget
    (T : EvenTorus) (middle : Fin (T.width + 1)) :=
  {target : SixVertexPhysicalRowCycleTarget T middle //
    target.1 ≠ target.2}

def sixVertexPhysicalRowCycleOffDiagonalForget
    {T : EvenTorus} {middle : Fin (T.width + 1)} :
    SixVertexPhysicalRowCycleOffDiagonalTarget T middle ↪
      SixVertexPhysicalRowCycleTarget T middle where
  toFun target := target.1
  inj' := Subtype.val_injective

def sixVertexPhysicalRowCycleOffDiagonalSwap
    {T : EvenTorus} {middle : Fin (T.width + 1)} :
    SixVertexPhysicalRowCycleOffDiagonalTarget T middle ↪
      SixVertexPhysicalRowCycleTarget T middle where
  toFun target := (target.1.2, target.1.1)
  inj' := by
    intro first second heq
    apply Subtype.ext
    exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)

theorem sixVertexPhysicalRowCycleOffDiagonal_branches_distinct
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    (target : SixVertexPhysicalRowCycleOffDiagonalTarget T middle) :
    sixVertexPhysicalRowCycleOffDiagonalForget target ≠
      sixVertexPhysicalRowCycleOffDiagonalSwap target := by
  intro heq
  exact target.2 (congrArg Prod.fst heq)

def sixVertexPhysicalRowCycleOffDiagonalGradeEquiv
    {T : EvenTorus} {middle : Fin (T.width + 1)} (totalC : Nat) :
    {target : SixVertexPhysicalRowCycleOffDiagonalTarget T middle //
      sixVertexPhysicalRowCyclePairTotalC target.1 = totalC} ≃
      {target :
          {pair : SixVertexPhysicalRowCycleTarget T middle //
            sixVertexPhysicalRowCyclePairTotalC pair = totalC} //
        target.1.1 ≠ target.1.2} where
  toFun target := ⟨⟨target.1.1, target.2⟩, target.1.2⟩
  invFun target := ⟨⟨target.1.1, target.2⟩, target.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def sixVertexPhysicalRowCycleDiagonalGradeEquiv
    {T : EvenTorus} {middle : Fin (T.width + 1)} (totalC : Nat) :
    {target :
        {pair : SixVertexPhysicalRowCycleTarget T middle //
          sixVertexPhysicalRowCyclePairTotalC pair = totalC} //
      target.1.1 = target.1.2} ≃
      {rows : SixVertexMarkedSectorRowCycle T middle //
        2 * sixVertexMarkedSectorRowCycleTotalC rows = totalC} where
  toFun target := ⟨target.1.1.1, by
    have hgrade := target.1.2
    change sixVertexMarkedSectorRowCycleTotalC target.1.1.1 +
      sixVertexMarkedSectorRowCycleTotalC target.1.1.2 = totalC at hgrade
    rw [← target.2] at hgrade
    simpa [two_mul] using hgrade⟩
  invFun rows := ⟨⟨(rows.1, rows.1), by
    simpa [sixVertexPhysicalRowCyclePairTotalC,
      sixVertexMarkedSectorRowCyclePairTotalC, two_mul] using rows.2⟩, rfl⟩
  left_inv target := by
    rcases target with ⟨⟨⟨first, second⟩, hgrade⟩, heq⟩
    change first = second at heq
    subst second
    rfl
  right_inv rows := by
    apply Subtype.ext
    rfl

theorem card_sixVertexPhysicalRowCycleOffDiagonalGradeFiber
    (T : EvenTorus) (middle : Fin (T.width + 1)) (totalC : Nat) :
    Fintype.card
        {target : SixVertexPhysicalRowCycleOffDiagonalTarget T middle //
          sixVertexPhysicalRowCyclePairTotalC target.1 = totalC} =
      sixVertexMarkedSectorRowCyclePairGradeCount
          T middle middle totalC -
        sixVertexMarkedSectorRowCycleDiagonalGradeCount
          T middle totalC := by
  rw [Fintype.card_congr
    (sixVertexPhysicalRowCycleOffDiagonalGradeEquiv totalC)]
  rw [Fintype.card_subtype_compl]
  have hpair :
      Nat.card
          {pair : SixVertexPhysicalRowCycleTarget T middle //
            sixVertexPhysicalRowCyclePairTotalC pair = totalC} =
        sixVertexMarkedSectorRowCyclePairGradeCount
          T middle middle totalC := by
    change Nat.card
        {pair : SixVertexMarkedSectorRowCycle T middle ×
            SixVertexMarkedSectorRowCycle T middle //
          sixVertexMarkedSectorRowCyclePairTotalC pair = totalC} = _
    rw [Nat.card_eq_fintype_card]
    exact card_sixVertexMarkedSectorRowCyclePairGradeFiber
      T middle middle totalC
  have hdiagonal :
      Nat.card
          {target :
              {pair : SixVertexPhysicalRowCycleTarget T middle //
                sixVertexPhysicalRowCyclePairTotalC pair = totalC} //
            target.1.1 = target.1.2} =
        sixVertexMarkedSectorRowCycleDiagonalGradeCount
          T middle totalC := by
    rw [Nat.card_congr
      (sixVertexPhysicalRowCycleDiagonalGradeEquiv totalC)]
    rw [Nat.card_eq_fintype_card]
    exact card_sixVertexMarkedSectorRowCycleDiagonalGradeFiber
      T middle totalC
  simpa only [← Nat.card_eq_fintype_card] using
    congrArg₂ Nat.sub hpair hdiagonal

@[simp] theorem sixVertexPhysicalRowCycleOffDiagonalSwap_totalC
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    (target : SixVertexPhysicalRowCycleOffDiagonalTarget T middle) :
    sixVertexPhysicalRowCyclePairTotalC
        (sixVertexPhysicalRowCycleOffDiagonalSwap target) =
      sixVertexPhysicalRowCyclePairTotalC target.1 := by
  simp [sixVertexPhysicalRowCyclePairTotalC,
    sixVertexMarkedSectorRowCyclePairTotalC,
    sixVertexPhysicalRowCycleOffDiagonalSwap, Nat.add_comm]



def SixVertexPhysicalRowCycleExactGradeCapacity
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  forall totalC,
    Nonempty
      ({source : SixVertexPhysicalRowCycleSource T middle
          hmiddle_pos hmiddle_lt //
        sixVertexPhysicalRowCyclePairTotalC source = totalC} ↪
      {target : SixVertexPhysicalRowCycleOffDiagonalTarget T middle //
        sixVertexPhysicalRowCyclePairTotalC target.1 = totalC})

set_option maxHeartbeats 1000000 in

noncomputable def
    sixVertexPhysicalRowCyclePairedBranchEmbeddings_of_exactGradeCapacity
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (hcapacity : SixVertexPhysicalRowCycleExactGradeCapacity
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexPhysicalRowCyclePairedBranchEmbeddings
      T middle hmiddle_pos hmiddle_lt := by
  classical
  let fiberEmbedding : forall totalC,
      {source : SixVertexPhysicalRowCycleSource T middle
          hmiddle_pos hmiddle_lt //
        sixVertexPhysicalRowCyclePairTotalC source = totalC} ↪
      {target : SixVertexPhysicalRowCycleOffDiagonalTarget T middle //
        sixVertexPhysicalRowCyclePairTotalC target.1 = totalC} :=
    fun totalC => Classical.choice (hcapacity totalC)
  let gradedEmbedding :
      (Sigma fun totalC =>
        {source : SixVertexPhysicalRowCycleSource T middle
            hmiddle_pos hmiddle_lt //
          sixVertexPhysicalRowCyclePairTotalC source = totalC}) ↪
      (Sigma fun totalC =>
        {target : SixVertexPhysicalRowCycleOffDiagonalTarget T middle //
          sixVertexPhysicalRowCyclePairTotalC target.1 = totalC}) :=
    { toFun := fun graded =>
        ⟨graded.1, fiberEmbedding graded.1 graded.2⟩
      inj' := by
        rintro ⟨firstTotal, first⟩ ⟨secondTotal, second⟩ heq
        have htotal : firstTotal = secondTotal := congrArg Sigma.fst heq
        subst secondTotal
        have hfiber : fiberEmbedding firstTotal first =
            fiberEmbedding firstTotal second := by
          exact eq_of_heq (Sigma.mk.inj heq).2
        have hsource := (fiberEmbedding firstTotal).injective hfiber
        cases hsource
        rfl }
  let matchingEmbedding :
      SixVertexPhysicalRowCycleSource T middle hmiddle_pos hmiddle_lt ↪
        SixVertexPhysicalRowCycleOffDiagonalTarget T middle :=
    (Equiv.sigmaFiberEquiv
      (fun source : SixVertexPhysicalRowCycleSource T middle
          hmiddle_pos hmiddle_lt =>
        sixVertexPhysicalRowCyclePairTotalC source)).symm.toEmbedding |>.trans
      (gradedEmbedding.trans
        (Equiv.sigmaFiberEquiv
          (fun target : SixVertexPhysicalRowCycleOffDiagonalTarget T middle =>
            sixVertexPhysicalRowCyclePairTotalC target.1)).toEmbedding)
  exact
    { branch := fun choice =>
        matchingEmbedding.trans
          (if choice then sixVertexPhysicalRowCycleOffDiagonalSwap
            else sixVertexPhysicalRowCycleOffDiagonalForget)
      distinct := by
        intro source
        simpa [matchingEmbedding] using
          sixVertexPhysicalRowCycleOffDiagonal_branches_distinct
            (matchingEmbedding source)
      aggregateTotalC := by
        intro source
        have hs : sixVertexPhysicalRowCyclePairTotalC
              (matchingEmbedding source).1 =
            sixVertexPhysicalRowCyclePairTotalC source := by
          simpa [matchingEmbedding, gradedEmbedding] using
            (fiberEmbedding
              (sixVertexPhysicalRowCyclePairTotalC source)
              ⟨source, rfl⟩).2
        simp only [matchingEmbedding, Function.Embedding.trans_apply,
          Bool.false_eq_true, if_false, if_true]
        rw [sixVertexPhysicalRowCycleOffDiagonalSwap_totalC]
        change 2 * sixVertexPhysicalRowCyclePairTotalC source <=
          sixVertexPhysicalRowCyclePairTotalC (matchingEmbedding source).1 +
            sixVertexPhysicalRowCyclePairTotalC (matchingEmbedding source).1
        omega }

end

end StatMech.FrontierD
