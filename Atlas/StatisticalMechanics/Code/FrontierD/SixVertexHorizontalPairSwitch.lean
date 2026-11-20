/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexHorizontalColumnClassification










open Finset

namespace StatMech.FrontierD

noncomputable section

local instance instDecidablePropHorizontalPairSwitch (p : Prop) : Decidable p :=
  Classical.propDecidable p


def sixVertexSwitchHorizontalPair
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    SixVertexHorizontalField T × SixVertexHorizontalField T :=
  (fun v => if mask v.1 then horizontal.2 v else horizontal.1 v,
   fun v => if mask v.1 then horizontal.1 v else horizontal.2 v)

theorem sixVertexHorizontalZeroCount_eq_sum
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    sixVertexHorizontalZeroCount horizontal =
      ∑ v : T.Vertex,
        if sixVertexHorizontalGaugeBit horizontal v = false then 1 else 0 := by
  unfold sixVertexHorizontalZeroCount
  rw [Fintype.card_subtype, Finset.card_filter]


theorem sixVertexSwitchHorizontalPair_zeroCount
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    sixVertexHorizontalZeroCount
          (sixVertexSwitchHorizontalPair mask horizontal).1 +
        sixVertexHorizontalZeroCount
          (sixVertexSwitchHorizontalPair mask horizontal).2 =
      sixVertexHorizontalZeroCount horizontal.1 +
        sixVertexHorizontalZeroCount horizontal.2 := by
  simp only [sixVertexHorizontalZeroCount_eq_sum, <- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  unfold sixVertexSwitchHorizontalPair sixVertexHorizontalGaugeBit
  cases hmask : mask v.1 <;> simp [hmask, add_comm]


theorem sixVertexSwitchHorizontalPair_involutive
    {T : EvenTorus} (mask : Fin T.width -> Bool) :
    Function.Involutive
      (sixVertexSwitchHorizontalPair (T := T) mask) := by
  intro horizontal
  apply Prod.ext <;> funext v
  · unfold sixVertexSwitchHorizontalPair
    cases hmask : mask v.1 <;> simp [hmask]
  · unfold sixVertexSwitchHorizontalPair
    cases hmask : mask v.1 <;> simp [hmask]

def boolPairAgreementCount (a b c d : Bool) : Nat :=
  (if a = c then 1 else 0) + (if b = d then 1 else 0)

def boolPairCrossAgreementCount (a b c d : Bool) : Nat :=
  (if a = d then 1 else 0) + (if b = c then 1 else 0)

theorem boolPairAgreementCount_eq_cross_of_left_eq
    {a b c d : Bool} (h : a = b) :
    boolPairAgreementCount a b c d =
      boolPairCrossAgreementCount a b c d := by
  subst b
  cases a <;> cases c <;> cases d <;> decide

theorem boolPairAgreementCount_eq_cross_of_right_eq
    {a b c d : Bool} (h : c = d) :
    boolPairAgreementCount a b c d =
      boolPairCrossAgreementCount a b c d := by
  subst d
  cases a <;> cases b <;> cases c <;> decide



theorem boolPairAgreementCount_add_cross_of_mixed
    {a b c d : Bool} (hab : a ≠ b) (hcd : c ≠ d) :
    boolPairAgreementCount a b c d +
      boolPairCrossAgreementCount a b c d = 2 := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [boolPairAgreementCount, boolPairCrossAgreementCount]

def sixVertexHorizontalPairBondAgreementCount
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
    (v : T.Vertex) : Nat :=
  boolPairAgreementCount
    (sixVertexHorizontalGaugeBit horizontal.1
      (SixVertexArrows.cyclicPred T.width_pos v.1, v.2))
    (sixVertexHorizontalGaugeBit horizontal.2
      (SixVertexArrows.cyclicPred T.width_pos v.1, v.2))
    (sixVertexHorizontalGaugeBit horizontal.1 v)
    (sixVertexHorizontalGaugeBit horizontal.2 v)

def sixVertexHorizontalPairBondCrossAgreementCount
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
    (v : T.Vertex) : Nat :=
  boolPairCrossAgreementCount
    (sixVertexHorizontalGaugeBit horizontal.1
      (SixVertexArrows.cyclicPred T.width_pos v.1, v.2))
    (sixVertexHorizontalGaugeBit horizontal.2
      (SixVertexArrows.cyclicPred T.width_pos v.1, v.2))
    (sixVertexHorizontalGaugeBit horizontal.1 v)
    (sixVertexHorizontalGaugeBit horizontal.2 v)

theorem sixVertexHorizontalPair_nontransitionCount_eq_sum
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    sixVertexHorizontalNontransitionCount horizontal.1 +
        sixVertexHorizontalNontransitionCount horizontal.2 =
      ∑ v : T.Vertex,
        sixVertexHorizontalPairBondAgreementCount horizontal v := by
  unfold sixVertexHorizontalNontransitionCount
    sixVertexHorizontalPairBondAgreementCount boolPairAgreementCount
  rw [Finset.sum_add_distrib]



theorem sixVertexSwitchHorizontalPair_bondAgreement
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
    (v : T.Vertex) :
    sixVertexHorizontalPairBondAgreementCount
        (sixVertexSwitchHorizontalPair mask horizontal) v =
      if mask (SixVertexArrows.cyclicPred T.width_pos v.1) = mask v.1
      then sixVertexHorizontalPairBondAgreementCount horizontal v
      else sixVertexHorizontalPairBondCrossAgreementCount horizontal v := by
  unfold sixVertexHorizontalPairBondAgreementCount
    sixVertexHorizontalPairBondCrossAgreementCount
    sixVertexSwitchHorizontalPair sixVertexHorizontalGaugeBit
  cases hleft : mask (SixVertexArrows.cyclicPred T.width_pos v.1) <;>
    cases hright : mask v.1 <;>
    simp [hleft, hright, boolPairAgreementCount,
      boolPairCrossAgreementCount, add_comm]

theorem sixVertexSwitchHorizontalPair_nontransitionCount
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    sixVertexHorizontalNontransitionCount
          (sixVertexSwitchHorizontalPair mask horizontal).1 +
        sixVertexHorizontalNontransitionCount
          (sixVertexSwitchHorizontalPair mask horizontal).2 =
      ∑ v : T.Vertex,
        if mask (SixVertexArrows.cyclicPred T.width_pos v.1) = mask v.1
        then sixVertexHorizontalPairBondAgreementCount horizontal v
        else sixVertexHorizontalPairBondCrossAgreementCount horizontal v := by
  rw [sixVertexHorizontalPair_nontransitionCount_eq_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact sixVertexSwitchHorizontalPair_bondAgreement mask horizontal v



def SixVertexHorizontalPairSwitchBoundaryBalanced
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    Prop :=
  (∑ v ∈ (Finset.univ : Finset T.Vertex).filter
        (fun v => mask (SixVertexArrows.cyclicPred T.width_pos v.1) ≠
          mask v.1),
      sixVertexHorizontalPairBondCrossAgreementCount horizontal v) =
    ∑ v ∈ (Finset.univ : Finset T.Vertex).filter
        (fun v => mask (SixVertexArrows.cyclicPred T.width_pos v.1) ≠
          mask v.1),
      sixVertexHorizontalPairBondAgreementCount horizontal v

theorem sixVertexSwitchHorizontalPair_nontransitionCount_eq_of_boundaryBalanced
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
    (hbalanced :
      SixVertexHorizontalPairSwitchBoundaryBalanced mask horizontal) :
    sixVertexHorizontalNontransitionCount
          (sixVertexSwitchHorizontalPair mask horizontal).1 +
        sixVertexHorizontalNontransitionCount
          (sixVertexSwitchHorizontalPair mask horizontal).2 =
      sixVertexHorizontalNontransitionCount horizontal.1 +
        sixVertexHorizontalNontransitionCount horizontal.2 := by
  rw [sixVertexSwitchHorizontalPair_nontransitionCount,
    sixVertexHorizontalPair_nontransitionCount_eq_sum]
  rw [Finset.sum_ite]
  change
    (∑ v ∈ (Finset.univ : Finset T.Vertex).filter
          (fun v => mask (SixVertexArrows.cyclicPred T.width_pos v.1) =
            mask v.1),
        sixVertexHorizontalPairBondAgreementCount horizontal v) +
      (∑ v ∈ (Finset.univ : Finset T.Vertex).filter
          (fun v => ¬mask (SixVertexArrows.cyclicPred T.width_pos v.1) =
            mask v.1),
        sixVertexHorizontalPairBondCrossAgreementCount horizontal v) = _
  rw [show (∑ v ∈ (Finset.univ : Finset T.Vertex).filter
          (fun v => ¬mask (SixVertexArrows.cyclicPred T.width_pos v.1) =
            mask v.1),
        sixVertexHorizontalPairBondCrossAgreementCount horizontal v) =
      ∑ v ∈ (Finset.univ : Finset T.Vertex).filter
          (fun v => mask (SixVertexArrows.cyclicPred T.width_pos v.1) ≠
            mask v.1),
        sixVertexHorizontalPairBondCrossAgreementCount horizontal v by rfl,
    hbalanced]
  exact Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset T.Vertex)
    (fun v => mask (SixVertexArrows.cyclicPred T.width_pos v.1) = mask v.1)
    (sixVertexHorizontalPairBondAgreementCount horizontal)



theorem sixVertexSwitchHorizontalPair_bigrade_of_boundaryBalanced
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
    (hbalanced :
      SixVertexHorizontalPairSwitchBoundaryBalanced mask horizontal) :
    sixVertexHorizontalPairBigrade
        (sixVertexSwitchHorizontalPair mask horizontal) =
      sixVertexHorizontalPairBigrade horizontal := by
  unfold sixVertexHorizontalPairBigrade
  apply Prod.ext
  · exact sixVertexSwitchHorizontalPair_nontransitionCount_eq_of_boundaryBalanced
      mask horizontal hbalanced
  · simp only [sixVertexSwitchHorizontalPair_zeroCount]

end

end StatMech.FrontierD
