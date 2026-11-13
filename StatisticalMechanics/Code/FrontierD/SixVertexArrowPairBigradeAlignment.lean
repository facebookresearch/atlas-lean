/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexLoopPairBigrade









namespace StatMech.FrontierD

noncomputable section

def sixVertexArrowStrandSlotColor
    {T : EvenTorus} (omega : SixVertexArrows T)
    (slot : T.Vertex × Bool) : Bool :=
  sixVertexArrowPairStrandSlotColor omega omega
    (false, slot.1, slot.2)

def sixVertexArrowCheckerHorizontalAgreementCount
    {T : EvenTorus} (omega : SixVertexArrows T) : Nat :=
  Fintype.card {v : T.Vertex //
    omega.horizontal v = fkMedialVertexParity v}

theorem sixVertexArrowStrandSlotColor_west_succ_eq_east
    {T : EvenTorus} (omega : SixVertexArrows T) (v : T.Vertex) :
    sixVertexArrowStrandSlotColor omega
        ((finitePeriodicSucc T.width_pos v.1, v.2), false) =
      sixVertexArrowStrandSlotColor omega (v, true) := by
  have hc := fkMedialCheckerColor_bondMate_ne T (v, .east)
  have hi := fkMedialDartIncoming_bondMate_ne T omega (v, .east)
  have hxor := boolXor_eq_of_ne_ne hc hi
  simpa [sixVertexArrowStrandSlotColor,
    sixVertexArrowPairStrandSlotColor, fkMedialBondMate] using hxor

theorem sixVertexArrowStrandSlotColor_west_eq_east_pred
    {T : EvenTorus} (omega : SixVertexArrows T) (v : T.Vertex) :
    sixVertexArrowStrandSlotColor omega (v, false) =
      sixVertexArrowStrandSlotColor omega
        ((SixVertexArrows.cyclicPred T.width_pos v.1, v.2), true) := by
  simpa [finitePeriodicSucc_cyclicPred] using
    sixVertexArrowStrandSlotColor_west_succ_eq_east omega
      (SixVertexArrows.cyclicPred T.width_pos v.1, v.2)

theorem sixVertexArrowStrandSlotColor_east_eq_true_iff
    {T : EvenTorus} (omega : SixVertexArrows T) (v : T.Vertex) :
    sixVertexArrowStrandSlotColor omega (v, true) = true ↔
      omega.horizontal v = fkMedialVertexParity v := by
  unfold sixVertexArrowStrandSlotColor
    sixVertexArrowPairStrandSlotColor fkMedialDartIncoming
    fkLoopEastIncoming fkMedialCheckerColor fkMedialSideVertical
  generalize hp : fkMedialVertexParity v = p
  generalize hh : omega.horizontal v = h
  cases p <;> cases h <;> simp_all

noncomputable def sixVertexArrowTrueStrandSlotEquiv
    {T : EvenTorus} (omega : SixVertexArrows T) :
    {slot : T.Vertex × Bool //
        sixVertexArrowStrandSlotColor omega slot = true} ≃
      ({v : T.Vertex //
          omega.horizontal v = fkMedialVertexParity v} × Bool) where
  toFun slot := by
    rcases slot with ⟨⟨v, side⟩, hcolor⟩
    cases side
    · let u : T.Vertex :=
        (SixVertexArrows.cyclicPred T.width_pos v.1, v.2)
      refine (⟨u, ?_⟩, false)
      apply (sixVertexArrowStrandSlotColor_east_eq_true_iff omega u).mp
      rw [← sixVertexArrowStrandSlotColor_west_eq_east_pred omega v]
      exact hcolor
    · refine (⟨v, ?_⟩, true)
      exact (sixVertexArrowStrandSlotColor_east_eq_true_iff omega v).mp hcolor
  invFun slot := by
    rcases slot with ⟨⟨v, hv⟩, side⟩
    cases side
    · refine ⟨((finitePeriodicSucc T.width_pos v.1, v.2), false), ?_⟩
      rw [sixVertexArrowStrandSlotColor_west_succ_eq_east]
      exact (sixVertexArrowStrandSlotColor_east_eq_true_iff omega v).mpr hv
    · exact ⟨(v, true),
        (sixVertexArrowStrandSlotColor_east_eq_true_iff omega v).mpr hv⟩
  left_inv slot := by
    rcases slot with ⟨⟨v, side⟩, hcolor⟩
    cases side
    · apply Subtype.ext
      simp [finitePeriodicSucc_cyclicPred]
    · rfl
  right_inv slot := by
    rcases slot with ⟨⟨v, hv⟩, side⟩
    cases side
    · apply Prod.ext
      · apply Subtype.ext
        simp [svCyclicPred_finitePeriodicSucc]
      · rfl
    · rfl

def sixVertexArrowTrueStrandSlotCount
    {T : EvenTorus} (omega : SixVertexArrows T) : Nat :=
  Fintype.card {slot : T.Vertex × Bool //
    sixVertexArrowStrandSlotColor omega slot = true}

theorem sixVertexArrowTrueStrandSlotCount_eq_two_mul_alignment
    {T : EvenTorus} (omega : SixVertexArrows T) :
    sixVertexArrowTrueStrandSlotCount omega =
      2 * sixVertexArrowCheckerHorizontalAgreementCount omega := by
  unfold sixVertexArrowTrueStrandSlotCount
  rw [Fintype.card_congr (sixVertexArrowTrueStrandSlotEquiv omega)]
  simp [sixVertexArrowCheckerHorizontalAgreementCount]
  omega

noncomputable def sixVertexArrowPairTrueStrandSlotEquivSum
    {T : EvenTorus} (omega eta : SixVertexArrows T) :
    {slot : FKLayeredStrandSlot T //
        sixVertexArrowPairStrandSlotColor omega eta slot = true} ≃
      {slot : T.Vertex × Bool //
          sixVertexArrowStrandSlotColor omega slot = true} ⊕
        {slot : T.Vertex × Bool //
          sixVertexArrowStrandSlotColor eta slot = true} where
  toFun slot := by
    rcases slot with ⟨⟨layer, v, side⟩, hcolor⟩
    cases layer
    · exact Sum.inl ⟨(v, side), hcolor⟩
    · exact Sum.inr ⟨(v, side), hcolor⟩
  invFun slot := by
    rcases slot with slot | slot
    · exact ⟨(false, slot.1.1, slot.1.2), slot.2⟩
    · exact ⟨(true, slot.1.1, slot.1.2), slot.2⟩
  left_inv slot := by
    rcases slot with ⟨⟨layer, v, side⟩, hcolor⟩
    cases layer <;> rfl
  right_inv slot := by
    rcases slot with slot | slot <;> rfl

theorem sixVertexArrowPairTrueStrandSlotCount_eq_two_mul_alignment
    {T : EvenTorus} (omega eta : SixVertexArrows T) :
    sixVertexArrowPairTrueStrandSlotCount omega eta =
      2 * (sixVertexArrowCheckerHorizontalAgreementCount omega +
        sixVertexArrowCheckerHorizontalAgreementCount eta) := by
  unfold sixVertexArrowPairTrueStrandSlotCount
  rw [Fintype.card_congr
      (sixVertexArrowPairTrueStrandSlotEquivSum omega eta),
    Fintype.card_sum,
    ← sixVertexArrowTrueStrandSlotCount,
    ← sixVertexArrowTrueStrandSlotCount,
    sixVertexArrowTrueStrandSlotCount_eq_two_mul_alignment,
    sixVertexArrowTrueStrandSlotCount_eq_two_mul_alignment]
  omega

end

end StatMech.FrontierD
