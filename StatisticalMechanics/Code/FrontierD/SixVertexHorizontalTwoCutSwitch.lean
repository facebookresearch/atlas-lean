/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexHorizontalPairSwitch









namespace StatMech.FrontierD

noncomputable section


def sixVertexHorizontalTwoCutMask
    {T : EvenTorus} (a b : Fin T.width) (x : Fin T.width) : Bool :=
  decide (a.val ≤ x.val ∧ x.val < b.val)



theorem sixVertexHorizontalTwoCutMask_boundary
    {T : EvenTorus} {a b : Fin T.width} (hab : a.val < b.val)
    (x : Fin T.width) :
    sixVertexHorizontalTwoCutMask a b
          (SixVertexArrows.cyclicPred T.width_pos x) ≠
        sixVertexHorizontalTwoCutMask a b x ↔
      x = a ∨ x = b := by
  simp only [sixVertexHorizontalTwoCutMask, Fin.ext_iff]
  by_cases hx0 : x.val = 0
  · have hpred :
        (SixVertexArrows.cyclicPred T.width_pos x).val =
          T.width - 1 := by
      unfold SixVertexArrows.cyclicPred
      simp only
      rw [hx0]
      simp
    rw [hpred, hx0]
    have hbLast : b.val ≤ T.width - 1 := by omega
    by_cases ha0 : a.val = 0
    · have hprev : ¬(a.val ≤ T.width - 1 ∧ T.width - 1 < b.val) :=
        by omega
      have hcurrent : a.val ≤ 0 ∧ 0 < b.val := by omega
      rw [decide_eq_false_iff_not.mpr hprev, decide_eq_true hcurrent]
      constructor
      · intro _
        exact Or.inl ha0.symm
      · intro _ h
        exact Bool.noConfusion h
    · have hprev : ¬(a.val ≤ T.width - 1 ∧ T.width - 1 < b.val) :=
        by omega
      have hcurrent : ¬(a.val ≤ 0 ∧ 0 < b.val) := by omega
      have hb0 : b.val ≠ 0 := by omega
      rw [decide_eq_false_iff_not.mpr hprev,
        decide_eq_false_iff_not.mpr hcurrent]
      constructor
      · intro h
        exact (h rfl).elim
      · intro hcuts
        rcases hcuts with h | h
        · exact (ha0 h.symm).elim
        · exact (hb0 h.symm).elim
  · have hxpos : 0 < x.val := Nat.pos_of_ne_zero hx0
    have hpred :
        (SixVertexArrows.cyclicPred T.width_pos x).val = x.val - 1 := by
      unfold SixVertexArrows.cyclicPred
      simp only
      rw [show x.val + T.width - 1 = T.width + (x.val - 1) by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hpred]
    by_cases hxa : x.val = a.val
    · have hprevOutside :
          ¬(a.val ≤ x.val - 1 ∧ x.val - 1 < b.val) := by omega
      have hcurrentInside : a.val ≤ x.val ∧ x.val < b.val := by omega
      have hxb : x.val ≠ b.val := by omega
      rw [decide_eq_false_iff_not.mpr hprevOutside,
        decide_eq_true hcurrentInside]
      constructor
      · intro _
        exact Or.inl hxa
      · intro _ h
        exact Bool.noConfusion h
    · by_cases hxb : x.val = b.val
      · have hprevInside :
            a.val ≤ x.val - 1 ∧ x.val - 1 < b.val := by
          omega
        have hcurrentOutside :
            ¬(a.val ≤ x.val ∧ x.val < b.val) := by omega
        rw [decide_eq_true hprevInside,
          decide_eq_false_iff_not.mpr hcurrentOutside]
        constructor
        · intro _
          exact Or.inr hxb
        · intro _ h
          exact Bool.noConfusion h
      · have hsame :
            (a.val ≤ x.val - 1 ∧ x.val - 1 < b.val) ↔
              (a.val ≤ x.val ∧ x.val < b.val) := by
          omega
        have hdecide :
            decide (a.val ≤ x.val - 1 ∧ x.val - 1 < b.val) =
              decide (a.val ≤ x.val ∧ x.val < b.val) := by
          apply Bool.eq_iff_iff.mpr
          simpa only [decide_eq_true_eq] using hsame
        rw [hdecide]
        constructor
        · intro h
          exact (h rfl).elim
        · intro hcuts
          rcases hcuts with h | h
          · exact (hxa h).elim
          · exact (hxb h).elim



theorem sixVertexHorizontalTwoCutMask_sum_boundary
    {T : EvenTorus} {a b : Fin T.width} (hab : a.val < b.val)
    (f : T.Vertex -> Nat) :
    (∑ v ∈ (Finset.univ : Finset T.Vertex).filter
        (fun v =>
          sixVertexHorizontalTwoCutMask a b
              (SixVertexArrows.cyclicPred T.width_pos v.1) ≠
            sixVertexHorizontalTwoCutMask a b v.1),
      f v) =
      (∑ j : Fin T.height, f (a, j)) +
        ∑ j : Fin T.height, f (b, j) := by
  rw [Finset.sum_filter]
  simp_rw [sixVertexHorizontalTwoCutMask_boundary hab]
  rw [Fintype.sum_prod_type]
  have habne : a ≠ b := fun h => by
    have := congrArg Fin.val h
    omega
  have hpoint (i : Fin T.width) :
      (∑ j : Fin T.height, if i = a ∨ i = b then f (i, j) else 0) =
        if i = a then (∑ j : Fin T.height, f (a, j))
        else if i = b then (∑ j : Fin T.height, f (b, j)) else 0 := by
    by_cases hia : i = a
    · subst i
      simp [habne]
    · by_cases hib : i = b
      · subst i
        simp [hia]
      · simp [hia, hib]
  simp_rw [hpoint]
  have hbane : b ≠ a := Ne.symm habne
  have hsplit (i : Fin T.width) :
      (if i = a then (∑ j : Fin T.height, f (a, j))
        else if i = b then (∑ j : Fin T.height, f (b, j)) else 0) =
      (if a = i then (∑ j : Fin T.height, f (a, j)) else 0) +
        (if b = i then (∑ j : Fin T.height, f (b, j)) else 0) := by
    by_cases hia : i = a
    · subst i
      simp [hbane]
    · by_cases hib : i = b
      · subst i
        simp [hia, habne]
      · simp [hia, hib, Ne.symm hia, Ne.symm hib]
  simp_rw [hsplit, Finset.sum_add_distrib, Fintype.sum_ite_eq]

def sixVertexHorizontalPairColumnAgreementCount
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
    (i : Fin T.width) : Nat :=
  ∑ j : Fin T.height,
    sixVertexHorizontalPairBondAgreementCount horizontal (i, j)

def sixVertexHorizontalPairColumnCrossAgreementCount
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
    (i : Fin T.width) : Nat :=
  ∑ j : Fin T.height,
    sixVertexHorizontalPairBondCrossAgreementCount horizontal (i, j)


def SixVertexHorizontalPairTwoCutBalanced
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
    (a b : Fin T.width) : Prop :=
  sixVertexHorizontalPairColumnCrossAgreementCount horizontal a +
      sixVertexHorizontalPairColumnCrossAgreementCount horizontal b =
    sixVertexHorizontalPairColumnAgreementCount horizontal a +
      sixVertexHorizontalPairColumnAgreementCount horizontal b

theorem sixVertexHorizontalTwoCutMask_boundaryBalanced
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
    {a b : Fin T.width} (hab : a.val < b.val)
    (hbalanced : SixVertexHorizontalPairTwoCutBalanced horizontal a b) :
    SixVertexHorizontalPairSwitchBoundaryBalanced
      (sixVertexHorizontalTwoCutMask a b) horizontal := by
  unfold SixVertexHorizontalPairSwitchBoundaryBalanced
  rw [sixVertexHorizontalTwoCutMask_sum_boundary hab,
    sixVertexHorizontalTwoCutMask_sum_boundary hab]
  simpa [SixVertexHorizontalPairTwoCutBalanced,
    sixVertexHorizontalPairColumnCrossAgreementCount,
    sixVertexHorizontalPairColumnAgreementCount] using hbalanced



theorem sixVertexHorizontalTwoCutSwitch_bigrade
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
    {a b : Fin T.width} (hab : a.val < b.val)
    (hbalanced : SixVertexHorizontalPairTwoCutBalanced horizontal a b) :
    sixVertexHorizontalPairBigrade
        (sixVertexSwitchHorizontalPair
          (sixVertexHorizontalTwoCutMask a b) horizontal) =
      sixVertexHorizontalPairBigrade horizontal :=
  sixVertexSwitchHorizontalPair_bigrade_of_boundaryBalanced _ _
    (sixVertexHorizontalTwoCutMask_boundaryBalanced horizontal hab hbalanced)

end

end StatMech.FrontierD
