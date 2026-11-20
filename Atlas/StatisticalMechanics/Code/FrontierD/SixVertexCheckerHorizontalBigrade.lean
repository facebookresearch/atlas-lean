/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexArrowPairBigradeAlignment








namespace StatMech.FrontierD

noncomputable section

def sixVertexCheckerHorizontalBit
    {T : EvenTorus} (omega : SixVertexArrows T) (v : T.Vertex) : Bool :=
  omega.horizontal v ^^ fkMedialVertexParity v

def sixVertexCheckerHorizontalZeroCount
    {T : EvenTorus} (omega : SixVertexArrows T) : Nat :=
  Fintype.card {v : T.Vertex //
    sixVertexCheckerHorizontalBit omega v = false}

def sixVertexCheckerHorizontalNontransitionCount
    {T : EvenTorus} (omega : SixVertexArrows T) : Nat :=
  ∑ v, if sixVertexCheckerHorizontalBit omega
          (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) =
        sixVertexCheckerHorizontalBit omega v then 1 else 0

theorem sixVertex_horizontal_agrees_checker_iff_gauged_false
    {T : EvenTorus} (omega : SixVertexArrows T) (v : T.Vertex) :
    omega.horizontal v = fkMedialVertexParity v ↔
      sixVertexCheckerHorizontalBit omega v = false := by
  unfold sixVertexCheckerHorizontalBit
  generalize hh : omega.horizontal v = h
  generalize hp : fkMedialVertexParity v = p
  cases h <;> cases p <;> simp_all

theorem sixVertexArrowCheckerHorizontalAgreementCount_eq_zeroCount
    {T : EvenTorus} (omega : SixVertexArrows T) :
    sixVertexArrowCheckerHorizontalAgreementCount omega =
      sixVertexCheckerHorizontalZeroCount omega := by
  unfold sixVertexArrowCheckerHorizontalAgreementCount
    sixVertexCheckerHorizontalZeroCount
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv (Equiv.refl _)
  intro v
  exact sixVertex_horizontal_agrees_checker_iff_gauged_false omega v

private theorem fkMedialVertexParity_cyclicPred_ne
    {T : EvenTorus} (v : T.Vertex) :
    fkMedialVertexParity
        (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) ≠
      fkMedialVertexParity v := by
  have hc := fkMedialCheckerColor_bondMate_ne T
    ((SixVertexArrows.cyclicPred T.width_pos v.1, v.2), .east)
  simpa [fkMedialBondMate, finitePeriodicSucc_cyclicPred,
    fkMedialCheckerColor, fkMedialSideVertical] using hc

theorem sixVertex_isCType_iff_checkerHorizontal_nontransition
    {T : EvenTorus} (omega : SixVertexArrows T) (v : T.Vertex) :
    omega.IsCType v ↔
      sixVertexCheckerHorizontalBit omega
          (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) =
        sixVertexCheckerHorizontalBit omega v := by
  rw [sixVertexIsCType_iff_horizontalIncoming_eq]
  unfold fkLoopWestIncoming fkLoopEastIncoming
    sixVertexCheckerHorizontalBit
  have hp := fkMedialVertexParity_cyclicPred_ne v
  generalize hleft : omega.horizontal
      (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) = left at hp ⊢
  generalize hright : omega.horizontal v = right at hp ⊢
  generalize hpleft : fkMedialVertexParity
      (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) = pleft at hp ⊢
  generalize hpright : fkMedialVertexParity v = pright at hp ⊢
  cases left <;> cases right <;> cases pleft <;> cases pright <;>
    simp_all

theorem sixVertexTorusCTypeCount_eq_checkerHorizontal_nontransitionCount
    {T : EvenTorus} (omega : SixVertexArrows T) :
    sixVertexTorusCTypeCount omega =
      sixVertexCheckerHorizontalNontransitionCount omega := by
  unfold sixVertexTorusCTypeCount
    sixVertexCheckerHorizontalNontransitionCount
  apply Finset.sum_congr rfl
  intro v _
  rw [sixVertex_isCType_iff_checkerHorizontal_nontransition]
  by_cases h : sixVertexCheckerHorizontalBit omega
      (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) =
    sixVertexCheckerHorizontalBit omega v <;> simp [h]

theorem sixVertexArrowPairTrueStrandSlotCount_eq_two_mul_zeroCount
    {T : EvenTorus} (omega eta : SixVertexArrows T) :
    sixVertexArrowPairTrueStrandSlotCount omega eta =
      2 * (sixVertexCheckerHorizontalZeroCount omega +
        sixVertexCheckerHorizontalZeroCount eta) := by
  rw [sixVertexArrowPairTrueStrandSlotCount_eq_two_mul_alignment,
    sixVertexArrowCheckerHorizontalAgreementCount_eq_zeroCount,
    sixVertexArrowCheckerHorizontalAgreementCount_eq_zeroCount]

end

end StatMech.FrontierD
