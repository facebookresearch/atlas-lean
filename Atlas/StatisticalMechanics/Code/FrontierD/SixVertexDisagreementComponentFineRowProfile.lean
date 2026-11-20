/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDisagreementComponentCType
import Code.FrontierD.SixVertexHorizontalFineRowProfile











open Finset

namespace StatMech.FrontierD

noncomputable section

local instance sixVertexDisagreementComponentFineRowProfilePropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p



theorem sixVertexHorizontalRowNontransitionCount_eq_rowCTypeCount
    {T : EvenTorus} (omega : SixVertexArrows T) (j : Fin T.height) :
    sixVertexHorizontalRowNontransitionCount omega.horizontal j =
      ∑ i : Fin T.width, if omega.IsCType (i, j) then 1 else 0 := by
  classical
  unfold sixVertexHorizontalRowNontransitionCount
  apply Finset.sum_congr rfl
  intro i hi
  rw [sixVertex_isCType_iff_checkerHorizontal_nontransition]
  unfold sixVertexHorizontalGaugeBit sixVertexCheckerHorizontalBit
  by_cases heq :
      (omega.horizontal (SixVertexArrows.cyclicPred T.width_pos i, j) ^^
          fkMedialVertexParity
            (SixVertexArrows.cyclicPred T.width_pos i, j)) =
        (omega.horizontal (i, j) ^^ fkMedialVertexParity (i, j)) <;>
    simp only [heq, ↓reduceIte]


theorem sixVertexTorusPairSwitch_rowZeroProfile
    {T : EvenTorus} (mask omega eta : SixVertexArrows T) :
    sixVertexHorizontalPairRowZeroProfile
        ((sixVertexTorusSwitchFirst mask omega eta).horizontal,
          (sixVertexTorusSwitchSecond mask omega eta).horizontal) =
      sixVertexHorizontalPairRowZeroProfile
        (omega.horizontal, eta.horizontal) := by
  funext j
  unfold sixVertexHorizontalPairRowZeroProfile
    sixVertexHorizontalRowZeroCount
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  unfold sixVertexHorizontalGaugeBit sixVertexTorusSwitchFirst
    sixVertexTorusSwitchSecond
  cases hmask : mask.horizontal (i, j) <;> simp [hmask, add_comm]



theorem sixVertexLexDisagreementComponentSwitch_rowNontransitionProfile
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
    sixVertexHorizontalPairRowNontransitionProfile
        ((sixVertexTorusSwitchFirst
            (sixVertexLexDisagreementComponentMask T omega eta h)
            omega eta).horizontal,
          (sixVertexTorusSwitchSecond
            (sixVertexLexDisagreementComponentMask T omega eta h)
            omega eta).horizontal) =
      sixVertexHorizontalPairRowNontransitionProfile
        (omega.horizontal, eta.horizontal) := by
  classical
  funext j
  unfold sixVertexHorizontalPairRowNontransitionProfile
  rw [sixVertexHorizontalRowNontransitionCount_eq_rowCTypeCount,
    sixVertexHorizontalRowNontransitionCount_eq_rowCTypeCount,
    sixVertexHorizontalRowNontransitionCount_eq_rowCTypeCount,
    sixVertexHorizontalRowNontransitionCount_eq_rowCTypeCount,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hlocal := sixVertexLexDisagreementComponentSwitch_localCTypeCount
    T omega eta h (i, j)
  simpa only [sixVertexLocalCTypeCount,
    sixVertexLocalIncomingPattern_isCType_iff] using hlocal



theorem sixVertexLexDisagreementComponentSwitch_fineRowProfile
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
    sixVertexHorizontalPairFineRowProfile
        ((sixVertexTorusSwitchFirst
            (sixVertexLexDisagreementComponentMask T omega eta h)
            omega eta).horizontal,
          (sixVertexTorusSwitchSecond
            (sixVertexLexDisagreementComponentMask T omega eta h)
            omega eta).horizontal) =
      sixVertexHorizontalPairFineRowProfile
        (omega.horizontal, eta.horizontal) := by
  funext j
  apply Prod.ext
  · exact congrFun
      (sixVertexLexDisagreementComponentSwitch_rowNontransitionProfile
        T omega eta h) j
  · exact congrFun
      (sixVertexTorusPairSwitch_rowZeroProfile
        (sixVertexLexDisagreementComponentMask T omega eta h) omega eta) j



theorem sixVertexLexDisagreementComponentSwitch_boundedFineRowProfile
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
    sixVertexHorizontalPairBoundedFineRowProfile
        ((sixVertexTorusSwitchFirst
            (sixVertexLexDisagreementComponentMask T omega eta h)
            omega eta).horizontal,
          (sixVertexTorusSwitchSecond
            (sixVertexLexDisagreementComponentMask T omega eta h)
            omega eta).horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile
        (omega.horizontal, eta.horizontal) :=
  sixVertexHorizontalPairBoundedFineRowProfile_eq_of_fine_eq
    (sixVertexLexDisagreementComponentSwitch_fineRowProfile T omega eta h)



theorem exists_middle_pair_same_boundedFineRowProfile_of_componentTransfer_one
    (T : EvenTorus) (omega eta : SixVertexArrows T) (middle : Nat)
    (homega : omega.IceRule) (heta : eta.IceRule)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty)
    (htransfer : sixVertexTorusMaskSeamTransfer
      (sixVertexLexDisagreementComponentMask T omega eta h)
      omega eta = 1) :
    exists first second : SixVertexArrows T,
      first.IceRule /\ second.IceRule /\
      sixVertexUpCount
          (svTorusVerticalRows T first (svFinLast T.height_pos)) = middle /\
      sixVertexUpCount
          (svTorusVerticalRows T second (svFinLast T.height_pos)) = middle /\
      sixVertexHorizontalPairBoundedFineRowProfile
          (first.horizontal, second.horizontal) =
        sixVertexHorizontalPairBoundedFineRowProfile
          (omega.horizontal, eta.horizontal) := by
  let first := sixVertexTorusSwitchFirst
    (sixVertexLexDisagreementComponentMask T omega eta h) omega eta
  let second := sixVertexTorusSwitchSecond
    (sixVertexLexDisagreementComponentMask T omega eta h) omega eta
  obtain ⟨hfirstIce, hsecondIce, hfirstSector, hsecondSector⟩ :=
    sixVertexLexDisagreementComponentSwitch_to_middle_of_transfer_one
      T omega eta middle homega heta homegaSector hetaSector hmiddle h htransfer
  refine ⟨first, second, hfirstIce, hsecondIce, hfirstSector, hsecondSector, ?_⟩
  exact sixVertexLexDisagreementComponentSwitch_boundedFineRowProfile
    T omega eta h

end

end StatMech.FrontierD
