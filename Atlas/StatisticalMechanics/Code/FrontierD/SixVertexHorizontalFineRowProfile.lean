/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexHorizontalRowProfileAggregate









open Finset

namespace StatMech.FrontierD

noncomputable section


def sixVertexHorizontalRowNontransitionCount
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T)
    (j : Fin T.height) : Nat :=
  ∑ i : Fin T.width,
    if sixVertexHorizontalGaugeBit horizontal
          (SixVertexArrows.cyclicPred T.width_pos i, j) =
        sixVertexHorizontalGaugeBit horizontal (i, j)
    then 1 else 0


def sixVertexHorizontalPairRowNontransitionProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) : Fin T.height -> Nat :=
  fun j => sixVertexHorizontalRowNontransitionCount horizontal.1 j +
    sixVertexHorizontalRowNontransitionCount horizontal.2 j


def sixVertexHorizontalPairFineRowProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) : Fin T.height -> Nat × Nat :=
  fun j =>
    (sixVertexHorizontalPairRowNontransitionProfile horizontal j,
      sixVertexHorizontalPairRowZeroProfile horizontal j)

abbrev SixVertexHorizontalBoundedFineRowProfile (T : EvenTorus) :=
  Fin T.height -> Fin (2 * T.width + 1) × Fin (2 * T.width + 1)

theorem sixVertexHorizontalRowZeroCount_le_width
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T)
    (j : Fin T.height) :
    sixVertexHorizontalRowZeroCount horizontal j <= T.width := by
  unfold sixVertexHorizontalRowZeroCount
  calc
    (∑ i : Fin T.width,
      if sixVertexHorizontalGaugeBit horizontal (i, j) = false
      then 1 else 0) <= ∑ _i : Fin T.width, 1 := by
        apply Finset.sum_le_sum
        intro i hi
        split <;> simp
    _ = T.width := by simp

theorem sixVertexHorizontalRowNontransitionCount_le_width
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T)
    (j : Fin T.height) :
    sixVertexHorizontalRowNontransitionCount horizontal j <= T.width := by
  unfold sixVertexHorizontalRowNontransitionCount
  calc
    (∑ i : Fin T.width,
      if sixVertexHorizontalGaugeBit horizontal
            (SixVertexArrows.cyclicPred T.width_pos i, j) =
          sixVertexHorizontalGaugeBit horizontal (i, j)
      then 1 else 0) <= ∑ _i : Fin T.width, 1 := by
        apply Finset.sum_le_sum
        intro i hi
        split <;> simp
    _ = T.width := by simp



def sixVertexHorizontalPairBoundedFineRowProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    SixVertexHorizontalBoundedFineRowProfile T :=
  fun j =>
    (⟨sixVertexHorizontalPairRowNontransitionProfile horizontal j,
      by
        unfold sixVertexHorizontalPairRowNontransitionProfile
        have hfirst := sixVertexHorizontalRowNontransitionCount_le_width
          horizontal.1 j
        have hsecond := sixVertexHorizontalRowNontransitionCount_le_width
          horizontal.2 j
        omega⟩,
     ⟨sixVertexHorizontalPairRowZeroProfile horizontal j,
      by
        unfold sixVertexHorizontalPairRowZeroProfile
        have hfirst := sixVertexHorizontalRowZeroCount_le_width horizontal.1 j
        have hsecond := sixVertexHorizontalRowZeroCount_le_width horizontal.2 j
        omega⟩)

theorem sixVertexHorizontalPairBoundedFineRowProfile_eq_of_fine_eq
    {T : EvenTorus}
    {first second : SixVertexHorizontalField T ×
      SixVertexHorizontalField T}
    (h : sixVertexHorizontalPairFineRowProfile first =
      sixVertexHorizontalPairFineRowProfile second) :
    sixVertexHorizontalPairBoundedFineRowProfile first =
      sixVertexHorizontalPairBoundedFineRowProfile second := by
  funext j
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg Prod.fst (congrFun h j)
  · exact congrArg Prod.snd (congrFun h j)

theorem sum_sixVertexHorizontalRowNontransitionCount
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    (∑ j : Fin T.height,
      sixVertexHorizontalRowNontransitionCount horizontal j) =
      sixVertexHorizontalNontransitionCount horizontal := by
  unfold sixVertexHorizontalRowNontransitionCount
    sixVertexHorizontalNontransitionCount
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem sum_sixVertexHorizontalPairRowNontransitionProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    (∑ j : Fin T.height,
      sixVertexHorizontalPairRowNontransitionProfile horizontal j) =
      sixVertexHorizontalNontransitionCount horizontal.1 +
        sixVertexHorizontalNontransitionCount horizontal.2 := by
  unfold sixVertexHorizontalPairRowNontransitionProfile
  rw [Finset.sum_add_distrib,
    sum_sixVertexHorizontalRowNontransitionCount,
    sum_sixVertexHorizontalRowNontransitionCount]

theorem sixVertexHorizontalRowNontransitionCount_reflect
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T)
    (j : Fin T.height) :
    sixVertexHorizontalRowNontransitionCount
        (sixVertexReflectHorizontalField horizontal) j =
      sixVertexHorizontalRowNontransitionCount horizontal j := by
  let xEquiv : Fin T.width ≃ Fin T.width :=
    (sixVertexCyclicNegEquiv T.width_pos).trans
      (svFinitePeriodicSuccEquiv T.width_pos)
  unfold sixVertexHorizontalRowNontransitionCount
  calc
    (∑ i : Fin T.width,
      if sixVertexHorizontalGaugeBit
            (sixVertexReflectHorizontalField horizontal)
            (SixVertexArrows.cyclicPred T.width_pos i, j) =
          sixVertexHorizontalGaugeBit
            (sixVertexReflectHorizontalField horizontal) (i, j)
      then 1 else 0) =
        ∑ i : Fin T.width,
          if sixVertexHorizontalGaugeBit horizontal
                (SixVertexArrows.cyclicPred T.width_pos (xEquiv i), j) =
              sixVertexHorizontalGaugeBit horizontal (xEquiv i, j)
          then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [sixVertexHorizontalGaugeBit_reflect,
        sixVertexHorizontalGaugeBit_reflect]
      have hnegPred := sixVertexCyclicNeg_cyclicPred T.width_pos i
      have hpredSucc := svCyclicPred_finitePeriodicSucc
        T.width_pos (sixVertexCyclicNeg T.width_pos i)
      change (if sixVertexHorizontalGaugeBit horizontal
            (sixVertexCyclicNeg T.width_pos
              (SixVertexArrows.cyclicPred T.width_pos i), j) =
          sixVertexHorizontalGaugeBit horizontal
            (sixVertexCyclicNeg T.width_pos i, j)
        then 1 else 0) = _
      rw [hnegPred]
      have hxi : xEquiv i = finitePeriodicSucc T.width_pos
          (sixVertexCyclicNeg T.width_pos i) := by rfl
      rw [hxi, hpredSucc]
      simp only [eq_comm]
    _ = _ := by
      exact xEquiv.sum_comp fun i =>
        if sixVertexHorizontalGaugeBit horizontal
              (SixVertexArrows.cyclicPred T.width_pos i, j) =
            sixVertexHorizontalGaugeBit horizontal (i, j)
        then 1 else 0

theorem sixVertexHorizontalPairRowNontransitionProfile_eq_sum
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) (j : Fin T.height) :
    sixVertexHorizontalPairRowNontransitionProfile horizontal j =
      ∑ i : Fin T.width,
        sixVertexHorizontalPairBondAgreementCount horizontal (i, j) := by
  unfold sixVertexHorizontalPairRowNontransitionProfile
    sixVertexHorizontalRowNontransitionCount
    sixVertexHorizontalPairBondAgreementCount boolPairAgreementCount
  rw [Finset.sum_add_distrib]

theorem sixVertexSwitchHorizontalPair_rowNontransitionProfile
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) (j : Fin T.height) :
    sixVertexHorizontalPairRowNontransitionProfile
        (sixVertexSwitchHorizontalPair mask horizontal) j =
      ∑ i : Fin T.width,
        if mask (SixVertexArrows.cyclicPred T.width_pos i) = mask i
        then sixVertexHorizontalPairBondAgreementCount horizontal (i, j)
        else sixVertexHorizontalPairBondCrossAgreementCount horizontal (i, j) := by
  rw [sixVertexHorizontalPairRowNontransitionProfile_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact sixVertexSwitchHorizontalPair_bondAgreement mask horizontal (i, j)


def SixVertexHorizontalPairSwitchRowBoundaryBalanced
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) : Prop :=
  forall j : Fin T.height,
    (∑ i ∈ (Finset.univ : Finset (Fin T.width)).filter
          (fun i => mask (SixVertexArrows.cyclicPred T.width_pos i) ≠ mask i),
        sixVertexHorizontalPairBondCrossAgreementCount horizontal (i, j)) =
      ∑ i ∈ (Finset.univ : Finset (Fin T.width)).filter
          (fun i => mask (SixVertexArrows.cyclicPred T.width_pos i) ≠ mask i),
        sixVertexHorizontalPairBondAgreementCount horizontal (i, j)

theorem sixVertexSwitchHorizontalPair_rowNontransitionProfile_eq_of_balanced
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T)
    (hbalanced :
      SixVertexHorizontalPairSwitchRowBoundaryBalanced mask horizontal) :
    sixVertexHorizontalPairRowNontransitionProfile
        (sixVertexSwitchHorizontalPair mask horizontal) =
      sixVertexHorizontalPairRowNontransitionProfile horizontal := by
  funext j
  rw [sixVertexSwitchHorizontalPair_rowNontransitionProfile,
    sixVertexHorizontalPairRowNontransitionProfile_eq_sum,
    Finset.sum_ite]
  change
    (∑ i ∈ (Finset.univ : Finset (Fin T.width)).filter
          (fun i => mask (SixVertexArrows.cyclicPred T.width_pos i) = mask i),
        sixVertexHorizontalPairBondAgreementCount horizontal (i, j)) +
      (∑ i ∈ (Finset.univ : Finset (Fin T.width)).filter
          (fun i => ¬mask (SixVertexArrows.cyclicPred T.width_pos i) = mask i),
        sixVertexHorizontalPairBondCrossAgreementCount horizontal (i, j)) = _
  rw [show (∑ i ∈ (Finset.univ : Finset (Fin T.width)).filter
          (fun i => ¬mask (SixVertexArrows.cyclicPred T.width_pos i) = mask i),
        sixVertexHorizontalPairBondCrossAgreementCount horizontal (i, j)) =
      ∑ i ∈ (Finset.univ : Finset (Fin T.width)).filter
          (fun i => mask (SixVertexArrows.cyclicPred T.width_pos i) ≠ mask i),
        sixVertexHorizontalPairBondCrossAgreementCount horizontal (i, j) by rfl,
    hbalanced j]
  exact Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin T.width))
    (fun i => mask (SixVertexArrows.cyclicPred T.width_pos i) = mask i)
    (fun i => sixVertexHorizontalPairBondAgreementCount horizontal (i, j))

theorem sixVertexSwitchHorizontalPair_fineRowProfile_of_balanced
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T)
    (hbalanced :
      SixVertexHorizontalPairSwitchRowBoundaryBalanced mask horizontal) :
    sixVertexHorizontalPairFineRowProfile
        (sixVertexSwitchHorizontalPair mask horizontal) =
      sixVertexHorizontalPairFineRowProfile horizontal := by
  funext j
  apply Prod.ext
  · exact congrFun
      (sixVertexSwitchHorizontalPair_rowNontransitionProfile_eq_of_balanced
        mask horizontal hbalanced) j
  · exact congrFun
      (sixVertexSwitchHorizontalPair_rowZeroProfile mask horizontal) j

theorem sixVertexSwitchHorizontalPair_boundedFineRowProfile_of_balanced
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T)
    (hbalanced :
      SixVertexHorizontalPairSwitchRowBoundaryBalanced mask horizontal) :
    sixVertexHorizontalPairBoundedFineRowProfile
        (sixVertexSwitchHorizontalPair mask horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile horizontal :=
  sixVertexHorizontalPairBoundedFineRowProfile_eq_of_fine_eq
    (sixVertexSwitchHorizontalPair_fineRowProfile_of_balanced
      mask horizontal hbalanced)

theorem sixVertexReflectFirstHorizontalLayer_fineRowProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairFineRowProfile
        (sixVertexReflectFirstHorizontalLayer horizontal) =
      sixVertexHorizontalPairFineRowProfile horizontal := by
  funext j
  apply Prod.ext
  · unfold sixVertexHorizontalPairFineRowProfile
      sixVertexHorizontalPairRowNontransitionProfile
      sixVertexReflectFirstHorizontalLayer
    rw [sixVertexHorizontalRowNontransitionCount_reflect]
  · exact congrFun
      (sixVertexReflectFirstHorizontalLayer_rowZeroProfile horizontal) j

theorem sixVertexReflectFirstHorizontalLayer_boundedFineRowProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairBoundedFineRowProfile
        (sixVertexReflectFirstHorizontalLayer horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile horizontal :=
  sixVertexHorizontalPairBoundedFineRowProfile_eq_of_fine_eq
    (sixVertexReflectFirstHorizontalLayer_fineRowProfile horizontal)

theorem sixVertexReflectSecondHorizontalLayer_fineRowProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairFineRowProfile
        (sixVertexReflectSecondHorizontalLayer horizontal) =
      sixVertexHorizontalPairFineRowProfile horizontal := by
  funext j
  apply Prod.ext
  · unfold sixVertexHorizontalPairFineRowProfile
      sixVertexHorizontalPairRowNontransitionProfile
      sixVertexReflectSecondHorizontalLayer
    rw [sixVertexHorizontalRowNontransitionCount_reflect]
  · exact congrFun
      (sixVertexReflectSecondHorizontalLayer_rowZeroProfile horizontal) j

theorem sixVertexReflectSecondHorizontalLayer_boundedFineRowProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairBoundedFineRowProfile
        (sixVertexReflectSecondHorizontalLayer horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile horizontal :=
  sixVertexHorizontalPairBoundedFineRowProfile_eq_of_fine_eq
    (sixVertexReflectSecondHorizontalLayer_fineRowProfile horizontal)

theorem sixVertexSwapHorizontalLayers_fineRowProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairFineRowProfile
        (sixVertexSwapHorizontalLayers horizontal) =
      sixVertexHorizontalPairFineRowProfile horizontal := by
  funext j
  apply Prod.ext
  · simp [sixVertexHorizontalPairFineRowProfile,
      sixVertexHorizontalPairRowNontransitionProfile,
      sixVertexSwapHorizontalLayers, add_comm]
  · exact congrFun (sixVertexSwapHorizontalLayers_rowZeroProfile horizontal) j

theorem sixVertexSwapHorizontalLayers_boundedFineRowProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairBoundedFineRowProfile
        (sixVertexSwapHorizontalLayers horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile horizontal :=
  sixVertexHorizontalPairBoundedFineRowProfile_eq_of_fine_eq
    (sixVertexSwapHorizontalLayers_fineRowProfile horizontal)




def SixVertexHorizontalFineRowProfileAggregateSignedNonnegative
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    Prop :=
  forall grade (rowProfile : SixVertexHorizontalRowZeroProfile T)
      (fineProfile : SixVertexHorizontalBoundedFineRowProfile T),
    0 <= ∑ horizontal ∈
        (Finset.univ : Finset
          (SixVertexHorizontalPairRowBigradeFiber T grade rowProfile)).filter
          (fun horizontal =>
            sixVertexHorizontalPairBoundedFineRowProfile horizontal.1 =
              fineProfile),
      sixVertexHorizontalProfileSignedKernel
        sourceLeft sourceRight targetLeft targetRight
        (sixVertexHorizontalPairCompletionProfile T horizontal.1)



theorem rowProfileSignedNonnegative_of_fineRowProfile
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (hfine : SixVertexHorizontalFineRowProfileAggregateSignedNonnegative T
      sourceLeft sourceRight targetLeft targetRight) :
    SixVertexHorizontalRowProfileAggregateSignedNonnegative T
      sourceLeft sourceRight targetLeft targetRight := by
  intro grade rowProfile
  let signature := fun horizontal :
      SixVertexHorizontalPairRowBigradeFiber T grade rowProfile =>
    sixVertexHorizontalPairBoundedFineRowProfile horizontal.1
  let kernel := fun horizontal :
      SixVertexHorizontalPairRowBigradeFiber T grade rowProfile =>
    sixVertexHorizontalProfileSignedKernel
      sourceLeft sourceRight targetLeft targetRight
      (sixVertexHorizontalPairCompletionProfile T horizontal.1)
  rw [← Finset.sum_fiberwise
    (Finset.univ : Finset
      (SixVertexHorizontalPairRowBigradeFiber T grade rowProfile))
    signature kernel]
  apply Finset.sum_nonneg
  intro fineProfile hfineProfile
  simpa [signature, kernel] using hfine grade rowProfile fineProfile



theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_fineRowProfileSigned
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hfine : SixVertexHorizontalFineRowProfileAggregateSignedNonnegative T
      ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩
      middle middle) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_rowProfileSigned
    T middle hmiddle_pos hmiddle_lt
      (rowProfileSignedNonnegative_of_fineRowProfile T
        ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩
        middle middle hfine)

end

end StatMech.FrontierD
