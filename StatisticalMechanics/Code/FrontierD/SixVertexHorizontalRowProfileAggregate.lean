/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexHorizontalRowProfileSupport








open Finset

namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexHorizontalPairRowBigradeFiber
    (T : EvenTorus) (grade : Nat × Nat)
    (rowProfile : SixVertexHorizontalRowZeroProfile T) :=
  {horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T //
    sixVertexHorizontalPairBigrade horizontal = grade /\
      sixVertexHorizontalPairRowZeroProfile horizontal = rowProfile}

noncomputable def sixVertexHorizontalActualDeficitRowProfileEquiv
    (T : EvenTorus) (grade : Nat × Nat)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (rowProfile : SixVertexHorizontalRowZeroProfile T) :
    {source : SixVertexHorizontalActualDeficitTokens T grade
        sourceLeft sourceRight targetLeft targetRight //
      sixVertexHorizontalActualDeficitRowProfile source = rowProfile} ≃
      Sigma fun horizontal :
          SixVertexHorizontalPairRowBigradeFiber T grade rowProfile =>
        Fin (sixVertexHorizontalProfileDeficit
          sourceLeft sourceRight targetLeft targetRight
          (sixVertexHorizontalPairCompletionProfile T horizontal.1)) where
  toFun source := by
    let horizontal : SixVertexHorizontalPairRowBigradeFiber
        T grade rowProfile :=
      ⟨sixVertexHorizontalActualDeficitPair source.1,
        sixVertexHorizontalActualDeficitPair_bigrade source.1,
        source.2⟩
    refine ⟨horizontal, source.1.2.2.1, ?_⟩
    have hprofile := source.1.2.1.2
    simpa [horizontal, sixVertexHorizontalActualDeficitPair,
      hprofile] using source.1.2.2.2
  invFun target := by
    let horizontal := target.1
    let profile := sixVertexHorizontalPairCompletionProfile T horizontal.1
    let source : SixVertexHorizontalActualDeficitTokens T grade
        sourceLeft sourceRight targetLeft targetRight :=
      ⟨profile,
        (⟨⟨horizontal.1, horizontal.2.1⟩, rfl⟩, target.2)⟩
    refine ⟨source, ?_⟩
    simpa [source, horizontal,
      sixVertexHorizontalActualDeficitRowProfile,
      sixVertexHorizontalActualDeficitPair] using horizontal.2.2
  left_inv source := by
    apply Subtype.ext
    rcases source with ⟨⟨profile, ⟨horizontal, hprofile⟩, index⟩, hrow⟩
    dsimp only
    subst profile
    rfl
  right_inv target := by
    rcases target with ⟨horizontal, index⟩
    rfl

noncomputable def sixVertexHorizontalActualSurplusRowProfileEquiv
    (T : EvenTorus) (grade : Nat × Nat)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (rowProfile : SixVertexHorizontalRowZeroProfile T) :
    {target : SixVertexHorizontalActualSurplusTokens T grade
        sourceLeft sourceRight targetLeft targetRight //
      sixVertexHorizontalActualSurplusRowProfile target = rowProfile} ≃
      Sigma fun horizontal :
          SixVertexHorizontalPairRowBigradeFiber T grade rowProfile =>
        Fin (sixVertexHorizontalProfileSurplus
          sourceLeft sourceRight targetLeft targetRight
          (sixVertexHorizontalPairCompletionProfile T horizontal.1)) where
  toFun target := by
    let horizontal : SixVertexHorizontalPairRowBigradeFiber
        T grade rowProfile :=
      ⟨sixVertexHorizontalActualSurplusPair target.1,
        sixVertexHorizontalActualSurplusPair_bigrade target.1,
        target.2⟩
    refine ⟨horizontal, target.1.2.2.1, ?_⟩
    have hprofile := target.1.2.1.2
    simpa [horizontal, sixVertexHorizontalActualSurplusPair,
      hprofile] using target.1.2.2.2
  invFun source := by
    let horizontal := source.1
    let profile := sixVertexHorizontalPairCompletionProfile T horizontal.1
    let target : SixVertexHorizontalActualSurplusTokens T grade
        sourceLeft sourceRight targetLeft targetRight :=
      ⟨profile,
        (⟨⟨horizontal.1, horizontal.2.1⟩, rfl⟩, source.2)⟩
    refine ⟨target, ?_⟩
    simpa [target, horizontal,
      sixVertexHorizontalActualSurplusRowProfile,
      sixVertexHorizontalActualSurplusPair] using horizontal.2.2
  left_inv target := by
    apply Subtype.ext
    rcases target with ⟨⟨profile, ⟨horizontal, hprofile⟩, index⟩, hrow⟩
    dsimp only
    subst profile
    rfl
  right_inv source := by
    rcases source with ⟨horizontal, index⟩
    rfl

theorem card_sixVertexHorizontalActualDeficitRowProfileFiber
    (T : EvenTorus) (grade : Nat × Nat)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (rowProfile : SixVertexHorizontalRowZeroProfile T) :
    Fintype.card
        {source : SixVertexHorizontalActualDeficitTokens T grade
            sourceLeft sourceRight targetLeft targetRight //
          sixVertexHorizontalActualDeficitRowProfile source = rowProfile} =
      ∑ horizontal : SixVertexHorizontalPairRowBigradeFiber
          T grade rowProfile,
        sixVertexHorizontalProfileDeficit
          sourceLeft sourceRight targetLeft targetRight
          (sixVertexHorizontalPairCompletionProfile T horizontal.1) := by
  rw [Fintype.card_congr
    (sixVertexHorizontalActualDeficitRowProfileEquiv T grade
      sourceLeft sourceRight targetLeft targetRight rowProfile),
    Fintype.card_sigma]
  simp

theorem card_sixVertexHorizontalActualSurplusRowProfileFiber
    (T : EvenTorus) (grade : Nat × Nat)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (rowProfile : SixVertexHorizontalRowZeroProfile T) :
    Fintype.card
        {target : SixVertexHorizontalActualSurplusTokens T grade
            sourceLeft sourceRight targetLeft targetRight //
          sixVertexHorizontalActualSurplusRowProfile target = rowProfile} =
      ∑ horizontal : SixVertexHorizontalPairRowBigradeFiber
          T grade rowProfile,
        sixVertexHorizontalProfileSurplus
          sourceLeft sourceRight targetLeft targetRight
          (sixVertexHorizontalPairCompletionProfile T horizontal.1) := by
  rw [Fintype.card_congr
    (sixVertexHorizontalActualSurplusRowProfileEquiv T grade
      sourceLeft sourceRight targetLeft targetRight rowProfile),
    Fintype.card_sigma]
  simp

def SixVertexHorizontalRowProfileAggregateSignedNonnegative
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    Prop :=
  forall grade (rowProfile : SixVertexHorizontalRowZeroProfile T),
    0 <= ∑ horizontal :
        SixVertexHorizontalPairRowBigradeFiber T grade rowProfile,
      sixVertexHorizontalProfileSignedKernel
        sourceLeft sourceRight targetLeft targetRight
        (sixVertexHorizontalPairCompletionProfile T horizontal.1)

theorem rowProfileResidualCapacity_iff_signedNonnegative
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    SixVertexHorizontalRowProfileResidualCapacity T
        sourceLeft sourceRight targetLeft targetRight <->
      SixVertexHorizontalRowProfileAggregateSignedNonnegative T
        sourceLeft sourceRight targetLeft targetRight := by
  unfold SixVertexHorizontalRowProfileResidualCapacity
    SixVertexHorizontalRowProfileAggregateSignedNonnegative
  constructor <;> intro h grade rowProfile
  · have hcard := h grade rowProfile
    rw [card_sixVertexHorizontalActualDeficitRowProfileFiber,
      card_sixVertexHorizontalActualSurplusRowProfileFiber] at hcard
    have hsplit :
        (∑ horizontal : SixVertexHorizontalPairRowBigradeFiber
          T grade rowProfile,
          sixVertexHorizontalProfileSignedKernel
            sourceLeft sourceRight targetLeft targetRight
            (sixVertexHorizontalPairCompletionProfile T horizontal.1)) =
        (∑ horizontal : SixVertexHorizontalPairRowBigradeFiber
          T grade rowProfile,
          (sixVertexHorizontalProfileSurplus
            sourceLeft sourceRight targetLeft targetRight
            (sixVertexHorizontalPairCompletionProfile T horizontal.1) : Int)) -
        ∑ horizontal : SixVertexHorizontalPairRowBigradeFiber
          T grade rowProfile,
          (sixVertexHorizontalProfileDeficit
            sourceLeft sourceRight targetLeft targetRight
            (sixVertexHorizontalPairCompletionProfile T horizontal.1) : Int) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro horizontal hhorizontal
      unfold sixVertexHorizontalProfileSignedKernel
        sixVertexHorizontalProfileSurplus
        sixVertexHorizontalProfileDeficit
      exact (Int.toNat_sub_toNat_neg _).symm
    rw [hsplit]
    have hcard' :
        (∑ horizontal : SixVertexHorizontalPairRowBigradeFiber
          T grade rowProfile,
          (sixVertexHorizontalProfileDeficit
            sourceLeft sourceRight targetLeft targetRight
            (sixVertexHorizontalPairCompletionProfile T horizontal.1) : Int)) <=
        ∑ horizontal : SixVertexHorizontalPairRowBigradeFiber
          T grade rowProfile,
          (sixVertexHorizontalProfileSurplus
            sourceLeft sourceRight targetLeft targetRight
            (sixVertexHorizontalPairCompletionProfile T horizontal.1) : Int) := by
      exact_mod_cast hcard
    omega
  · rw [card_sixVertexHorizontalActualDeficitRowProfileFiber,
      card_sixVertexHorizontalActualSurplusRowProfileFiber]
    have hsigned := h grade rowProfile
    have hsplit :
        (∑ horizontal : SixVertexHorizontalPairRowBigradeFiber
          T grade rowProfile,
          sixVertexHorizontalProfileSignedKernel
            sourceLeft sourceRight targetLeft targetRight
            (sixVertexHorizontalPairCompletionProfile T horizontal.1)) =
        (∑ horizontal : SixVertexHorizontalPairRowBigradeFiber
          T grade rowProfile,
          (sixVertexHorizontalProfileSurplus
            sourceLeft sourceRight targetLeft targetRight
            (sixVertexHorizontalPairCompletionProfile T horizontal.1) : Int)) -
        ∑ horizontal : SixVertexHorizontalPairRowBigradeFiber
          T grade rowProfile,
          (sixVertexHorizontalProfileDeficit
            sourceLeft sourceRight targetLeft targetRight
            (sixVertexHorizontalPairCompletionProfile T horizontal.1) : Int) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro horizontal hhorizontal
      unfold sixVertexHorizontalProfileSignedKernel
        sixVertexHorizontalProfileSurplus
        sixVertexHorizontalProfileDeficit
      exact (Int.toNat_sub_toNat_neg _).symm
    rw [hsplit] at hsigned
    have hcard :
      (∑ horizontal : SixVertexHorizontalPairRowBigradeFiber
        T grade rowProfile,
        (sixVertexHorizontalProfileDeficit
          sourceLeft sourceRight targetLeft targetRight
          (sixVertexHorizontalPairCompletionProfile T horizontal.1) : Int)) <=
      ∑ horizontal : SixVertexHorizontalPairRowBigradeFiber
        T grade rowProfile,
        (sixVertexHorizontalProfileSurplus
          sourceLeft sourceRight targetLeft targetRight
          (sixVertexHorizontalPairCompletionProfile T horizontal.1) : Int) := by
      omega
    exact_mod_cast hcard



theorem configurationBigradeFibers_of_rowProfileSignedNonnegative
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (hsigned : SixVertexHorizontalRowProfileAggregateSignedNonnegative T
      sourceLeft sourceRight targetLeft targetRight) :
    SixVertexConfigurationPairBigradeFiberDominates T
      sourceLeft sourceRight targetLeft targetRight := by
  apply configurationBigradeFibers_of_rowProfileResidualCapacity T
  exact (rowProfileResidualCapacity_iff_signedNonnegative T
    sourceLeft sourceRight targetLeft targetRight).mpr hsigned



theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_rowProfileSigned
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hsigned : SixVertexHorizontalRowProfileAggregateSignedNonnegative T
      ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩
      middle middle) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_configurationBigradeFibers
    T middle hmiddle_pos hmiddle_lt
      (configurationBigradeFibers_of_rowProfileSignedNonnegative T
        ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩
        middle middle hsigned)

end

end StatMech.FrontierD
