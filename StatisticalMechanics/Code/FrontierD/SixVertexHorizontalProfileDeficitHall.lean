/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexHorizontalProfileLayerSymmetry









open Finset

namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalProfileDeficit
    {T : EvenTorus}
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (profile : SixVertexHorizontalPairCompletionProfile T) : Nat :=
  (-sixVertexHorizontalProfileSignedKernel
    sourceLeft sourceRight targetLeft targetRight profile).toNat

def sixVertexHorizontalProfileSurplus
    {T : EvenTorus}
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (profile : SixVertexHorizontalPairCompletionProfile T) : Nat :=
  (sixVertexHorizontalProfileSignedKernel
    sourceLeft sourceRight targetLeft targetRight profile).toNat

abbrev SixVertexHorizontalProfileDeficitTokens
    (T : EvenTorus) (grade : Nat × Nat)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :=
  Sigma fun profile : SixVertexHorizontalPairCompletionProfile T =>
    Fin (sixVertexHorizontalPairProfileMultiplicity T grade profile *
      sixVertexHorizontalProfileDeficit
        sourceLeft sourceRight targetLeft targetRight profile)

abbrev SixVertexHorizontalProfileSurplusTokens
    (T : EvenTorus) (grade : Nat × Nat)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :=
  Sigma fun profile : SixVertexHorizontalPairCompletionProfile T =>
    Fin (sixVertexHorizontalPairProfileMultiplicity T grade profile *
      sixVertexHorizontalProfileSurplus
        sourceLeft sourceRight targetLeft targetRight profile)

theorem card_sixVertexHorizontalProfileDeficitTokens
    (T : EvenTorus) (grade : Nat × Nat)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    Fintype.card (SixVertexHorizontalProfileDeficitTokens T grade
      sourceLeft sourceRight targetLeft targetRight) =
      ∑ profile : SixVertexHorizontalPairCompletionProfile T,
        sixVertexHorizontalPairProfileMultiplicity T grade profile *
          sixVertexHorizontalProfileDeficit
            sourceLeft sourceRight targetLeft targetRight profile := by
  rw [Fintype.card_sigma]
  simp

theorem card_sixVertexHorizontalProfileSurplusTokens
    (T : EvenTorus) (grade : Nat × Nat)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    Fintype.card (SixVertexHorizontalProfileSurplusTokens T grade
      sourceLeft sourceRight targetLeft targetRight) =
      ∑ profile : SixVertexHorizontalPairCompletionProfile T,
        sixVertexHorizontalPairProfileMultiplicity T grade profile *
          sixVertexHorizontalProfileSurplus
            sourceLeft sourceRight targetLeft targetRight profile := by
  rw [Fintype.card_sigma]
  simp

theorem profileSignedNonnegative_iff_deficit_le_surplus
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    SixVertexHorizontalProfileAggregateSignedNonnegative T
        sourceLeft sourceRight targetLeft targetRight ↔
      forall grade,
        Fintype.card (SixVertexHorizontalProfileDeficitTokens T grade
          sourceLeft sourceRight targetLeft targetRight) <=
        Fintype.card (SixVertexHorizontalProfileSurplusTokens T grade
          sourceLeft sourceRight targetLeft targetRight) := by
  unfold SixVertexHorizontalProfileAggregateSignedNonnegative
  constructor <;> intro hsign grade
  · rw [card_sixVertexHorizontalProfileDeficitTokens,
      card_sixVertexHorizontalProfileSurplusTokens]
    have hsum := hsign grade
    have hsplit :
        (∑ profile : SixVertexHorizontalPairCompletionProfile T,
          (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
            sixVertexHorizontalProfileSignedKernel
              sourceLeft sourceRight targetLeft targetRight profile) =
        (∑ profile : SixVertexHorizontalPairCompletionProfile T,
          (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
            (sixVertexHorizontalProfileSurplus
              sourceLeft sourceRight targetLeft targetRight profile : Int)) -
        ∑ profile : SixVertexHorizontalPairCompletionProfile T,
          (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
            (sixVertexHorizontalProfileDeficit
              sourceLeft sourceRight targetLeft targetRight profile : Int) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro profile hprofile
      unfold sixVertexHorizontalProfileSurplus
        sixVertexHorizontalProfileDeficit
      let k := sixVertexHorizontalProfileSignedKernel
        sourceLeft sourceRight targetLeft targetRight profile
      change (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) * k =
        (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
            (k.toNat : Int) -
          (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
            ((-k).toNat : Int)
      rw [← mul_sub, Int.toNat_sub_toNat_neg]
    rw [hsplit] at hsum
    have hsum' :
        (∑ profile : SixVertexHorizontalPairCompletionProfile T,
          (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
            (sixVertexHorizontalProfileDeficit
              sourceLeft sourceRight targetLeft targetRight profile : Int)) <=
        ∑ profile : SixVertexHorizontalPairCompletionProfile T,
          (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
            (sixVertexHorizontalProfileSurplus
              sourceLeft sourceRight targetLeft targetRight profile : Int) := by
      omega
    exact_mod_cast hsum'
  · have hcard := hsign grade
    rw [card_sixVertexHorizontalProfileDeficitTokens,
      card_sixVertexHorizontalProfileSurplusTokens] at hcard
    have hsplit :
        (∑ profile : SixVertexHorizontalPairCompletionProfile T,
          (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
            sixVertexHorizontalProfileSignedKernel
              sourceLeft sourceRight targetLeft targetRight profile) =
        (∑ profile : SixVertexHorizontalPairCompletionProfile T,
          (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
            (sixVertexHorizontalProfileSurplus
              sourceLeft sourceRight targetLeft targetRight profile : Int)) -
        ∑ profile : SixVertexHorizontalPairCompletionProfile T,
          (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
            (sixVertexHorizontalProfileDeficit
              sourceLeft sourceRight targetLeft targetRight profile : Int) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro profile hprofile
      unfold sixVertexHorizontalProfileSurplus
        sixVertexHorizontalProfileDeficit
      let k := sixVertexHorizontalProfileSignedKernel
        sourceLeft sourceRight targetLeft targetRight profile
      change (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) * k =
        (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
            (k.toNat : Int) -
          (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
            ((-k).toNat : Int)
      rw [← mul_sub, Int.toNat_sub_toNat_neg]
    rw [hsplit]
    have hcard' :
        (∑ profile : SixVertexHorizontalPairCompletionProfile T,
          (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
            (sixVertexHorizontalProfileDeficit
              sourceLeft sourceRight targetLeft targetRight profile : Int)) <=
        ∑ profile : SixVertexHorizontalPairCompletionProfile T,
          (sixVertexHorizontalPairProfileMultiplicity T grade profile : Int) *
            (sixVertexHorizontalProfileSurplus
              sourceLeft sourceRight targetLeft targetRight profile : Int) := by
      exact_mod_cast hcard
    omega

theorem profileSignedNonnegative_iff_deficitEmbeddings
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    SixVertexHorizontalProfileAggregateSignedNonnegative T
        sourceLeft sourceRight targetLeft targetRight ↔
      forall grade, Nonempty
        (SixVertexHorizontalProfileDeficitTokens T grade
            sourceLeft sourceRight targetLeft targetRight ↪
          SixVertexHorizontalProfileSurplusTokens T grade
            sourceLeft sourceRight targetLeft targetRight) := by
  rw [profileSignedNonnegative_iff_deficit_le_surplus]
  constructor
  · intro hcard grade
    exact Function.Embedding.nonempty_of_card_le (hcard grade)
  · intro hemb grade
    exact Function.Embedding.nonempty_iff_card_le.mp (hemb grade)

end

end StatMech.FrontierD

