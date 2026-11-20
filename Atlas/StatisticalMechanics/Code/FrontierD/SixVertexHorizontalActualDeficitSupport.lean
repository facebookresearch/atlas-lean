/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexHorizontalProfileDeficitSupport









open Finset

namespace StatMech.FrontierD

noncomputable section

local instance sixVertexHorizontalActualDeficitSupportPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p

abbrev SixVertexHorizontalPairProfileFiber
    (T : EvenTorus) (grade : Nat × Nat)
    (profile : SixVertexHorizontalPairCompletionProfile T) :=
  {horizontal :
      {horizontal : SixVertexHorizontalField T ×
          SixVertexHorizontalField T //
        sixVertexHorizontalPairBigrade horizontal = grade} //
    sixVertexHorizontalPairCompletionProfile T horizontal.1 = profile}

theorem card_sixVertexHorizontalPairProfileFiber
    (T : EvenTorus) (grade : Nat × Nat)
    (profile : SixVertexHorizontalPairCompletionProfile T) :
    Fintype.card (SixVertexHorizontalPairProfileFiber T grade profile) =
      sixVertexHorizontalPairProfileMultiplicity T grade profile := by
  rfl

abbrev SixVertexHorizontalActualDeficitTokens
    (T : EvenTorus) (grade : Nat × Nat)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :=
  Sigma fun profile : SixVertexHorizontalPairCompletionProfile T =>
    SixVertexHorizontalPairProfileFiber T grade profile ×
      Fin (sixVertexHorizontalProfileDeficit
        sourceLeft sourceRight targetLeft targetRight profile)

abbrev SixVertexHorizontalActualSurplusTokens
    (T : EvenTorus) (grade : Nat × Nat)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :=
  Sigma fun profile : SixVertexHorizontalPairCompletionProfile T =>
    SixVertexHorizontalPairProfileFiber T grade profile ×
      Fin (sixVertexHorizontalProfileSurplus
        sourceLeft sourceRight targetLeft targetRight profile)

def sixVertexHorizontalActualDeficitPair
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (token : SixVertexHorizontalActualDeficitTokens T grade
      sourceLeft sourceRight targetLeft targetRight) :
    SixVertexHorizontalField T × SixVertexHorizontalField T :=
  token.2.1.1.1

def sixVertexHorizontalActualSurplusPair
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (token : SixVertexHorizontalActualSurplusTokens T grade
      sourceLeft sourceRight targetLeft targetRight) :
    SixVertexHorizontalField T × SixVertexHorizontalField T :=
  token.2.1.1.1

@[simp] theorem sixVertexHorizontalActualDeficitPair_bigrade
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (token : SixVertexHorizontalActualDeficitTokens T grade
      sourceLeft sourceRight targetLeft targetRight) :
    sixVertexHorizontalPairBigrade
        (sixVertexHorizontalActualDeficitPair token) = grade :=
  token.2.1.1.2

@[simp] theorem sixVertexHorizontalActualSurplusPair_bigrade
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (token : SixVertexHorizontalActualSurplusTokens T grade
      sourceLeft sourceRight targetLeft targetRight) :
    sixVertexHorizontalPairBigrade
        (sixVertexHorizontalActualSurplusPair token) = grade :=
  token.2.1.1.2

theorem card_sixVertexHorizontalActualDeficitTokens
    (T : EvenTorus) (grade : Nat × Nat)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    Fintype.card (SixVertexHorizontalActualDeficitTokens T grade
      sourceLeft sourceRight targetLeft targetRight) =
      Fintype.card (SixVertexHorizontalProfileDeficitTokens T grade
        sourceLeft sourceRight targetLeft targetRight) := by
  rw [Fintype.card_sigma, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro profile hprofile
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    card_sixVertexHorizontalPairProfileFiber]

theorem card_sixVertexHorizontalActualSurplusTokens
    (T : EvenTorus) (grade : Nat × Nat)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    Fintype.card (SixVertexHorizontalActualSurplusTokens T grade
      sourceLeft sourceRight targetLeft targetRight) =
      Fintype.card (SixVertexHorizontalProfileSurplusTokens T grade
        sourceLeft sourceRight targetLeft targetRight) := by
  rw [Fintype.card_sigma, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro profile hprofile
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    card_sixVertexHorizontalPairProfileFiber]

theorem profileSignedNonnegative_iff_actualDeficitEmbeddings
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    SixVertexHorizontalProfileAggregateSignedNonnegative T
        sourceLeft sourceRight targetLeft targetRight ↔
      forall grade, Nonempty
        (SixVertexHorizontalActualDeficitTokens T grade
            sourceLeft sourceRight targetLeft targetRight ↪
          SixVertexHorizontalActualSurplusTokens T grade
            sourceLeft sourceRight targetLeft targetRight) := by
  rw [profileSignedNonnegative_iff_deficit_le_surplus]
  constructor
  · intro hcard grade
    apply Function.Embedding.nonempty_of_card_le
    rw [card_sixVertexHorizontalActualDeficitTokens,
      card_sixVertexHorizontalActualSurplusTokens]
    exact hcard grade
  · intro hemb grade
    rw [← card_sixVertexHorizontalActualDeficitTokens,
      ← card_sixVertexHorizontalActualSurplusTokens]
    exact Function.Embedding.nonempty_iff_card_le.mp (hemb grade)

def SixVertexHorizontalActualDeficitTokenHall
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (support : forall grade,
      SixVertexHorizontalActualDeficitTokens T grade
          sourceLeft sourceRight targetLeft targetRight ->
        SixVertexHorizontalActualSurplusTokens T grade
          sourceLeft sourceRight targetLeft targetRight -> Prop) : Prop :=
  forall grade
    (A : Finset (SixVertexHorizontalActualDeficitTokens T grade
      sourceLeft sourceRight targetLeft targetRight)),
    A.card <=
      ((Finset.univ.filter fun target =>
        Exists fun source => source ∈ A ∧ support grade source target)).card

def SixVertexHorizontalActualDeficitSupportedMatching
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (support : forall grade,
      SixVertexHorizontalActualDeficitTokens T grade
          sourceLeft sourceRight targetLeft targetRight ->
        SixVertexHorizontalActualSurplusTokens T grade
          sourceLeft sourceRight targetLeft targetRight -> Prop) : Prop :=
  forall grade, Exists fun matching :
      SixVertexHorizontalActualDeficitTokens T grade
          sourceLeft sourceRight targetLeft targetRight ->
        SixVertexHorizontalActualSurplusTokens T grade
          sourceLeft sourceRight targetLeft targetRight =>
    Function.Injective matching ∧
      forall source, support grade source (matching source)

theorem actualDeficitTokenHall_iff_supportedMatching
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (support : forall grade,
      SixVertexHorizontalActualDeficitTokens T grade
          sourceLeft sourceRight targetLeft targetRight ->
        SixVertexHorizontalActualSurplusTokens T grade
          sourceLeft sourceRight targetLeft targetRight -> Prop) :
    SixVertexHorizontalActualDeficitTokenHall T
        sourceLeft sourceRight targetLeft targetRight support ↔
      SixVertexHorizontalActualDeficitSupportedMatching T
        sourceLeft sourceRight targetLeft targetRight support := by
  constructor
  · intro hHall grade
    exact (Fintype.all_card_le_filter_rel_iff_exists_injective
      (support grade)).mp (hHall grade)
  · intro hmatching grade
    exact (Fintype.all_card_le_filter_rel_iff_exists_injective
      (support grade)).mpr (hmatching grade)

theorem configurationBigradeFibers_of_actualDeficitTokenHall
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (support : forall grade,
      SixVertexHorizontalActualDeficitTokens T grade
          sourceLeft sourceRight targetLeft targetRight ->
        SixVertexHorizontalActualSurplusTokens T grade
          sourceLeft sourceRight targetLeft targetRight -> Prop)
    (hHall : SixVertexHorizontalActualDeficitTokenHall T
      sourceLeft sourceRight targetLeft targetRight support) :
    SixVertexConfigurationPairBigradeFiberDominates T
      sourceLeft sourceRight targetLeft targetRight := by
  rw [configurationBigradeFibers_iff_horizontalChooseBigradeFibers,
    horizontalChooseBigradeFibers_iff_profileAggregate,
    profileAggregate_iff_signedNonnegative,
    profileSignedNonnegative_iff_actualDeficitEmbeddings]
  intro grade
  have hmatching :=
    (actualDeficitTokenHall_iff_supportedMatching T
      sourceLeft sourceRight targetLeft targetRight support).mp hHall grade
  rcases hmatching with ⟨matching, hinjective, hsupported⟩
  exact ⟨⟨matching, hinjective⟩⟩

end

end StatMech.FrontierD
