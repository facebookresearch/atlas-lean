/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexHorizontalProfileDeficitHall








open Finset

namespace StatMech.FrontierD

noncomputable section

local instance sixVertexHorizontalProfileDeficitSupportPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p

def SixVertexHorizontalProfileDeficitTokenHall
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (support : forall grade,
      SixVertexHorizontalProfileDeficitTokens T grade
          sourceLeft sourceRight targetLeft targetRight ->
        SixVertexHorizontalProfileSurplusTokens T grade
          sourceLeft sourceRight targetLeft targetRight -> Prop) : Prop :=
  forall grade
    (A : Finset (SixVertexHorizontalProfileDeficitTokens T grade
      sourceLeft sourceRight targetLeft targetRight)),
    A.card <=
      ((Finset.univ.filter fun target =>
        Exists fun source => source ∈ A ∧ support grade source target)).card

def SixVertexHorizontalProfileDeficitSupportedMatching
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (support : forall grade,
      SixVertexHorizontalProfileDeficitTokens T grade
          sourceLeft sourceRight targetLeft targetRight ->
        SixVertexHorizontalProfileSurplusTokens T grade
          sourceLeft sourceRight targetLeft targetRight -> Prop) : Prop :=
  forall grade, Exists fun matching :
      SixVertexHorizontalProfileDeficitTokens T grade
          sourceLeft sourceRight targetLeft targetRight ->
        SixVertexHorizontalProfileSurplusTokens T grade
          sourceLeft sourceRight targetLeft targetRight =>
    Function.Injective matching ∧
      forall source, support grade source (matching source)

theorem deficitTokenHall_iff_supportedMatching
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (support : forall grade,
      SixVertexHorizontalProfileDeficitTokens T grade
          sourceLeft sourceRight targetLeft targetRight ->
        SixVertexHorizontalProfileSurplusTokens T grade
          sourceLeft sourceRight targetLeft targetRight -> Prop) :
    SixVertexHorizontalProfileDeficitTokenHall T
        sourceLeft sourceRight targetLeft targetRight support ↔
      SixVertexHorizontalProfileDeficitSupportedMatching T
        sourceLeft sourceRight targetLeft targetRight support := by
  constructor
  · intro hHall grade
    exact (Fintype.all_card_le_filter_rel_iff_exists_injective
      (support grade)).mp (hHall grade)
  · intro hmatching grade
    exact (Fintype.all_card_le_filter_rel_iff_exists_injective
      (support grade)).mpr (hmatching grade)

theorem horizontalChooseBigradeFibers_of_deficitTokenHall
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (support : forall grade,
      SixVertexHorizontalProfileDeficitTokens T grade
          sourceLeft sourceRight targetLeft targetRight ->
        SixVertexHorizontalProfileSurplusTokens T grade
          sourceLeft sourceRight targetLeft targetRight -> Prop)
    (hHall : SixVertexHorizontalProfileDeficitTokenHall T
      sourceLeft sourceRight targetLeft targetRight support) :
    SixVertexHorizontalChooseBigradeFiberDominates T
      sourceLeft sourceRight targetLeft targetRight := by
  rw [horizontalChooseBigradeFibers_iff_profileAggregate,
    profileAggregate_iff_signedNonnegative,
    profileSignedNonnegative_iff_deficitEmbeddings]
  intro grade
  have hmatching :=
    (deficitTokenHall_iff_supportedMatching T
      sourceLeft sourceRight targetLeft targetRight support).mp hHall grade
  rcases hmatching with ⟨matching, hinjective, hsupported⟩
  exact ⟨⟨matching, hinjective⟩⟩

theorem configurationBigradeFibers_of_deficitTokenHall
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (support : forall grade,
      SixVertexHorizontalProfileDeficitTokens T grade
          sourceLeft sourceRight targetLeft targetRight ->
        SixVertexHorizontalProfileSurplusTokens T grade
          sourceLeft sourceRight targetLeft targetRight -> Prop)
    (hHall : SixVertexHorizontalProfileDeficitTokenHall T
      sourceLeft sourceRight targetLeft targetRight support) :
    SixVertexConfigurationPairBigradeFiberDominates T
      sourceLeft sourceRight targetLeft targetRight := by
  rw [configurationBigradeFibers_iff_horizontalChooseBigradeFibers]
  exact horizontalChooseBigradeFibers_of_deficitTokenHall T
    sourceLeft sourceRight targetLeft targetRight support hHall

end

end StatMech.FrontierD
