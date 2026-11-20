/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexHorizontalProfileAggregate










open Finset

namespace StatMech.FrontierD

noncomputable section

local instance instDecidablePropHorizontalProfileHall (p : Prop) : Decidable p :=
  Classical.propDecidable p


abbrev SixVertexHorizontalProfileTokens
    (T : EvenTorus) (grade : Nat × Nat)
    (left right : Fin (T.width + 1)) :=
  Sigma fun profile : SixVertexHorizontalPairCompletionProfile T =>
    Fin (sixVertexHorizontalPairProfileMultiplicity T grade profile *
      sixVertexHorizontalPairProfileChooseWeight left right profile)

theorem card_sixVertexHorizontalProfileTokens
    (T : EvenTorus) (grade : Nat × Nat)
    (left right : Fin (T.width + 1)) :
    Fintype.card (SixVertexHorizontalProfileTokens T grade left right) =
      ∑ profile : SixVertexHorizontalPairCompletionProfile T,
        sixVertexHorizontalPairProfileMultiplicity T grade profile *
          sixVertexHorizontalPairProfileChooseWeight left right profile := by
  rw [Fintype.card_sigma]
  simp



theorem profileAggregate_iff_tokenEmbeddings
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    SixVertexHorizontalProfileAggregateDominates T
        sourceLeft sourceRight targetLeft targetRight ↔
      forall grade, Nonempty
        (SixVertexHorizontalProfileTokens T grade sourceLeft sourceRight ↪
          SixVertexHorizontalProfileTokens T grade targetLeft targetRight) := by
  unfold SixVertexHorizontalProfileAggregateDominates
  constructor
  · intro hdom grade
    apply Function.Embedding.nonempty_of_card_le
    rw [card_sixVertexHorizontalProfileTokens,
      card_sixVertexHorizontalProfileTokens]
    exact hdom grade
  · intro hemb grade
    rw [<- card_sixVertexHorizontalProfileTokens,
      <- card_sixVertexHorizontalProfileTokens]
    exact Function.Embedding.nonempty_iff_card_le.mp (hemb grade)



def SixVertexHorizontalProfileTokenHall
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (support : forall grade,
      SixVertexHorizontalProfileTokens T grade sourceLeft sourceRight ->
        SixVertexHorizontalProfileTokens T grade targetLeft targetRight -> Prop) :
    Prop :=
  forall grade
    (A : Finset
      (SixVertexHorizontalProfileTokens T grade sourceLeft sourceRight)),
    A.card <=
      ((Finset.univ.filter fun target =>
        Exists fun source => source ∈ A ∧ support grade source target)).card



theorem profileAggregate_of_tokenHall
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (support : forall grade,
      SixVertexHorizontalProfileTokens T grade sourceLeft sourceRight ->
        SixVertexHorizontalProfileTokens T grade targetLeft targetRight -> Prop)
    (hHall : SixVertexHorizontalProfileTokenHall T
      sourceLeft sourceRight targetLeft targetRight support) :
    SixVertexHorizontalProfileAggregateDominates T
      sourceLeft sourceRight targetLeft targetRight := by
  rw [profileAggregate_iff_tokenEmbeddings]
  intro grade
  have hmatching :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective
      (support grade)).mp (hHall grade)
  rcases hmatching with ⟨f, hinjective, hsupported⟩
  exact ⟨⟨f, hinjective⟩⟩

end

end StatMech.FrontierD
