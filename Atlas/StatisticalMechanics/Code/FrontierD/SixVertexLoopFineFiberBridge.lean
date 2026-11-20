/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexLoopDecoratedUnitTransfer
import Code.FrontierD.SixVertexPairTwoCycleCompletionHall
import Code.FrontierD.SixVertexHorizontalFineFiberFactorization
import Code.FrontierA.GrahamCanonicalEdgeDegreeHall











namespace StatMech.FrontierD

noncomputable section

local instance sixVertexLoopFineFiberBridgePropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p



abbrev SixVertexLoopDecoratedPairFineProfileFiber
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (profile : SixVertexHorizontalBoundedFineRowProfile T) :=
  {decorated : SixVertexLoopDecoratedPair T left right //
    sixVertexHorizontalPairBoundedFineRowProfile
      ((sixVertexLoopDecoratedPairColored decorated false).arrows.horizontal,
        (sixVertexLoopDecoratedPairColored decorated true).arrows.horizontal) =
      profile}

theorem sixVertexConfigurationPairTotalC_eq_fineProfileGrade
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    {profile : SixVertexHorizontalBoundedFineRowProfile T}
    (pair : SixVertexConfigurationPairFineProfileFiber
      T left right profile) :
    sixVertexConfigurationPairTotalC pair.1 =
      (sixVertexHorizontalFineRowProfileGrade profile).1 := by
  have hgrade := sixVertexConfigurationPairBigrade_eq_horizontalPairBigrade
    pair.1
  have hfine := sixVertexHorizontalPairBigrade_eq_fineRowProfileGrade
    (pair.1.1.1.horizontal, pair.1.2.1.horizontal)
  rw [pair.2] at hfine
  exact congrArg Prod.fst (hgrade.trans hfine)



theorem card_sixVertexConfigurationPairFineProfileFiber
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (profile : SixVertexHorizontalBoundedFineRowProfile T) :
    Fintype.card
        (SixVertexConfigurationPairFineProfileFiber T left right profile) =
      sixVertexHorizontalFineRowProfileSectorPairSum
        T left right profile := by
  rw [Fintype.card_congr
    (sixVertexConfigurationPairFineProfileFiberEquivHorizontalCompletions
      T left right profile)]
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_prod,
    card_sixVertexHorizontalSectorCompletion_eq_chooseCount]
  unfold sixVertexHorizontalFineRowProfileSectorPairSum
  rw [← Finset.sum_subtype
    (Finset.univ.filter fun horizontal :
      SixVertexHorizontalField T × SixVertexHorizontalField T =>
        sixVertexHorizontalPairBoundedFineRowProfile horizontal = profile)
    (by simp)
    (fun horizontal =>
      sixVertexHorizontalSectorCompletionChooseCount T left horizontal.1 *
        sixVertexHorizontalSectorCompletionChooseCount T right horizontal.2)]
  rw [Finset.sum_filter]



noncomputable def sixVertexLoopFineProfileFiberEquiv
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (profile : SixVertexHorizontalBoundedFineRowProfile T) :
    SixVertexLoopDecoratedPairFineProfileFiber T left right profile ≃
      (SixVertexConfigurationPairFineProfileFiber T left right profile ×
        Fin (2 ^ (sixVertexHorizontalFineRowProfileGrade profile).1)) where
  toFun decorated :=
    let hprofile : sixVertexHorizontalPairBoundedFineRowProfile
        (decorated.1.1.1.1.horizontal,
          decorated.1.1.2.1.horizontal) = profile := by
      simpa using decorated.2
    let pair : SixVertexConfigurationPairFineProfileFiber
        T left right profile := ⟨decorated.1.1, hprofile⟩
    let htotal := sixVertexConfigurationPairTotalC_eq_fineProfileGrade pair
    (pair, sixVertexCompatibleLoopPairingPairEquivFin
      pair.1 (sixVertexHorizontalFineRowProfileGrade profile).1 htotal
      decorated.1.2)
  invFun decorated :=
    let htotal := sixVertexConfigurationPairTotalC_eq_fineProfileGrade
      decorated.1
    ⟨⟨decorated.1.1,
        (sixVertexCompatibleLoopPairingPairEquivFin decorated.1.1
          (sixVertexHorizontalFineRowProfileGrade profile).1 htotal).symm
          decorated.2⟩,
      by simpa using decorated.1.2⟩
  left_inv decorated := by
    apply Subtype.ext
    apply Sigma.ext
    · rfl
    · simp
  right_inv decorated := by
    apply Prod.ext
    · rfl
    · simp

theorem card_sixVertexLoopDecoratedPairFineProfileFiber
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (profile : SixVertexHorizontalBoundedFineRowProfile T) :
    Fintype.card
        (SixVertexLoopDecoratedPairFineProfileFiber T left right profile) =
      sixVertexHorizontalFineRowProfileSectorPairSum T left right profile *
        2 ^ (sixVertexHorizontalFineRowProfileGrade profile).1 := by
  rw [Fintype.card_congr
    (sixVertexLoopFineProfileFiberEquiv T left right profile)]
  rw [Fintype.card_prod,
    card_sixVertexConfigurationPairFineProfileFiber]
  simp


def SixVertexLoopDecoratedPairFineProfileFiberDominates
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    Prop :=
  forall profile : SixVertexHorizontalBoundedFineRowProfile T,
    Fintype.card (SixVertexLoopDecoratedPairFineProfileFiber
      T sourceLeft sourceRight profile) <=
    Fintype.card (SixVertexLoopDecoratedPairFineProfileFiber
      T targetLeft targetRight profile)




theorem loopFineProfileFibers_of_relationEdgeDegree
    {T : EvenTorus}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (related : forall profile : SixVertexHorizontalBoundedFineRowProfile T,
      SixVertexLoopDecoratedPairFineProfileFiber
          T sourceLeft sourceRight profile ->
        SixVertexLoopDecoratedPairFineProfileFiber
          T targetLeft targetRight profile -> Prop)
    (hne : forall profile source,
      (Finset.univ.filter (related profile source)).Nonempty)
    (hdegree : forall profile source target,
      related profile source target ->
        (Finset.univ.filter fun otherSource =>
          related profile otherSource target).card <=
        (Finset.univ.filter (related profile source)).card) :
    SixVertexLoopDecoratedPairFineProfileFiberDominates T
      sourceLeft sourceRight targetLeft targetRight := by
  intro profile
  classical
  let sources : Finset (SixVertexLoopDecoratedPairFineProfileFiber
      T sourceLeft sourceRight profile) := Finset.univ
  have hHall := StatMech.FrontierA.card_le_bipartiteNeighbors_of_edgeDegree
    (related profile) sources
    (fun source _ => hne profile source)
    (fun source _ target hrelated =>
      hdegree profile source target hrelated)
  calc
    Fintype.card (SixVertexLoopDecoratedPairFineProfileFiber
        T sourceLeft sourceRight profile) = sources.card := by simp [sources]
    _ <= (Finset.univ.filter fun target =>
        ∃ source ∈ sources, related profile source target).card := hHall
    _ <= Fintype.card (SixVertexLoopDecoratedPairFineProfileFiber
        T targetLeft targetRight profile) := by
      simpa only [Finset.card_univ] using Finset.card_le_univ
        (Finset.univ.filter fun target =>
          ∃ source ∈ sources, related profile source target)



theorem rawFineProfile_of_loopFineProfileFibers
    {T : EvenTorus}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (hfiber : SixVertexLoopDecoratedPairFineProfileFiberDominates T
      sourceLeft sourceRight targetLeft targetRight) :
    forall profile : SixVertexHorizontalBoundedFineRowProfile T,
      0 <= sixVertexHorizontalFineRowProfileSignedSum T
        sourceLeft sourceRight targetLeft targetRight profile := by
  intro profile
  have hcard := hfiber profile
  rw [card_sixVertexLoopDecoratedPairFineProfileFiber,
    card_sixVertexLoopDecoratedPairFineProfileFiber] at hcard
  have hraw : sixVertexHorizontalFineRowProfileSectorPairSum
      T sourceLeft sourceRight profile <=
      sixVertexHorizontalFineRowProfileSectorPairSum
        T targetLeft targetRight profile := by
    exact Nat.le_of_mul_le_mul_right hcard (by positivity)
  unfold sixVertexHorizontalFineRowProfileSignedSum
  exact sub_nonneg.mpr (by exact_mod_cast hraw)



theorem rawFineProfile_of_loopRelationEdgeDegree
    {T : EvenTorus}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (related : forall profile : SixVertexHorizontalBoundedFineRowProfile T,
      SixVertexLoopDecoratedPairFineProfileFiber
          T sourceLeft sourceRight profile ->
        SixVertexLoopDecoratedPairFineProfileFiber
          T targetLeft targetRight profile -> Prop)
    (hne : forall profile source,
      (Finset.univ.filter (related profile source)).Nonempty)
    (hdegree : forall profile source target,
      related profile source target ->
        (Finset.univ.filter fun otherSource =>
          related profile otherSource target).card <=
        (Finset.univ.filter (related profile source)).card) :
    forall profile : SixVertexHorizontalBoundedFineRowProfile T,
      0 <= sixVertexHorizontalFineRowProfileSignedSum T
        sourceLeft sourceRight targetLeft targetRight profile :=
  rawFineProfile_of_loopFineProfileFibers
    (loopFineProfileFibers_of_relationEdgeDegree related hne hdegree)



theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_loopFineProfileFibers
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hfiber : SixVertexLoopDecoratedPairFineProfileFiberDominates T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val := by
  apply sixVertexMarkedTraceCoefficientwiseLogConcave_of_rawFineProfile
    T middle hmiddle_pos hmiddle_lt
  exact rawFineProfile_of_loopFineProfileFibers hfiber

end

end StatMech.FrontierD
