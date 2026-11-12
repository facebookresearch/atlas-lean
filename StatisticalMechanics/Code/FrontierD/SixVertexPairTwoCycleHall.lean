/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexPairTwoCycleRelation
import Code.FrontierD.SixVertexMarkedPairCTypeHall










open Finset

namespace StatMech.FrontierD

noncomputable section

local instance instDecidablePropTwoCycleHall (p : Prop) : Decidable p :=
  Classical.propDecidable p



def SixVertexConfigurationPairTwoCycleFineRelated
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    (source : SixVertexMarkedPairSource T lower upper)
    (target : SixVertexMarkedPairTarget T middle) : Prop :=
  sixVertexPairAtMostTwoCycleFineRelated
    (source.1.1, source.2.1) (target.1.1, target.2.1)

theorem SixVertexConfigurationPairTwoCycleFineRelated.totalC
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    {source : SixVertexMarkedPairSource T lower upper}
    {target : SixVertexMarkedPairTarget T middle}
    (hrelated : SixVertexConfigurationPairTwoCycleFineRelated source target) :
    sixVertexConfigurationPairTotalC source =
      sixVertexConfigurationPairTotalC target := by
  exact sixVertexPairAtMostTwoCycleFineRelated_totalC hrelated



def SixVertexConfigurationPairTwoCycleFineHall
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) : Prop :=
  forall sources : Finset (SixVertexMarkedPairSource T lower upper),
    sources.card <=
      (Finset.univ.filter fun target : SixVertexMarkedPairTarget T middle =>
        ∃ source ∈ sources,
          SixVertexConfigurationPairTwoCycleFineRelated source target).card



theorem configurationPairTwoCycleFineHall_iff_exists_injective
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) :
    SixVertexConfigurationPairTwoCycleFineHall T lower middle upper <->
      exists matching : SixVertexMarkedPairSource T lower upper ->
          SixVertexMarkedPairTarget T middle,
        Function.Injective matching /\
          forall source,
            SixVertexConfigurationPairTwoCycleFineRelated
              source (matching source) := by
  unfold SixVertexConfigurationPairTwoCycleFineHall
  exact Fintype.all_card_le_filter_rel_iff_exists_injective
    SixVertexConfigurationPairTwoCycleFineRelated


abbrev SixVertexConfigurationPairFineProfileFiber
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (profile : SixVertexHorizontalBoundedFineRowProfile T) :=
  {pair : SixVertexMarkedSectorConfiguration T left ×
      SixVertexMarkedSectorConfiguration T right //
    sixVertexHorizontalPairBoundedFineRowProfile
        (pair.1.1.horizontal, pair.2.1.horizontal) = profile}


def SixVertexConfigurationPairTwoCycleFineProfileRelated
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    {profile : SixVertexHorizontalBoundedFineRowProfile T}
    (source : SixVertexConfigurationPairFineProfileFiber
      T lower upper profile)
    (target : SixVertexConfigurationPairFineProfileFiber
      T middle middle profile) : Prop :=
  SixVertexConfigurationPairTwoCycleFineRelated source.1 target.1


def SixVertexConfigurationPairTwoCycleFineProfileFiberHall
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) : Prop :=
  forall profile : SixVertexHorizontalBoundedFineRowProfile T,
    forall sources : Finset
        (SixVertexConfigurationPairFineProfileFiber
          T lower upper profile),
      sources.card <=
        (Finset.univ.filter fun target :
            SixVertexConfigurationPairFineProfileFiber
              T middle middle profile =>
          ∃ source ∈ sources,
            SixVertexConfigurationPairTwoCycleFineProfileRelated
              source target).card



theorem configurationPairTwoCycleFineProfileFiberHall_iff
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) :
    SixVertexConfigurationPairTwoCycleFineProfileFiberHall
        T lower middle upper <->
      forall profile : SixVertexHorizontalBoundedFineRowProfile T,
        exists matching :
            SixVertexConfigurationPairFineProfileFiber
                T lower upper profile ->
              SixVertexConfigurationPairFineProfileFiber
                T middle middle profile,
          Function.Injective matching /\
            forall source,
              SixVertexConfigurationPairTwoCycleFineProfileRelated
                source (matching source) := by
  unfold SixVertexConfigurationPairTwoCycleFineProfileFiberHall
  constructor
  · intro hHall profile
    exact (Fintype.all_card_le_filter_rel_iff_exists_injective
      SixVertexConfigurationPairTwoCycleFineProfileRelated).mp
        (hHall profile)
  · intro hmatching profile
    exact (Fintype.all_card_le_filter_rel_iff_exists_injective
      SixVertexConfigurationPairTwoCycleFineProfileRelated).mpr
        (hmatching profile)



theorem configurationPairTwoCycleFineHall_of_profileFiberHall
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    (hFiber : SixVertexConfigurationPairTwoCycleFineProfileFiberHall
      T lower middle upper) :
    SixVertexConfigurationPairTwoCycleFineHall
      T lower middle upper := by
  let profileOfSource : SixVertexMarkedPairSource T lower upper ->
      SixVertexHorizontalBoundedFineRowProfile T :=
    fun source => sixVertexHorizontalPairBoundedFineRowProfile
      (source.1.1.horizontal, source.2.1.horizontal)
  let profileOfTarget : SixVertexMarkedPairTarget T middle ->
      SixVertexHorizontalBoundedFineRowProfile T :=
    fun target => sixVertexHorizontalPairBoundedFineRowProfile
      (target.1.1.horizontal, target.2.1.horizontal)
  have hmatching :=
    (configurationPairTwoCycleFineProfileFiberHall_iff
      T lower middle upper).mp hFiber
  let fiberEmbedding : forall profile,
      {source : SixVertexMarkedPairSource T lower upper //
          profileOfSource source = profile} ↪
        {target : SixVertexMarkedPairTarget T middle //
          profileOfTarget target = profile} :=
    fun profile =>
      ⟨(hmatching profile).choose,
        (hmatching profile).choose_spec.1⟩
  let gradedEmbedding :
      (Sigma fun profile =>
        {source : SixVertexMarkedPairSource T lower upper //
          profileOfSource source = profile}) ↪
      (Sigma fun profile =>
        {target : SixVertexMarkedPairTarget T middle //
          profileOfTarget target = profile}) :=
    { toFun := fun graded =>
        ⟨graded.1, fiberEmbedding graded.1 graded.2⟩
      inj' := by
        rintro ⟨profile₁, source₁⟩ ⟨profile₂, source₂⟩ heq
        have hprofile : profile₁ = profile₂ := congrArg Sigma.fst heq
        subst profile₂
        have hfiber :
            fiberEmbedding profile₁ source₁ =
              fiberEmbedding profile₁ source₂ := by
          exact eq_of_heq (Sigma.mk.inj heq).2
        have hsource := (fiberEmbedding profile₁).injective hfiber
        cases hsource
        rfl }
  let matchingEmbedding :
      SixVertexMarkedPairSource T lower upper ↪
        SixVertexMarkedPairTarget T middle :=
    (Equiv.sigmaFiberEquiv profileOfSource).symm.toEmbedding |>.trans
      (gradedEmbedding.trans
        (Equiv.sigmaFiberEquiv profileOfTarget).toEmbedding)
  rw [configurationPairTwoCycleFineHall_iff_exists_injective]
  refine ⟨matchingEmbedding, matchingEmbedding.injective, ?_⟩
  intro source
  change SixVertexConfigurationPairTwoCycleFineRelated source
    ((fiberEmbedding (profileOfSource source)
      ⟨source, rfl⟩).1)
  exact (hmatching (profileOfSource source)).choose_spec.2 ⟨source, rfl⟩



theorem configurationPairTwoCycleFineProfileFiberHall_of_Hall
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    (hHall : SixVertexConfigurationPairTwoCycleFineHall
      T lower middle upper) :
    SixVertexConfigurationPairTwoCycleFineProfileFiberHall
      T lower middle upper := by
  obtain ⟨matching, hinjective, hrelated⟩ :=
    (configurationPairTwoCycleFineHall_iff_exists_injective
      T lower middle upper).mp hHall
  rw [configurationPairTwoCycleFineProfileFiberHall_iff]
  intro profile
  let fiberMatching :
      SixVertexConfigurationPairFineProfileFiber T lower upper profile ->
        SixVertexConfigurationPairFineProfileFiber
          T middle middle profile :=
    fun source =>
      ⟨matching source.1,
        (hrelated source.1).2.symm.trans source.2⟩
  refine ⟨fiberMatching, ?_, ?_⟩
  · intro source₁ source₂ heq
    apply Subtype.ext
    apply hinjective
    exact congrArg Subtype.val heq
  · intro source
    exact hrelated source.1



theorem configurationPairTwoCycleFineHall_iff_profileFiberHall
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) :
    SixVertexConfigurationPairTwoCycleFineHall T lower middle upper <->
      SixVertexConfigurationPairTwoCycleFineProfileFiberHall
        T lower middle upper :=
  ⟨configurationPairTwoCycleFineProfileFiberHall_of_Hall,
    configurationPairTwoCycleFineHall_of_profileFiberHall⟩



theorem configurationPairTotalCReconnection_of_twoCycleFineHall
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    (hHall : SixVertexConfigurationPairTwoCycleFineHall
      T lower middle upper) :
    SixVertexConfigurationPairTotalCReconnection
      T lower middle upper := by
  obtain ⟨matching, hinjective, hrelated⟩ :=
    (configurationPairTwoCycleFineHall_iff_exists_injective
      T lower middle upper).mp hHall
  exact ⟨matching, hinjective,
    fun source => (hrelated source).totalC⟩



theorem configurationPairTotalCFibers_of_twoCycleFineHall
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    (hHall : SixVertexConfigurationPairTwoCycleFineHall
      T lower middle upper) :
    SixVertexConfigurationPairTotalCFiberDominates
      T lower middle upper :=
  (configurationPairTotalCReconnection_iff_fiberDominates
    T lower middle upper).mp
      (configurationPairTotalCReconnection_of_twoCycleFineHall hHall)



theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_twoCycleFineHall
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hHall : SixVertexConfigurationPairTwoCycleFineHall T
      ⟨middle.val - 1, by omega⟩ middle
      ⟨middle.val + 1, by omega⟩) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCFibers
    T middle hmiddle_pos hmiddle_lt
      (configurationPairTotalCFibers_of_twoCycleFineHall hHall)



theorem sixVertexSectorTrace_logConcave_of_twoCycleFineHall
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    {c : Real} (hc : 2 <= c)
    (hHall : SixVertexConfigurationPairTwoCycleFineHall T
      ⟨middle.val - 1, by omega⟩ middle
      ⟨middle.val + 1, by omega⟩) :
    Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) *
        Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <=
      Matrix.trace
          (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 :=
  sixVertexSectorTrace_logConcave_of_totalCFibers
    T middle hmiddle_pos hmiddle_lt hc
      (configurationPairTotalCFibers_of_twoCycleFineHall hHall)

end

end StatMech.FrontierD
