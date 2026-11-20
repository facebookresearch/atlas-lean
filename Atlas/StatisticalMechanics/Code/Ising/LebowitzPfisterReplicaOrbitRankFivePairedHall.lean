/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveOrderedPairSwap
import Code.Foundations.FiniteBidegreeHall










open scoped symmDiff

namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFivePairedHallDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _


def LPReplicaAggregateDecoratedTargetBase
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  Sigma fun i : I => Sigma fun j : I =>
    LPReplicaDecoratedOrbitAtom G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) q

noncomputable instance instFintypeLPReplicaAggregateDecoratedTargetBase
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype (LPReplicaAggregateDecoratedTargetBase G sites q) := by
  unfold LPReplicaAggregateDecoratedTargetBase
  infer_instance




noncomputable def lpReplicaAggregateDecoratedEmbeddingOfPairRepresentative
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (paired : LPReplicaAggregateDecoratedSourcePairRepresentative G sites q ↪
      LPReplicaAggregateDecoratedTargetBase G sites q) :
    LPReplicaAggregateDecoratedSource G sites q ↪
      LPReplicaAggregateDecoratedTarget G sites q where
  toFun z :=
    let coded := lpReplicaAggregateDecoratedSourcePairEquiv G sites q z
    ⟨coded.1, paired coded.2⟩
  inj' := by
    intro z w h
    let E := lpReplicaAggregateDecoratedSourcePairEquiv G sites q
    apply E.injective
    change ((E z).1, paired (E z).2) =
      ((E w).1, paired (E w).2) at h
    have hfst : (E z).1 = (E w).1 := congrArg
      (fun x : LPReplicaAggregateDecoratedTarget G sites q => x.1) h
    have hsnd : paired (E z).2 = paired (E w).2 := congrArg
      (fun x : LPReplicaAggregateDecoratedTarget G sites q => x.2) h
    exact Prod.ext hfst (paired.injective hsnd)



noncomputable def
    lpReplicaAggregateDecoratedEmbeddingOfPairRepresentativeCertificates
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (related : LPReplicaAggregateDecoratedSourcePairRepresentative G sites q ->
      LPReplicaAggregateDecoratedTargetBase G sites q -> Prop)
    (degree : Nat) (hdegree : 0 < degree)
    (sourceCertificates : forall source,
      Fin degree ↪ {target // related source target})
    (targetCertificateCode : forall target,
      {source // related source target} ↪ Fin degree) :
    LPReplicaAggregateDecoratedSource G sites q ↪
      LPReplicaAggregateDecoratedTarget G sites q := by
  classical
  let hexists :=
    finiteRelation_exists_injective_of_certificateEmbeddings
      related degree hdegree sourceCertificates targetCertificateCode
  let matching := Classical.choose hexists
  have hmatching := Classical.choose_spec hexists
  exact lpReplicaAggregateDecoratedEmbeddingOfPairRepresentative
    G sites q ⟨matching, hmatching.1⟩



def LPReplicaAggregateDecoratedPairCandidateRelated
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (degree : Nat)
    (candidate : LPReplicaAggregateDecoratedSourcePairRepresentative
        G sites q -> Fin degree ->
      LPReplicaAggregateDecoratedTargetBase G sites q)
    (source : LPReplicaAggregateDecoratedSourcePairRepresentative G sites q)
    (target : LPReplicaAggregateDecoratedTargetBase G sites q) : Prop :=
  ∃ certificate, candidate source certificate = target


def lpReplicaAggregateDecoratedPairCandidateSourceCertificates
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (degree : Nat)
    (candidate : LPReplicaAggregateDecoratedSourcePairRepresentative
        G sites q -> Fin degree ->
      LPReplicaAggregateDecoratedTargetBase G sites q)
    (hcandidate : forall source, Function.Injective (candidate source))
    (source : LPReplicaAggregateDecoratedSourcePairRepresentative G sites q) :
    Fin degree ↪
      {target // LPReplicaAggregateDecoratedPairCandidateRelated
        G sites q degree candidate source target} where
  toFun certificate := ⟨candidate source certificate, certificate, rfl⟩
  inj' := fun _ _ h => hcandidate source (congrArg Subtype.val h)



noncomputable def lpReplicaAggregateDecoratedPairCandidateTargetCode
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (degree : Nat)
    (candidate : LPReplicaAggregateDecoratedSourcePairRepresentative
        G sites q -> Fin degree ->
      LPReplicaAggregateDecoratedTargetBase G sites q)
    (recover : LPReplicaAggregateDecoratedTargetBase G sites q ->
      Fin degree ->
        LPReplicaAggregateDecoratedSourcePairRepresentative G sites q)
    (hrecover : forall source certificate,
      recover (candidate source certificate) certificate = source)
    (target : LPReplicaAggregateDecoratedTargetBase G sites q) :
    {source // LPReplicaAggregateDecoratedPairCandidateRelated
        G sites q degree candidate source target} ↪ Fin degree := by
  classical
  let certificate := fun source :
      {source // LPReplicaAggregateDecoratedPairCandidateRelated
        G sites q degree candidate source target} =>
    Classical.choose source.2
  refine ⟨certificate, ?_⟩
  intro source₁ source₂ hcertificate
  have htarget₁ : candidate source₁.1 (certificate source₁) = target :=
    Classical.choose_spec source₁.2
  have htarget₂ : candidate source₂.1 (certificate source₂) = target :=
    Classical.choose_spec source₂.2
  have hrecover₁ : recover target (certificate source₁) = source₁.1 := by
    calc
      recover target (certificate source₁) =
          recover (candidate source₁.1 (certificate source₁))
            (certificate source₁) :=
        congrArg (fun t => recover t (certificate source₁)) htarget₁.symm
      _ = source₁.1 := hrecover source₁.1 (certificate source₁)
  have hrecover₂ : recover target (certificate source₂) = source₂.1 := by
    calc
      recover target (certificate source₂) =
          recover (candidate source₂.1 (certificate source₂))
            (certificate source₂) :=
        congrArg (fun t => recover t (certificate source₂)) htarget₂.symm
      _ = source₂.1 := hrecover source₂.1 (certificate source₂)
  apply Subtype.ext
  rw [← hrecover₁, ← hrecover₂, hcertificate]



noncomputable def
    lpReplicaAggregateDecoratedEmbeddingOfPairRepresentativeCandidates
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (degree : Nat) (hdegree : 0 < degree)
    (candidate : LPReplicaAggregateDecoratedSourcePairRepresentative
        G sites q -> Fin degree ->
      LPReplicaAggregateDecoratedTargetBase G sites q)
    (hcandidate : forall source, Function.Injective (candidate source))
    (recover : LPReplicaAggregateDecoratedTargetBase G sites q ->
      Fin degree ->
        LPReplicaAggregateDecoratedSourcePairRepresentative G sites q)
    (hrecover : forall source certificate,
      recover (candidate source certificate) certificate = source) :
    LPReplicaAggregateDecoratedSource G sites q ↪
      LPReplicaAggregateDecoratedTarget G sites q :=
  lpReplicaAggregateDecoratedEmbeddingOfPairRepresentativeCertificates
    G sites q
    (LPReplicaAggregateDecoratedPairCandidateRelated
      G sites q degree candidate)
    degree hdegree
    (lpReplicaAggregateDecoratedPairCandidateSourceCertificates
      G sites q degree candidate hcandidate)
    (lpReplicaAggregateDecoratedPairCandidateTargetCode
      G sites q degree candidate recover hrecover)

end

end StatMech.Ising
