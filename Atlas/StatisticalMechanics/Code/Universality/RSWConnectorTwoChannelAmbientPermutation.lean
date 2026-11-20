/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.RSWConnectorTwoChannelStaticCutEndpoint
import Code.Universality.RSWSequentialStoppedConditionalLaw












open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section



noncomputable def rlc_twoChannelFullPhysicalAmbientFailureEmbedding
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hfaith) :
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} ↪
      ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  rlc_twoChannelLiftEdgeFailureEmbedding gamma gamma'
    (rlc_twoChannelFullPhysicalSuccessEmbedding hfaith
      (rlc_twoChannelFullPhysicalPermutationSuccess_of_staticCutIntersection
        hfaith hstatic))



theorem rlc_twoChannelFullPhysicalAmbientFailureEmbedding_success
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hfaith)
    (rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
      rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'}) :
    rlc_twoChannelFullPhysicalAmbientFailureEmbedding hfaith hstatic rho ∈
      rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
  exact rlc_twoChannelLiftEdgeFailureEmbedding_success gamma gamma'
    (rlc_twoChannelFullPhysicalSuccessEmbedding hfaith
      (rlc_twoChannelFullPhysicalPermutationSuccess_of_staticCutIntersection
        hfaith hstatic)) rho



theorem rlc_twoChannelFullPhysicalAmbientFailureEmbedding_apply_of_not_edge
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hfaith)
    (rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
      rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'})
    (e : Sym2 (RlcConnectorVertex n))
    (he : e ∉ (rlc_connectorTwoChannelGraph gamma gamma').edgeSet) :
    rlc_twoChannelFullPhysicalAmbientFailureEmbedding hfaith hstatic rho e =
      rho.1 e := by
  change rlc_twoChannelEdgeConfigCombine gamma gamma' _
      ((rlc_twoChannelConfigSplitEquiv gamma gamma' rho.1).2) e = rho.1 e
  simp [rlc_twoChannelEdgeConfigCombine, rlc_twoChannelConfigSplitEquiv, he]




theorem rlc_twoChannelFullPhysicalAmbientFailureEmbedding_agreesOff
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hfaith)
    (rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
      rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'}) :
    FK.AgreesOff (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset rho.1
      (rlc_twoChannelFullPhysicalAmbientFailureEmbedding
        hfaith hstatic rho) := by
  intro e he
  apply rlc_twoChannelFullPhysicalAmbientFailureEmbedding_apply_of_not_edge
  simpa [SimpleGraph.mem_edgeFinset] using he



theorem rlc_connectorTwoChannelGraph_edgeFinset_disjoint_traceWiring
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    Disjoint (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset
      (rlc_connectorTraceWiring gamma gamma').edgeFinset := by
  rw [Finset.disjoint_left]
  intro e heChannel heTrace
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeFinset] at heChannel heTrace
      exact heChannel.2 heTrace


theorem rlc_connectorExtendConfig_pathPairOpen_of_trace_open
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (htrace : ∀ e ∈ (rlc_connectorTraceWiring gamma gamma').edgeFinset,
      psi e = true) :
    rlc_connectorExtendConfig psi ∈ rlc_pathPairOpen (gamma, gamma') := by
  constructor
  · intro e he
    have heCandidate :
        e ∈ rlc_extremalPairCandidateEdges (gamma, gamma') := by
      rw [rlc_extremalPairCandidateEdges, rlc_rightLowestCandidateEdges,
        Finset.mem_union, Finset.mem_union]
      exact Or.inl (Or.inl he)
    obtain ⟨f, rfl⟩ :=
      rlc_extremalPairCandidateEdge_exists_connectorLift
        gamma gamma' heCandidate
    rw [rlc_connectorExtendConfig_apply]
    apply htrace
    induction f using Sym2.inductionOn with
    | _ x y =>
        rw [SimpleGraph.mem_edgeFinset]
        exact ⟨rlc_pathEdge_lattice gamma.1 (by simpa using he),
          Finset.mem_union_left _ (by simpa using he)⟩
  · intro e he
    have heCandidate :
        e ∈ rlc_extremalPairCandidateEdges (gamma, gamma') := by
      rw [rlc_extremalPairCandidateEdges, rlc_leftHighestCandidateEdges,
        Finset.mem_union, Finset.mem_union]
      exact Or.inr (Or.inl he)
    obtain ⟨f, rfl⟩ :=
      rlc_extremalPairCandidateEdge_exists_connectorLift
        gamma gamma' heCandidate
    rw [rlc_connectorExtendConfig_apply]
    apply htrace
    induction f using Sym2.inductionOn with
    | _ x y =>
        rw [SimpleGraph.mem_edgeFinset]
        exact ⟨rlc_pathEdge_lattice gamma'.1 (by simpa using he),
          Finset.mem_union_right _ (by simpa using he)⟩





theorem rlc_allOpenConnectorConfig_displays_two_pathPairs
    {n : Int} (pair pair' : RlcDiagonalPathPair n) :
    let psi : ConfigSpace (Sym2 (RlcConnectorVertex n)) := fun _ ↦ true
    rlc_connectorExtendConfig psi ∈ rlc_pathPairOpen pair ∩
      rlc_pathPairOpen pair' := by
  dsimp only
  constructor
  · apply rlc_connectorExtendConfig_pathPairOpen_of_trace_open
    simp
  · apply rlc_connectorExtendConfig_pathPairOpen_of_trace_open
    simp






abbrev RlcTwoChannelActiveFiniteExtremalPair (n : Int) :=
  {pair : RlcDiagonalPathPair n //
    (rlc_finiteExtremalPairCandidate pair.1 pair.2).Nonempty}

noncomputable instance rlcTwoChannelActiveFiniteExtremalPairFintype
    (n : Int) : Fintype (RlcTwoChannelActiveFiniteExtremalPair n) :=
  Fintype.ofFinite _



theorem rlc_finiteExtremalPairCandidate_pairwiseDisjoint
    {n : Int} (hright : RlcRightEnvelopeProperty n)
    (hleft : RlcLeftEnvelopeProperty n) :
    Pairwise fun pair pair' : RlcDiagonalPathPair n ↦
      Disjoint
        (rlc_finiteExtremalPairCandidate pair.1 pair.2)
        (rlc_finiteExtremalPairCandidate pair'.1 pair'.2) := by
  intro pair pair' hne
  rw [Set.disjoint_left]
  intro psi hpair hpair'
  exact Set.disjoint_left.mp
    (rlc_extremalPairCandidate_pairwiseDisjoint hright hleft hne)
    hpair hpair'



theorem rlc_activeFiniteExtremalPairCandidate_pairwiseDisjoint
    {n : Int} (hright : RlcRightEnvelopeProperty n)
    (hleft : RlcLeftEnvelopeProperty n) :
    Pairwise fun pair pair' : RlcTwoChannelActiveFiniteExtremalPair n ↦
      Disjoint
        (rlc_finiteExtremalPairCandidate pair.1.1 pair.1.2)
        (rlc_finiteExtremalPairCandidate pair'.1.1 pair'.1.2) := by
  intro pair pair' hne
  apply rlc_finiteExtremalPairCandidate_pairwiseDisjoint hright hleft
  intro heq
  exact hne (Subtype.ext heq)



abbrev RlcTwoChannelFiniteDiagonalConfig (n : Int) :=
  {psi : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
    rlc_connectorExtendConfig psi ∈
      rlc_rightDiagonal n ∩ rlc_leftDiagonal n}



theorem rlc_exists_finiteExtremalPairCandidate
    {n : Int} (psi : RlcTwoChannelFiniteDiagonalConfig n) :
    ∃ pair : RlcDiagonalPathPair n,
      psi.1 ∈ rlc_finiteExtremalPairCandidate pair.1 pair.2 := by
  have h : rlc_connectorExtendConfig psi.1 ∈
      ⋃ pair : RlcDiagonalPathPair n, rlc_extremalPairCandidate pair := by
    rw [rlc_iUnion_extremalPairCandidate n]
    exact psi.2
  obtain ⟨pair, hpair⟩ := Set.mem_iUnion.mp h
  exact ⟨pair, hpair⟩

noncomputable def rlc_twoChannelFiniteExtremalPairSelector
    {n : Int} (psi : RlcTwoChannelFiniteDiagonalConfig n) :
    RlcTwoChannelActiveFiniteExtremalPair n :=
  ⟨Classical.choose (rlc_exists_finiteExtremalPairCandidate psi),
    ⟨psi.1, Classical.choose_spec
      (rlc_exists_finiteExtremalPairCandidate psi)⟩⟩


theorem rlc_twoChannelFiniteExtremalPairSelector_selected
    {n : Int} (psi : RlcTwoChannelFiniteDiagonalConfig n) :
    psi.1 ∈ rlc_finiteExtremalPairCandidate
      (rlc_twoChannelFiniteExtremalPairSelector psi).1.1
      (rlc_twoChannelFiniteExtremalPairSelector psi).1.2 := by
  exact Classical.choose_spec (rlc_exists_finiteExtremalPairCandidate psi)



theorem rlc_twoChannelFiniteExtremalPairSelector_eq_of_selected
    {n : Int} (hright : RlcRightEnvelopeProperty n)
    (hleft : RlcLeftEnvelopeProperty n)
    (psi : RlcTwoChannelFiniteDiagonalConfig n)
    (pair : RlcTwoChannelActiveFiniteExtremalPair n)
    (hselected : psi.1 ∈
      rlc_finiteExtremalPairCandidate pair.1.1 pair.1.2) :
    rlc_twoChannelFiniteExtremalPairSelector psi = pair := by
  by_contra hne
  exact Set.disjoint_left.mp
    (rlc_activeFiniteExtremalPairCandidate_pairwiseDisjoint
      hright hleft hne)
    (rlc_twoChannelFiniteExtremalPairSelector_selected psi) hselected




structure RlcTwoChannelIndexedSelectedFailure {n : Int} (I : Type*)
    (pair : I → RlcDiagonalPathPair n) where
  index : I
  config : ConfigSpace (Sym2 (RlcConnectorVertex n))
  selected : config ∈
    rlc_finiteExtremalPairCandidate (pair index).1 (pair index).2
  failure : config ∉
    rlc_finiteTwoChannelConnectorEvent (pair index).1 (pair index).2



noncomputable def rlc_twoChannelIndexedAmbientFailureMap
    {n : Int} {I : Type*} (pair : I → RlcDiagonalPathPair n)
    (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
    (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection
      (pair i).1 (pair i).2 (hfaith i))
    (x : RlcTwoChannelIndexedSelectedFailure I pair) :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  rlc_twoChannelFullPhysicalAmbientFailureEmbedding
    (hfaith x.index) (hstatic x.index) ⟨x.config, x.failure⟩



def RlcTwoChannelIndexedAmbientCollisionRecovery
    {n : Int} {I : Type*} (pair : I → RlcDiagonalPathPair n)
    (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
    (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection
      (pair i).1 (pair i).2 (hfaith i)) : Prop :=
  ∀ x y : RlcTwoChannelIndexedSelectedFailure I pair,
    rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x =
        rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic y →
      x.index = y.index



theorem rlc_twoChannelIndexedAmbientFailureMap_success
    {n : Int} {I : Type*} (pair : I → RlcDiagonalPathPair n)
    (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
    (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection
      (pair i).1 (pair i).2 (hfaith i))
    (x : RlcTwoChannelIndexedSelectedFailure I pair) :
    rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x ∈
      rlc_finiteTwoChannelConnectorEvent
        (pair x.index).1 (pair x.index).2 := by
  exact rlc_twoChannelFullPhysicalAmbientFailureEmbedding_success
    (hfaith x.index) (hstatic x.index) ⟨x.config, x.failure⟩



theorem rlc_twoChannelIndexedAmbientFailureMap_agreesOff
    {n : Int} {I : Type*} (pair : I → RlcDiagonalPathPair n)
    (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
    (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection
      (pair i).1 (pair i).2 (hfaith i))
    (x : RlcTwoChannelIndexedSelectedFailure I pair) :
    FK.AgreesOff
      (rlc_connectorTwoChannelGraph
        (pair x.index).1 (pair x.index).2).edgeFinset
      x.config
      (rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x) := by
  exact rlc_twoChannelFullPhysicalAmbientFailureEmbedding_agreesOff
    (hfaith x.index) (hstatic x.index) ⟨x.config, x.failure⟩




theorem rlc_twoChannelIndexedAmbientFailureMap_collision_agreesOff_union
    {n : Int} {I : Type*} (pair : I → RlcDiagonalPathPair n)
    (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
    (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection
      (pair i).1 (pair i).2 (hfaith i))
    {x y : RlcTwoChannelIndexedSelectedFailure I pair}
    (hxy : rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x =
      rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic y) :
    ∀ e,
      e ∉ (rlc_connectorTwoChannelGraph
        (pair x.index).1 (pair x.index).2).edgeFinset →
      e ∉ (rlc_connectorTwoChannelGraph
        (pair y.index).1 (pair y.index).2).edgeFinset →
      x.config e = y.config e := by
  intro e hex hey
  calc
    x.config e =
        rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x e :=
      (rlc_twoChannelIndexedAmbientFailureMap_agreesOff
        pair hfaith hstatic x e hex).symm
    _ = rlc_twoChannelIndexedAmbientFailureMap
        pair hfaith hstatic y e := congrFun hxy e
    _ = y.config e :=
      rlc_twoChannelIndexedAmbientFailureMap_agreesOff
        pair hfaith hstatic y e hey


theorem rlc_twoChannelIndexedAmbientFailureMap_trace_open
    {n : Int} {I : Type*} (pair : I → RlcDiagonalPathPair n)
    (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
    (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection
      (pair i).1 (pair i).2 (hfaith i))
    (x : RlcTwoChannelIndexedSelectedFailure I pair) :
    ∀ e ∈ (rlc_connectorTraceWiring
      (pair x.index).1 (pair x.index).2).edgeFinset,
      rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x e = true := by
  intro e heTrace
  have heOutside : e ∉ (rlc_connectorTwoChannelGraph
      (pair x.index).1 (pair x.index).2).edgeFinset := fun heChannel =>
    (Finset.disjoint_left.mp
      (rlc_connectorTwoChannelGraph_edgeFinset_disjoint_traceWiring
        (pair x.index).1 (pair x.index).2)) heChannel heTrace
  rw [rlc_twoChannelIndexedAmbientFailureMap_agreesOff
    pair hfaith hstatic x e heOutside]
  exact rlc_finiteExtremalPairCandidate_trace_open
    (pair x.index).1 (pair x.index).2 x.selected e heTrace



noncomputable def rlc_twoChannelIndexedAmbientTargetDiagonalConfig
    {n : Int} {I : Type*} (pair : I → RlcDiagonalPathPair n)
    (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
    (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection
      (pair i).1 (pair i).2 (hfaith i))
    (x : RlcTwoChannelIndexedSelectedFailure I pair) :
    RlcTwoChannelFiniteDiagonalConfig n := by
  let psi := rlc_twoChannelIndexedAmbientFailureMap
    pair hfaith hstatic x
  have hopen : rlc_connectorExtendConfig psi ∈
      rlc_pathPairOpen (pair x.index) :=
    rlc_connectorExtendConfig_pathPairOpen_of_trace_open
      (pair x.index).1 (pair x.index).2 psi
      (rlc_twoChannelIndexedAmbientFailureMap_trace_open
        pair hfaith hstatic x)
  refine ⟨psi, ?_⟩
  constructor
  · rw [← rlc_iUnion_rightDiagonalPath n]
    exact Set.mem_iUnion.mpr ⟨(pair x.index).1, hopen.1⟩
  · rw [← rlc_iUnion_leftDiagonalPath n]
    exact Set.mem_iUnion.mpr ⟨(pair x.index).2, hopen.2⟩


noncomputable def rlc_twoChannelIndexedAmbientTargetSelector
    {n : Int} {I : Type*} (pair : I → RlcDiagonalPathPair n)
    (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
    (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection
      (pair i).1 (pair i).2 (hfaith i))
    (x : RlcTwoChannelIndexedSelectedFailure I pair) :
    RlcTwoChannelActiveFiniteExtremalPair n :=
  rlc_twoChannelFiniteExtremalPairSelector
    (rlc_twoChannelIndexedAmbientTargetDiagonalConfig
      pair hfaith hstatic x)




theorem rlc_twoChannelActiveAmbientTargetSelector_eq_iff_stable
    {n : Int} (hright : RlcRightEnvelopeProperty n)
    (hleft : RlcLeftEnvelopeProperty n)
    (hfaith : ∀ i : RlcTwoChannelActiveFiniteExtremalPair n,
      RlcBookFaithfulTracePair i.1.1 i.1.2)
    (hstatic : ∀ i : RlcTwoChannelActiveFiniteExtremalPair n,
      RlcTwoChannelFullPhysicalStaticCutIntersection
        i.1.1 i.1.2 (hfaith i))
    (x : RlcTwoChannelIndexedSelectedFailure
      (RlcTwoChannelActiveFiniteExtremalPair n) Subtype.val) :
    rlc_twoChannelIndexedAmbientTargetSelector
        Subtype.val hfaith hstatic x = x.index ↔
      rlc_twoChannelIndexedAmbientFailureMap
          Subtype.val hfaith hstatic x ∈
        rlc_finiteExtremalPairCandidate
          x.index.1.1 x.index.1.2 := by
  constructor
  · intro heq
    have hselected := rlc_twoChannelFiniteExtremalPairSelector_selected
      (rlc_twoChannelIndexedAmbientTargetDiagonalConfig
        Subtype.val hfaith hstatic x)
    change rlc_twoChannelFiniteExtremalPairSelector
      (rlc_twoChannelIndexedAmbientTargetDiagonalConfig
        Subtype.val hfaith hstatic x) = x.index at heq
    change rlc_twoChannelIndexedAmbientFailureMap
        Subtype.val hfaith hstatic x ∈
      rlc_finiteExtremalPairCandidate
        (rlc_twoChannelFiniteExtremalPairSelector
          (rlc_twoChannelIndexedAmbientTargetDiagonalConfig
            Subtype.val hfaith hstatic x)).1.1
        (rlc_twoChannelFiniteExtremalPairSelector
          (rlc_twoChannelIndexedAmbientTargetDiagonalConfig
            Subtype.val hfaith hstatic x)).1.2 at hselected
    rwa [heq] at hselected
  · intro hstable
    apply rlc_twoChannelFiniteExtremalPairSelector_eq_of_selected
      hright hleft
    exact hstable




theorem rlc_twoChannelIndexedAmbientFailureMap_glues_horizontal
    {n : Int} (hn : 0 < n) {I : Type*}
    (pair : I → RlcDiagonalPathPair n)
    (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
    (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection
      (pair i).1 (pair i).2 (hfaith i))
    (x : RlcTwoChannelIndexedSelectedFailure I pair) :
    rlc_connectorExtendConfig
        (rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x) ∈
      horizontalCrossingEvent (-2 * n) (2 * n) (-n) n := by
  apply rlc_twoChannelConnector_glues_horizontal n hn
    (pair x.index).1 (pair x.index).2
  refine ⟨rlc_connectorExtendConfig_pathPairOpen_of_trace_open
    (pair x.index).1 (pair x.index).2 _
      (rlc_twoChannelIndexedAmbientFailureMap_trace_open
        pair hfaith hstatic x), ?_⟩
  change rlc_connectorRestrictConfig
      (rlc_connectorExtendConfig
        (rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x)) ∈
    rlc_finiteTwoChannelConnectorEvent
      (pair x.index).1 (pair x.index).2
  have hrestrict : rlc_connectorRestrictConfig
      (rlc_connectorExtendConfig
        (rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x)) =
      rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x := by
    funext e
    exact rlc_connectorExtendConfig_apply _ e
  rw [hrestrict]
  exact rlc_twoChannelIndexedAmbientFailureMap_success
    pair hfaith hstatic x




theorem rlc_twoChannelIndexedAmbientCollisionRecovery_of_target_stable
    {n : Int} {I : Type*} (pair : I → RlcDiagonalPathPair n)
    (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
    (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection
      (pair i).1 (pair i).2 (hfaith i))
    (hdisjoint : Pairwise fun i j : I ↦
      Disjoint
        (rlc_finiteExtremalPairCandidate (pair i).1 (pair i).2)
        (rlc_finiteExtremalPairCandidate (pair j).1 (pair j).2))
    (hstable : ∀ x : RlcTwoChannelIndexedSelectedFailure I pair,
      rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic x ∈
        rlc_finiteExtremalPairCandidate
          (pair x.index).1 (pair x.index).2) :
    RlcTwoChannelIndexedAmbientCollisionRecovery pair hfaith hstatic := by
  intro x y hxy
  by_contra hne
  exact Set.disjoint_left.mp (hdisjoint hne)
    (hstable x) (hxy ▸ hstable y)




theorem
    rlc_twoChannelActiveAmbientCollisionRecovery_of_target_stable
    {n : Int} (hright : RlcRightEnvelopeProperty n)
    (hleft : RlcLeftEnvelopeProperty n)
    (hfaith : ∀ i : RlcTwoChannelActiveFiniteExtremalPair n,
      RlcBookFaithfulTracePair i.1.1 i.1.2)
    (hstatic : ∀ i : RlcTwoChannelActiveFiniteExtremalPair n,
      RlcTwoChannelFullPhysicalStaticCutIntersection
        i.1.1 i.1.2 (hfaith i))
    (hstable : ∀ x : RlcTwoChannelIndexedSelectedFailure
        (RlcTwoChannelActiveFiniteExtremalPair n) Subtype.val,
      rlc_twoChannelIndexedAmbientFailureMap
          Subtype.val hfaith hstatic x ∈
        rlc_finiteExtremalPairCandidate
          x.index.1.1 x.index.1.2) :
    RlcTwoChannelIndexedAmbientCollisionRecovery
      Subtype.val hfaith hstatic := by
  apply rlc_twoChannelIndexedAmbientCollisionRecovery_of_target_stable
    Subtype.val hfaith hstatic
    (rlc_activeFiniteExtremalPairCandidate_pairwiseDisjoint hright hleft)
    hstable





theorem rlc_twoChannelIndexedAmbientCollisionRecovery_const_bool_no_go
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hstatic : RlcTwoChannelFullPhysicalStaticCutIntersection
      gamma gamma' hfaith)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hselected : rho ∈ rlc_finiteExtremalPairCandidate gamma gamma')
    (hfailure : rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    ¬ RlcTwoChannelIndexedAmbientCollisionRecovery
      (I := Bool) (fun _ ↦ (gamma, gamma')) (fun _ ↦ hfaith)
        (fun _ ↦ hstatic) := by
  intro hrecover
  let x : RlcTwoChannelIndexedSelectedFailure Bool
      (fun _ ↦ (gamma, gamma')) :=
    ⟨false, rho, hselected, hfailure⟩
  let y : RlcTwoChannelIndexedSelectedFailure Bool
      (fun _ ↦ (gamma, gamma')) :=
    ⟨true, rho, hselected, hfailure⟩
  have hmap : rlc_twoChannelIndexedAmbientFailureMap
      (fun _ : Bool ↦ (gamma, gamma')) (fun _ ↦ hfaith)
        (fun _ ↦ hstatic) x =
      rlc_twoChannelIndexedAmbientFailureMap
        (fun _ : Bool ↦ (gamma, gamma')) (fun _ ↦ hfaith)
          (fun _ ↦ hstatic) y := rfl
  have := hrecover x y hmap
  simp [x, y] at this



noncomputable def rlc_twoChannelIndexedAmbientFailureEmbedding
    {n : Int} {I : Type*} (pair : I → RlcDiagonalPathPair n)
    (hfaith : ∀ i, RlcBookFaithfulTracePair (pair i).1 (pair i).2)
    (hstatic : ∀ i, RlcTwoChannelFullPhysicalStaticCutIntersection
      (pair i).1 (pair i).2 (hfaith i))
    (hrecover : RlcTwoChannelIndexedAmbientCollisionRecovery
      pair hfaith hstatic) :
    RlcTwoChannelIndexedSelectedFailure I pair ↪
      ConfigSpace (Sym2 (RlcConnectorVertex n)) where
  toFun := rlc_twoChannelIndexedAmbientFailureMap pair hfaith hstatic
  inj' := by
    intro x y hxy
    have hindex : x.index = y.index := hrecover x y hxy
    cases x with
    | mk ix rho hselected hfailure =>
      cases y with
      | mk iy sigma hselected' hfailure' =>
        dsimp only at hindex
        subst iy
        simp only [rlc_twoChannelIndexedAmbientFailureMap] at hxy
        have hlocal :
            (⟨rho, hfailure⟩ :
              {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
                rho ∉ rlc_finiteTwoChannelConnectorEvent
                  (pair ix).1 (pair ix).2}) =
            ⟨sigma, hfailure'⟩ :=
          (rlc_twoChannelFullPhysicalAmbientFailureEmbedding
            (hfaith ix) (hstatic ix)).injective hxy
        cases hlocal
        rfl

end

end StatMech.Universality
