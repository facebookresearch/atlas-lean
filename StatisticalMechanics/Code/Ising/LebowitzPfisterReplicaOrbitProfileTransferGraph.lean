/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching










namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaProfileTransferDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _


abbrev LPReplicaCommonOrbitProfile
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  {m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
    lpReplicaSymmetrizedProfile G sites m = q}



def LPReplicaProfilePartialReflects
    (G : SimpleGraph V) (sites : I -> V)
    (m n : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Prop :=
  ∃ p, p <= m ∧ lpReplicaPartialReflectProfile G sites m p = n



theorem lpReplicaProfilePartialReflects_of_symmetrizedProfile_eq
    (G : SimpleGraph V) (sites : I -> V)
    (m n q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hn : lpReplicaSymmetrizedProfile G sites n = q) :
    LPReplicaProfilePartialReflects G sites m n := by
  let p := fun e => m e - n e
  refine ⟨p, fun e => Nat.sub_le _ _, ?_⟩
  funext e
  have htot := congrFun (hm.trans hn.symm) e
  unfold lpReplicaSymmetrizedProfile at htot
  unfold lpReplicaPartialReflectProfile
  dsimp only [p]
  omega

theorem lpReplicaProfilePartialReflects_commonOrbit
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (m n : LPReplicaCommonOrbitProfile G sites q) :
    LPReplicaProfilePartialReflects G sites m.1 n.1 :=
  lpReplicaProfilePartialReflects_of_symmetrizedProfile_eq
    G sites m.1 n.1 q m.2 n.2



noncomputable def lpReplicaCommonOrbitTransferGraph
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    SimpleGraph (LPReplicaCommonOrbitProfile G sites q) :=
  SimpleGraph.completeGraph _

theorem lpReplicaCommonOrbitTransferGraph_adj_iff
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (m n : LPReplicaCommonOrbitProfile G sites q) :
    (lpReplicaCommonOrbitTransferGraph G sites q).Adj m n ↔
      m ≠ n ∧ LPReplicaProfilePartialReflects G sites m.1 n.1 := by
  simp only [lpReplicaCommonOrbitTransferGraph, SimpleGraph.top_adj]
  constructor
  · intro hne
    exact ⟨hne,
      lpReplicaProfilePartialReflects_commonOrbit G sites q m n⟩
  · exact And.left

theorem lpReplicaCommonOrbitTransferGraph_preconnected
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaCommonOrbitTransferGraph G sites q).Preconnected := by
  exact SimpleGraph.preconnected_top

theorem lpReplicaCommonOrbitTransferGraph_component_eq
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (m n : LPReplicaCommonOrbitProfile G sites q) :
    (lpReplicaCommonOrbitTransferGraph G sites q).connectedComponentMk m =
      (lpReplicaCommonOrbitTransferGraph G sites q).connectedComponentMk n := by
  exact SimpleGraph.ConnectedComponent.sound
    (lpReplicaCommonOrbitTransferGraph_preconnected G sites q m n)


def lpReplicaOffdiagDecoratedSourceOrbitProfile
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    LPReplicaCommonOrbitProfile G sites q :=
  ⟨z.1.1.1, z.1.1.2⟩


def lpReplicaOffdiagDecoratedTargetOrbitProfile
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    LPReplicaCommonOrbitProfile G sites q :=
  match y with
  | Sum.inl z => ⟨z.1.1.1, z.1.1.2⟩
  | Sum.inr z => ⟨z.1.1.1, z.1.1.2⟩


def lpReplicaOffdiagDecoratedSourceTransferComponent
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    (lpReplicaCommonOrbitTransferGraph G sites q).ConnectedComponent :=
  (lpReplicaCommonOrbitTransferGraph G sites q).connectedComponentMk
    (lpReplicaOffdiagDecoratedSourceOrbitProfile G sites i j q z)


def lpReplicaOffdiagDecoratedTargetTransferComponent
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    (lpReplicaCommonOrbitTransferGraph G sites q).ConnectedComponent :=
  (lpReplicaCommonOrbitTransferGraph G sites q).connectedComponentMk
    (lpReplicaOffdiagDecoratedTargetOrbitProfile G sites i j q y)



theorem lpReplicaOffdiag_source_target_transferComponent_eq
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    lpReplicaOffdiagDecoratedSourceTransferComponent G sites i j q z =
      lpReplicaOffdiagDecoratedTargetTransferComponent G sites i j q y := by
  exact lpReplicaCommonOrbitTransferGraph_component_eq G sites q
    (lpReplicaOffdiagDecoratedSourceOrbitProfile G sites i j q z)
    (lpReplicaOffdiagDecoratedTargetOrbitProfile G sites i j q y)


noncomputable def lpReplicaOffdiagDecoratedSourcesInTransferComponent
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : (lpReplicaCommonOrbitTransferGraph G sites q).ConnectedComponent) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact Finset.univ.filter fun z =>
    lpReplicaOffdiagDecoratedSourceTransferComponent G sites i j q z = c


noncomputable def lpReplicaOffdiagBalancedOutputsInTransferComponent
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : (lpReplicaCommonOrbitTransferGraph G sites q).ConnectedComponent) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact (lpReplicaOffdiagBalancedOutputs G sites i j q).filter fun y =>
    lpReplicaOffdiagDecoratedTargetTransferComponent G sites i j q y = c




noncomputable def lpReplicaOffdiagBalancedRelevantTransferComponents
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset
      (lpReplicaCommonOrbitTransferGraph G sites q).ConnectedComponent := by
  classical
  exact ((Finset.univ : Finset
      (LPReplicaOffdiagDecoratedSource G sites i j q)).image
        (lpReplicaOffdiagDecoratedSourceTransferComponent G sites i j q)) ∪
    (lpReplicaOffdiagBalancedOutputs G sites i j q).image
      (lpReplicaOffdiagDecoratedTargetTransferComponent G sites i j q)

theorem lpReplicaOffdiagDecoratedSource_card_eq_sum_transferComponents
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) =
      ∑ c ∈ lpReplicaOffdiagBalancedRelevantTransferComponents
          G sites i j q,
        (lpReplicaOffdiagDecoratedSourcesInTransferComponent
          G sites i j q c).card := by
  classical
  rw [← Finset.card_univ]
  simpa only [lpReplicaOffdiagDecoratedSourcesInTransferComponent] using
    Finset.card_eq_sum_card_fiberwise (by
      intro z hz
      unfold lpReplicaOffdiagBalancedRelevantTransferComponents
      exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_image.mpr ⟨z, hz, rfl⟩)))

theorem lpReplicaOffdiagBalancedOutputs_card_eq_sum_transferComponents
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaOffdiagBalancedOutputs G sites i j q).card =
      ∑ c ∈ lpReplicaOffdiagBalancedRelevantTransferComponents
          G sites i j q,
        (lpReplicaOffdiagBalancedOutputsInTransferComponent
          G sites i j q c).card := by
  classical
  simpa only [lpReplicaOffdiagBalancedOutputsInTransferComponent] using
    Finset.card_eq_sum_card_fiberwise (by
      intro y hy
      unfold lpReplicaOffdiagBalancedRelevantTransferComponents
      exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_image.mpr ⟨y, hy, rfl⟩)))



theorem lpReplicaOffdiagOrbitAtomCardInequality_of_transferComponentCards
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : ∀ c ∈ lpReplicaOffdiagBalancedRelevantTransferComponents
        G sites i j q,
      (lpReplicaOffdiagDecoratedSourcesInTransferComponent
          G sites i j q c).card <=
        (lpReplicaOffdiagBalancedOutputsInTransferComponent
          G sites i j q c).card) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  apply lpReplicaOffdiagOrbitAtomCardInequality_of_balancedOutputCard
  rw [lpReplicaOffdiagDecoratedSource_card_eq_sum_transferComponents,
    lpReplicaOffdiagBalancedOutputs_card_eq_sum_transferComponents]
  exact Finset.sum_le_sum hcard

end

end StatMech.Ising
