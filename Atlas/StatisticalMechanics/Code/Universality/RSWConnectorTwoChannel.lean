/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWConnectorCentralFaceFilledBoundary
import Code.Foundations.WeightedFiniteInjection












open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section





noncomputable def rlc_connectorTwoChannelGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y :=
    ((rlc_connectorCentralFaceFiniteGraph gamma gamma').Adj x y ∨
      (rlc_connectorReflectedTraceWiring gamma gamma').Adj x y) ∧
        ¬ (rlc_connectorTraceWiring gamma gamma').Adj x y
  symm := by
    rintro x y ⟨hxy, hnot⟩
    exact ⟨hxy.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm),
      fun hyx => hnot hyx.symm⟩
  loopless := ⟨fun x hxx => hxx.1.elim
    (fun h => h.ne rfl) (fun h => h.ne rfl)⟩

noncomputable instance rlc_connectorTwoChannelGraphDecidableAdj
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_connectorTwoChannelGraph gamma gamma').Adj :=
  Classical.decRel _


def rlc_finiteTwoChannelConnectorEvent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (ConfigSpace (Sym2 (RlcConnectorVertex n))) :=
  {rho | ∃ x y : RlcConnectorVertex n,
    rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
      (FK.openSub (rlc_connectorTwoChannelGraph gamma gamma') rho).Reachable
        x y}

theorem rlc_connectorCentralFaceFiniteGraph_le_twoChannel {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_connectorCentralFaceFiniteGraph gamma gamma' ≤
      rlc_connectorTwoChannelGraph gamma gamma' :=
  by
    intro x y hxy
    refine ⟨Or.inl hxy, ?_⟩
    intro htrace
    apply Finset.disjoint_left.mp
      (rlc_connectorCentralFaceEdges_disjoint_fourTrace gamma gamma')
      hxy.2
    exact Finset.mem_union_left _ htrace.2

theorem rlc_finiteCentralFaceRandomConnectorEvent_subset_twoChannel
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    rlc_finiteCentralFaceRandomConnectorEvent gamma gamma' ⊆
      rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
  rintro rho ⟨x, y, hx, hy, hxy⟩
  refine ⟨x, y, hx, hy, hxy.mono ?_⟩
  intro u v huv
  rw [FK.openSub_adj] at huv ⊢
  exact ⟨rlc_connectorCentralFaceFiniteGraph_le_twoChannel
    gamma gamma' huv.1, huv.2⟩



theorem rlc_connectorCentralFaceClosureGraph_eq_twoChannel_sup_trace
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    rlc_connectorCentralFaceClosureGraph gamma gamma' =
      rlc_connectorTwoChannelGraph gamma gamma' ⊔
        rlc_connectorTraceWiring gamma gamma' := by
  ext x y
  simp only [rlc_connectorCentralFaceClosureGraph,
    rlc_connectorTwoChannelGraph, rlc_connectorCentralFaceFiniteGraph,
    rlc_connectorReflectedTraceWiring, rlc_connectorTraceWiring,
    SimpleGraph.sup_adj]
  constructor
  · rintro ⟨hxy, hedge⟩
    rw [rlc_connectorCentralFacePlanarEdges, Finset.mem_union] at hedge
    rcases hedge with hclosure | hfour
    · by_cases hwall : s((x : Site 2), (y : Site 2)) ∈
          rlc_connectorFourTraceEdges gamma gamma'
      · rw [rlc_connectorFourTraceEdges, Finset.mem_union] at hwall
        rcases hwall with horiginal | hreflected
        · exact Or.inr ⟨hxy, horiginal⟩
        · by_cases horiginal : s((x : Site 2), (y : Site 2)) ∈
              rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
          · exact Or.inr ⟨hxy, horiginal⟩
          · exact Or.inl ⟨Or.inr ⟨hxy, hreflected⟩,
              fun htrace => horiginal htrace.2⟩
      · exact Or.inl ⟨Or.inl ⟨hxy,
          Finset.mem_sdiff.mpr ⟨hclosure, hwall⟩⟩, fun htrace =>
            hwall (Finset.mem_union_left _ htrace.2)⟩
    · rw [rlc_connectorFourTraceEdges, Finset.mem_union] at hfour
      rcases hfour with horiginal | hreflected
      · exact Or.inr ⟨hxy, horiginal⟩
      · by_cases horiginal : s((x : Site 2), (y : Site 2)) ∈
            rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
        · exact Or.inr ⟨hxy, horiginal⟩
        · exact Or.inl ⟨Or.inr ⟨hxy, hreflected⟩,
            fun htrace => horiginal htrace.2⟩
  · rintro (htwo | htrace)
    · rcases htwo with ⟨hchannel, _hnot⟩
      rcases hchannel with ⟨hxy, hcentral⟩ | ⟨hxy, hreflected⟩
      · exact ⟨hxy, Finset.mem_union_left _
          (Finset.mem_sdiff.mp hcentral).1⟩
      · exact ⟨hxy, Finset.mem_union_right _ <|
          Finset.mem_union_right _ hreflected⟩
    · rcases htrace with ⟨hxy, horiginal⟩
      exact ⟨hxy, Finset.mem_union_right _ <|
        Finset.mem_union_left _ horiginal⟩



def rlc_connectorTwoChannelAugmentedPlanarDomain {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Lattice.PlanarZ2Subgraph where
  V := RlcConnectorVertex n
  finV := inferInstance
  decV := inferInstance
  G := rlc_connectorTwoChannelGraph gamma gamma' ⊔
    rlc_connectorTraceWiring gamma gamma'
  emb := ⟨Subtype.val, Subtype.val_injective⟩
  isSub := by
    intro x y hxy
    rcases hxy with ⟨hcentral | hreflected, _hnot⟩ | htrace
    · exact hcentral.1
    · exact hreflected.1
    · exact htrace.1



theorem rlc_connectorTwoChannelAugmentedGraph_eq_closure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G =
      rlc_connectorCentralFaceClosureGraph gamma gamma' := by
  exact (rlc_connectorCentralFaceClosureGraph_eq_twoChannel_sup_trace
    gamma gamma').symm



theorem rlc_twoChannel_numClustersBC_traceWiring_eq_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorTraceWiring gamma gamma') rho =
      FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') rho := by
  unfold FK.numClustersBC
  exact Nat.card_congr (rlc_connectorTraceComponentEquiv gamma gamma'
    (FK.openSub (rlc_connectorTwoChannelGraph gamma gamma') rho))

theorem rlc_twoChannel_bcWeight_traceWiring_eq_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.bcWeight (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorTraceWiring gamma gamma') p q rho =
      FK.bcWeight (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q rho := by
  unfold FK.bcWeight
  rw [rlc_twoChannel_numClustersBC_traceWiring_eq_separateWiring]

theorem rlc_twoChannel_bcZ_traceWiring_eq_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) :
    FK.bcZ (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorTraceWiring gamma gamma') p q =
      FK.bcZ (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q := by
  unfold FK.bcZ
  apply Finset.sum_congr rfl
  intro rho _
  exact rlc_twoChannel_bcWeight_traceWiring_eq_separateWiring
    gamma gamma' p q rho

theorem rlc_twoChannel_bcProb_traceWiring_eq_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorTraceWiring gamma gamma') p q rho =
      FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q rho := by
  unfold FK.bcProb
  rw [rlc_twoChannel_bcWeight_traceWiring_eq_separateWiring,
    rlc_twoChannel_bcZ_traceWiring_eq_separateWiring]

theorem rlc_twoChannel_bcEventMass_traceWiring_eq_separateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n)))) :
    FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorTraceWiring gamma gamma') p q A =
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q A := by
  unfold FK.bcEventMass
  apply Finset.sum_congr rfl
  intro rho _
  rw [rlc_twoChannel_bcProb_traceWiring_eq_separateWiring]



theorem rlc_openSub_twoChannelAugmented_forceTrace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openSub (rlc_connectorTwoChannelAugmentedPlanarDomain
          gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' rho) =
      FK.openSub (rlc_connectorTwoChannelGraph gamma gamma') rho ⊔
        rlc_connectorTraceWiring gamma gamma' := by
  ext x y
  simp only [FK.openSub_adj,
    rlc_connectorTwoChannelAugmentedPlanarDomain, SimpleGraph.sup_adj]
  by_cases htrace :
      (rlc_connectorTraceWiring gamma gamma').Adj x y
  · simp [rlc_connectorForceTraceConfig, htrace]
  · simp [rlc_connectorForceTraceConfig, htrace]

theorem rlc_connectorTwoChannelGraph_adj_not_traceWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcConnectorVertex n}
    (hxy : (rlc_connectorTwoChannelGraph gamma gamma').Adj x y) :
    ¬ (rlc_connectorTraceWiring gamma gamma').Adj x y :=
  hxy.2

theorem rlc_twoChannel_numClusters_augmented_forceTrace_eq_traceBC
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.numClusters (rlc_connectorTwoChannelAugmentedPlanarDomain
        gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' rho) =
      FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorTraceWiring gamma gamma') rho := by
  let A := FK.openSub
    (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
    (rlc_connectorForceTraceConfig gamma gamma' rho)
  let B := FK.openSub (rlc_connectorTwoChannelGraph gamma gamma') rho ⊔
    rlc_connectorTraceWiring gamma gamma'
  have hAB : A = B :=
    rlc_openSub_twoChannelAugmented_forceTrace gamma gamma' rho
  have htypes : A.ConnectedComponent = B.ConnectedComponent :=
    congrArg (fun H : SimpleGraph (RlcConnectorVertex n) =>
      H.ConnectedComponent) hAB
  unfold FK.numClusters FK.numClustersBC
  calc
    Fintype.card A.ConnectedComponent = Nat.card A.ConnectedComponent :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card B.ConnectedComponent :=
      Nat.card_congr (Equiv.cast htypes)

theorem rlc_twoChannel_edgeProduct_augmented_forceTrace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p : Real) (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.edgeProduct (rlc_connectorTwoChannelAugmentedPlanarDomain
        gamma gamma').G p
        (rlc_connectorForceTraceConfig gamma gamma' rho) =
      p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        FK.edgeProduct (rlc_connectorTwoChannelGraph gamma gamma') p rho := by
  classical
  let G := rlc_connectorTwoChannelGraph gamma gamma'
  let T := rlc_connectorTraceWiring gamma gamma'
  have hd : Disjoint G.edgeFinset T.edgeFinset := by
    rw [Finset.disjoint_left]
    intro e heG heT
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hG : G.Adj x y := (SimpleGraph.mem_edgeSet G).mp
          (SimpleGraph.mem_edgeFinset.mp heG)
        have hT : T.Adj x y := (SimpleGraph.mem_edgeSet T).mp
          (SimpleGraph.mem_edgeFinset.mp heT)
        exact rlc_connectorTwoChannelGraph_adj_not_traceWiring
          gamma gamma' hG hT
  have hGprod :
      (∏ e ∈ G.edgeFinset,
          if rlc_connectorForceTraceConfig gamma gamma' rho e
            then p else 1 - p) =
        ∏ e ∈ G.edgeFinset, if rho e then p else 1 - p := by
    apply Finset.prod_congr rfl
    intro e heG
    have hnot : e ∉ T.edgeFinset := Finset.disjoint_left.mp hd heG
    simp [rlc_connectorForceTraceConfig, T, hnot]
  have hTprod :
      (∏ e ∈ T.edgeFinset,
          if rlc_connectorForceTraceConfig gamma gamma' rho e
            then p else 1 - p) = p ^ T.edgeFinset.card := by
    calc
      (∏ e ∈ T.edgeFinset,
          if rlc_connectorForceTraceConfig gamma gamma' rho e
            then p else 1 - p) = ∏ _e ∈ T.edgeFinset, p := by
        apply Finset.prod_congr rfl
        intro e heT
        simp [rlc_connectorForceTraceConfig, T, heT]
      _ = p ^ T.edgeFinset.card := by simp
  unfold FK.edgeProduct
  have hEdges :
      (rlc_connectorTwoChannelAugmentedPlanarDomain
        gamma gamma').G.edgeFinset = G.edgeFinset ∪ T.edgeFinset := by
    simp [rlc_connectorTwoChannelAugmentedPlanarDomain, G, T]
  rw [hEdges]
  calc
    (∏ e ∈ G.edgeFinset ∪ T.edgeFinset,
        if rlc_connectorForceTraceConfig gamma gamma' rho e
          then p else 1 - p) =
        (∏ e ∈ G.edgeFinset,
          if rlc_connectorForceTraceConfig gamma gamma' rho e
            then p else 1 - p) *
        ∏ e ∈ T.edgeFinset,
          if rlc_connectorForceTraceConfig gamma gamma' rho e
            then p else 1 - p := Finset.prod_union hd
    _ = (∏ e ∈ G.edgeFinset, if rho e then p else 1 - p) *
        p ^ T.edgeFinset.card := by rw [hGprod, hTprod]
    _ = p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        ∏ e ∈ (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset,
          if rho e then p else 1 - p := by
      simp only [G, T, mul_comm]



theorem rlc_twoChannel_fkWeight_augmented_forceTrace_eq_separateBC {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.fkWeight (rlc_connectorTwoChannelAugmentedPlanarDomain
        gamma gamma').G p q
        (rlc_connectorForceTraceConfig gamma gamma' rho) =
      p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        FK.bcWeight (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') p q rho := by
  unfold FK.fkWeight FK.bcWeight
  rw [rlc_twoChannel_edgeProduct_augmented_forceTrace,
    rlc_twoChannel_numClusters_augmented_forceTrace_eq_traceBC,
    rlc_twoChannel_numClustersBC_traceWiring_eq_separateWiring]
  ring

theorem rlc_twoChannelForced_weight_duality {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'
    p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
          FK.bcWeight (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorSeparateWiring gamma gamma') p q rho *
        q ^ (P.G.edgeFinset.card + 1) =
      (p / (1 - BeffaraDC.dualParam p q)) ^ P.G.edgeFinset.card *
        q ^ Nat.card P.V *
          BeffaraDC.pfdDualWeight P (BeffaraDC.dualParam p q) q
            (FK.openSub P.G
              (rlc_connectorForceTraceConfig gamma gamma' rho)) := by
  dsimp only
  rw [← rlc_twoChannel_fkWeight_augmented_forceTrace_eq_separateBC]
  exact BeffaraDC.pfd_fkWeight_duality
    (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
    (rlc_connectorForceTraceConfig gamma gamma' rho) hp hp1 hq

noncomputable def rlc_twoChannelForcedDualZ {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) : Real :=
  let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'
  ∑ rho : ConfigSpace (Sym2 (RlcConnectorVertex n)),
    BeffaraDC.pfdDualWeight P p q
      (FK.openSub P.G (rlc_connectorForceTraceConfig gamma gamma' rho))

noncomputable def rlc_twoChannelForcedDualProb {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Real :=
  let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'
  BeffaraDC.pfdDualWeight P p q
      (FK.openSub P.G (rlc_connectorForceTraceConfig gamma gamma' rho)) /
    rlc_twoChannelForcedDualZ gamma gamma' p q

theorem rlc_twoChannelForcedDualZ_pos {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < rlc_twoChannelForcedDualZ gamma gamma' p q := by
  unfold rlc_twoChannelForcedDualZ
  exact Finset.sum_pos
    (fun rho _ => BeffaraDC.pfd_dualWeight_pos
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' rho)) hp hp1 hq)
    Finset.univ_nonempty

theorem rlc_twoChannelForced_partition_duality {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'
    p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
          FK.bcZ (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorSeparateWiring gamma gamma') p q *
        q ^ (P.G.edgeFinset.card + 1) =
      (p / (1 - BeffaraDC.dualParam p q)) ^ P.G.edgeFinset.card *
        q ^ Nat.card P.V *
          rlc_twoChannelForcedDualZ gamma gamma'
            (BeffaraDC.dualParam p q) q := by
  dsimp only
  let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'
  let t : Real := p ^
    (rlc_connectorTraceWiring gamma gamma').edgeFinset.card
  let A : Real := q ^ (P.G.edgeFinset.card + 1)
  let B : Real :=
    (p / (1 - BeffaraDC.dualParam p q)) ^ P.G.edgeFinset.card *
      q ^ Nat.card P.V
  unfold FK.bcZ rlc_twoChannelForcedDualZ
  calc
    t * (∑ rho, FK.bcWeight (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q rho) * A =
      ∑ rho, t * FK.bcWeight (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q rho * A := by
          rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ rho, B * BeffaraDC.pfdDualWeight P
        (BeffaraDC.dualParam p q) q
        (FK.openSub P.G
          (rlc_connectorForceTraceConfig gamma gamma' rho)) := by
      apply Finset.sum_congr rfl
      intro rho _
      exact rlc_twoChannelForced_weight_duality
        gamma gamma' rho hp hp1 hq
    _ = B * ∑ rho, BeffaraDC.pfdDualWeight P
        (BeffaraDC.dualParam p q) q
        (FK.openSub P.G
          (rlc_connectorForceTraceConfig gamma gamma' rho)) := by
      rw [Finset.mul_sum]

theorem rlc_twoChannel_bcProb_separate_eq_forcedDualProb {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q rho =
      rlc_twoChannelForcedDualProb gamma gamma'
        (BeffaraDC.dualParam p q) q rho := by
  have hps0 : 0 < BeffaraDC.dualParam p q :=
    BeffaraDC.dualParam_pos hp hp1 hq
  have hps1 : BeffaraDC.dualParam p q < 1 :=
    BeffaraDC.dualParam_lt_one hp hp1 hq
  have hZp : FK.bcZ (rlc_connectorTwoChannelGraph gamma gamma')
      (rlc_connectorSeparateWiring gamma gamma') p q ≠ 0 :=
    (FK.bcZ_pos (rlc_connectorTwoChannelGraph gamma gamma')
      (rlc_connectorSeparateWiring gamma gamma') hp hp1 hq).ne'
  have hZd : rlc_twoChannelForcedDualZ gamma gamma'
      (BeffaraDC.dualParam p q) q ≠ 0 :=
    (rlc_twoChannelForcedDualZ_pos gamma gamma' hps0 hps1 hq).ne'
  let C : Real :=
    p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
      q ^ ((rlc_connectorTwoChannelAugmentedPlanarDomain
        gamma gamma').G.edgeFinset.card + 1)
  let B : Real :=
    (p / (1 - BeffaraDC.dualParam p q)) ^
        (rlc_connectorTwoChannelAugmentedPlanarDomain
          gamma gamma').G.edgeFinset.card *
      q ^ Nat.card
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').V
  let wp := FK.bcWeight (rlc_connectorTwoChannelGraph gamma gamma')
    (rlc_connectorSeparateWiring gamma gamma') p q rho
  let wd := BeffaraDC.pfdDualWeight
    (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
    (BeffaraDC.dualParam p q) q
    (FK.openSub
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
      (rlc_connectorForceTraceConfig gamma gamma' rho))
  have hC : 0 < C := mul_pos (pow_pos hp _) (pow_pos hq _)
  have hB : 0 < B := by
    have hden : 0 < 1 - BeffaraDC.dualParam p q := by linarith
    exact mul_pos (pow_pos (div_pos hp hden) _) (pow_pos hq _)
  have hw : wp * C = B * wd := by
    have h := rlc_twoChannelForced_weight_duality
      gamma gamma' rho hp hp1 hq
    dsimp only at h
    dsimp only [wp, wd, C, B]
    calc
      _ = p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
          FK.bcWeight (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorSeparateWiring gamma gamma') p q rho *
          q ^ ((rlc_connectorTwoChannelAugmentedPlanarDomain
            gamma gamma').G.edgeFinset.card + 1) := by ring
      _ = _ := h
  have hZ : FK.bcZ (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q * C =
      B * rlc_twoChannelForcedDualZ gamma gamma'
        (BeffaraDC.dualParam p q) q := by
    have h := rlc_twoChannelForced_partition_duality
      gamma gamma' hp hp1 hq
    dsimp only at h
    dsimp only [C, B]
    calc
      _ = p ^ (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
          FK.bcZ (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorSeparateWiring gamma gamma') p q *
          q ^ ((rlc_connectorTwoChannelAugmentedPlanarDomain
            gamma gamma').G.edgeFinset.card + 1) := by ring
      _ = _ := h
  have hcrossCB :
      C * (B * (wp * rlc_twoChannelForcedDualZ gamma gamma'
        (BeffaraDC.dualParam p q) q)) =
      C * (B * (wd * FK.bcZ
        (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q)) := by
    calc
      C * (B * (wp * rlc_twoChannelForcedDualZ gamma gamma'
          (BeffaraDC.dualParam p q) q)) =
        (wp * C) * (B * rlc_twoChannelForcedDualZ gamma gamma'
          (BeffaraDC.dualParam p q) q) := by ring
      _ = (B * wd) *
          (FK.bcZ (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorSeparateWiring gamma gamma') p q * C) := by
        rw [hw, hZ]
      _ = C * (B * (wd * FK.bcZ
          (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') p q)) := by ring
  have hcrossB := mul_left_cancel₀ hC.ne' hcrossCB
  have hcross : wp * rlc_twoChannelForcedDualZ gamma gamma'
      (BeffaraDC.dualParam p q) q =
      wd * FK.bcZ (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q :=
    mul_left_cancel₀ hB.ne' hcrossB
  unfold FK.bcProb rlc_twoChannelForcedDualProb
  exact (div_eq_div_iff hZp hZd).2 hcross

noncomputable def rlc_twoChannelForcedDualEventMass {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n)))) : Real :=
  ∑ rho : ConfigSpace (Sym2 (RlcConnectorVertex n)),
    A.indicator (fun _ => (1 : Real)) rho *
      rlc_twoChannelForcedDualProb gamma gamma' p q rho

theorem rlc_twoChannelForcedDualProb_nonneg {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    0 ≤ rlc_twoChannelForcedDualProb gamma gamma' p q rho := by
  unfold rlc_twoChannelForcedDualProb
  exact div_nonneg
    (le_of_lt (BeffaraDC.pfd_dualWeight_pos
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' rho)) hp hp1 hq))
    (le_of_lt (rlc_twoChannelForcedDualZ_pos
      gamma gamma' hp hp1 hq))



theorem rlc_bcProb_half_q_one_uniform {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C D : SimpleGraph V) [DecidableRel C.Adj] [DecidableRel D.Adj]
    (rho eta : ConfigSpace (Sym2 V)) :
    FK.bcProb G C (1 / 2 : Real) 1 rho =
      FK.bcProb G D (1 / 2 : Real) 1 eta := by
  classical
  unfold FK.bcProb FK.bcZ FK.bcWeight FK.edgeProduct
  simp only [one_pow, mul_one]
  have huniform (omega : ConfigSpace (Sym2 V)) :
      (∏ e ∈ G.edgeFinset,
        if omega e = true then (1 / 2 : Real) else 1 - 1 / 2) =
      (1 / 2 : Real) ^ G.edgeFinset.card := by
    calc
      _ = ∏ _e ∈ G.edgeFinset, (1 / 2 : Real) := by
        apply Finset.prod_congr rfl
        intro e _
        split <;> norm_num
      _ = _ := by simp
  simp_rw [huniform]



theorem rlc_twoChannelForcedDualProb_half_q_one_eq_merged {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho eta : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_twoChannelForcedDualProb gamma gamma' (1 / 2) 1 rho =
      FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1 eta := by
  have hdual := rlc_twoChannel_bcProb_separate_eq_forcedDualProb
    gamma gamma' rho (p := (1 / 2 : Real)) (q := (1 : Real))
      (by norm_num) (by norm_num) (by norm_num)
  norm_num [BeffaraDC.dualParam] at hdual
  rw [← hdual]
  exact rlc_bcProb_half_q_one_uniform
    (rlc_connectorTwoChannelGraph gamma gamma')
    (rlc_connectorSeparateWiring gamma gamma')
    (rlc_connectorMergedWiring gamma gamma') rho eta




theorem rlc_twoChannelForcedDualSingletonMass_le_merged_of_mem {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho eta : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (heta : eta ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    rlc_twoChannelForcedDualEventMass gamma gamma' (1 / 2) 1 {rho} ≤
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  classical
  unfold rlc_twoChannelForcedDualEventMass FK.bcEventMass
  calc
    (∑ omega : ConfigSpace (Sym2 (RlcConnectorVertex n)),
        ({rho} : Set (ConfigSpace (Sym2 (RlcConnectorVertex n)))).indicator
          (fun _ => (1 : Real)) omega *
          rlc_twoChannelForcedDualProb gamma gamma' (1 / 2) 1 omega) =
      rlc_twoChannelForcedDualProb gamma gamma' (1 / 2) 1 rho := by
        rw [Finset.sum_eq_single rho]
        · simp
        · intro omega _ hne
          simp [hne]
        · simp
    _ = FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1 eta :=
      rlc_twoChannelForcedDualProb_half_q_one_eq_merged
        gamma gamma' rho eta
    _ ≤ ∑ omega : ConfigSpace (Sym2 (RlcConnectorVertex n)),
        (rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator
          (fun _ => (1 : Real)) omega *
          FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1 omega := by
      have hle := Finset.single_le_sum (s := Finset.univ)
        (f := fun omega : ConfigSpace (Sym2 (RlcConnectorVertex n)) =>
          (rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator
            (fun _ => (1 : Real)) omega *
            FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
              (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1 omega)
        (fun omega _ => mul_nonneg
          (Set.indicator_nonneg (fun _ _ => zero_le_one) omega)
          (FK.bcProb_nonneg (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma') (by norm_num)
              (by norm_num) (by norm_num) omega))
        (Finset.mem_univ eta)
      simpa [heta] using hle

theorem rlc_twoChannel_bcEventMass_separate_eq_forcedDualEventMass {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n))))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q A =
      rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.dualParam p q) q A := by
  unfold FK.bcEventMass rlc_twoChannelForcedDualEventMass
  apply Finset.sum_congr rfl
  intro rho _
  rw [rlc_twoChannel_bcProb_separate_eq_forcedDualProb
    gamma gamma' rho hp hp1 hq]

theorem rlc_twoChannel_bcEventMass_separate_selfDual_eq_forcedDualEventMass
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A : Set (ConfigSpace (Sym2 (RlcConnectorVertex n))))
    {q : Real} (hq : 0 < q) :
    FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q A =
      rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q A := by
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq
  simpa only [BeffaraDC.selfDualPoint_is_fixed hq] using
    rlc_twoChannel_bcEventMass_separate_eq_forcedDualEventMass
      gamma gamma' A hp hp1 hq

theorem rlc_twoChannel_bcProb_separate_selfDual_eq_forcedDualProb
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {q : Real} (hq : 0 < q) :
    FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q rho =
      rlc_twoChannelForcedDualProb gamma gamma'
        (BeffaraDC.selfDualPoint q) q rho := by
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq
  simpa only [BeffaraDC.selfDualPoint_is_fixed hq] using
    rlc_twoChannel_bcProb_separate_eq_forcedDualProb
      gamma gamma' rho hp hp1 hq



theorem rlc_finiteCentralFaceClosureConnectorEvent_subset_twoChannel
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' ⊆
      rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
  intro rho hclosure
  have hanchorsClosure :
      (FK.openSub (rlc_connectorCentralFaceClosureGraph gamma gamma') rho ⊔
        rlc_connectorTraceWiring gamma gamma').Reachable
          (rlc_connectorRightAnchor gamma)
          (rlc_connectorLeftAnchor gamma') :=
    (rlc_exists_connector_iff_traceAnchors gamma gamma'
      (FK.openSub (rlc_connectorCentralFaceClosureGraph gamma gamma') rho)).1
        hclosure
  have hopenLe :
      FK.openSub (rlc_connectorCentralFaceClosureGraph gamma gamma') rho ≤
        FK.openSub (rlc_connectorTwoChannelGraph gamma gamma') rho ⊔
          rlc_connectorTraceWiring gamma gamma' := by
    intro x y hxy
    rw [FK.openSub_adj] at hxy
    rw [rlc_connectorCentralFaceClosureGraph_eq_twoChannel_sup_trace]
      at hxy
    rcases hxy.1 with htwo | htrace
    · exact Or.inl ⟨htwo, hxy.2⟩
    · exact Or.inr htrace
  have hanchorsTwo :
      (FK.openSub (rlc_connectorTwoChannelGraph gamma gamma') rho ⊔
        rlc_connectorTraceWiring gamma gamma').Reachable
          (rlc_connectorRightAnchor gamma)
          (rlc_connectorLeftAnchor gamma') :=
    hanchorsClosure.mono <| sup_le hopenLe le_sup_right
  exact (rlc_exists_connector_iff_traceAnchors gamma gamma'
    (FK.openSub (rlc_connectorTwoChannelGraph gamma gamma') rho)).2
      hanchorsTwo



theorem rlc_centralFacePIMS_twoChannel_success_of_closure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hclosure : rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
      rlc_finiteCentralFaceClosureConnectorEvent gamma gamma') :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
      rlc_finiteTwoChannelConnectorEvent gamma gamma' :=
  rlc_finiteCentralFaceClosureConnectorEvent_subset_twoChannel
    gamma gamma' hclosure



def RlcTwoChannelClosureFailureCertificate {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) : Prop :=
  ∀ rho : ConfigSpace (Sym2 (RlcConnectorVertex n)),
    rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma' →
      rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
        rlc_finiteCentralFaceClosureConnectorEvent gamma gamma'




def RlcCentralFaceClosureFailureCertificate {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) : Prop :=
  ∀ rho : ConfigSpace (Sym2 (RlcConnectorVertex n)),
    rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma' →
      rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
        rlc_finiteCentralFaceClosureConnectorEvent gamma gamma'




theorem rlc_twoChannelClosureFailureCertificate_of_centralFace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hcentral : RlcCentralFaceClosureFailureCertificate gamma gamma') :
    RlcTwoChannelClosureFailureCertificate gamma gamma' := by
  intro rho hno
  apply hcentral rho
  intro hcentralSuccess
  exact hno (rlc_finiteCentralFaceRandomConnectorEvent_subset_twoChannel
    gamma gamma' hcentralSuccess)



theorem rlc_twoChannelPIMS_success_of_closureFailureCertificate {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfailure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
      rlc_finiteTwoChannelConnectorEvent gamma gamma' :=
  rlc_centralFacePIMS_twoChannel_success_of_closure gamma gamma' rho
    (hfailure rho hno)

theorem rlc_finiteTwoChannelConnectorEvent_isIncreasing {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    IsIncreasing (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  intro rho rho' hrho
  rintro ⟨x, y, hx, hy, hxy⟩
  exact ⟨x, y, hx, hy, hxy.mono (FK.openSub_mono _ hrho)⟩





noncomputable def rlc_twoChannelPIMSFailureImageMass {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) : Real :=
  ∑ rho : ConfigSpace (Sym2 (RlcConnectorVertex n)),
    (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ.indicator
      (fun _ => (1 : Real)) rho *
        (rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator
          (fun _ => (1 : Real))
          (rlc_connectorCentralFacePIMSConfig gamma gamma' rho) *
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') p q rho



noncomputable def rlc_twoChannelForcedDualFailureImageMass {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) : Real :=
  ∑ rho : ConfigSpace (Sym2 (RlcConnectorVertex n)),
    (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ.indicator
      (fun _ => (1 : Real)) rho *
        (rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator
          (fun _ => (1 : Real))
          (rlc_connectorCentralFacePIMSConfig gamma gamma' rho) *
        rlc_twoChannelForcedDualProb gamma gamma' p q rho



theorem rlc_twoChannelPIMSFailureImageMass_eq_forcedDual {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 0 < q) :
    rlc_twoChannelPIMSFailureImageMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q =
      rlc_twoChannelForcedDualFailureImageMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q := by
  unfold rlc_twoChannelPIMSFailureImageMass
    rlc_twoChannelForcedDualFailureImageMass
  apply Finset.sum_congr rfl
  intro rho _
  rw [rlc_twoChannel_bcProb_separate_selfDual_eq_forcedDualProb
    gamma gamma' rho hq]



theorem rlc_twoChannel_failureMass_eq_PIMSFailureImageMass {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (hfailure : RlcTwoChannelClosureFailureCertificate gamma gamma') :
    FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ =
      rlc_twoChannelPIMSFailureImageMass gamma gamma' p q := by
  classical
  unfold FK.bcEventMass rlc_twoChannelPIMSFailureImageMass
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hrho : rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma'
  · rw [Set.indicator_of_notMem (by simpa using hrho)]
    simp
  · rw [Set.indicator_of_mem (by simpa using hrho),
      Set.indicator_of_mem
        (rlc_twoChannelPIMS_success_of_closureFailureCertificate
          gamma gamma' hfailure rho hrho)]
    simp



theorem rlc_twoChannelForcedDualFailureImageMass_eq_compl {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (hfailure : RlcTwoChannelClosureFailureCertificate gamma gamma') :
    rlc_twoChannelForcedDualFailureImageMass gamma gamma' p q =
      rlc_twoChannelForcedDualEventMass gamma gamma' p q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ := by
  classical
  unfold rlc_twoChannelForcedDualFailureImageMass
    rlc_twoChannelForcedDualEventMass
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hrho : rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma'
  · rw [Set.indicator_of_notMem (by simpa using hrho)]
    simp
  · rw [Set.indicator_of_mem (by simpa using hrho),
      Set.indicator_of_mem
        (rlc_twoChannelPIMS_success_of_closureFailureCertificate
          gamma gamma' hfailure rho hrho)]
    simp




theorem rlc_twoChannelForcedDualEventMass_compl_le_merged_of_equiv {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 ≤ q)
    (D : ConfigSpace (Sym2 (RlcConnectorVertex n)) ≃
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hfailure : ∀ rho,
      rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma' →
        D rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hprob : ∀ rho,
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q rho ≤
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q (D rho)) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ ≤
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  unfold rlc_twoChannelForcedDualEventMass FK.bcEventMass
  rw [← Equiv.sum_comp D (fun eta :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) =>
      (rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator
        (fun _ => (1 : Real)) eta *
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q eta)]
  apply Finset.sum_le_sum
  intro rho _
  by_cases hrho : rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma'
  · rw [Set.indicator_of_notMem (by simpa using hrho)]
    simp only [zero_mul]
    exact mul_nonneg (by
      by_cases hD : D rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma'
      <;> simp [hD])
      (FK.bcProb_nonneg (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') hp hp1 hq0 (D rho))
  · rw [Set.indicator_of_mem (by simpa using hrho),
      Set.indicator_of_mem (hfailure rho hrho)]
    simpa using hprob rho





theorem rlc_twoChannelForcedDualEventMass_compl_le_merged_of_injection
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 ≤ q)
    (D : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} →
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hinj : Function.Injective D)
    (hsuccess : ∀ rho,
      D rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hprob : ∀ rho,
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q rho.1 ≤
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q (D rho)) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ ≤
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  classical
  let A := rlc_finiteTwoChannelConnectorEvent gamma gamma'
  let source := {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) // rho ∉ A}
  let range : Set (ConfigSpace (Sym2 (RlcConnectorVertex n))) := Set.range D
  let e : source ≃ range := Equiv.ofInjective D hinj
  have hrange : range ⊆ A := by
    rintro eta ⟨rho, rfl⟩
    exact hsuccess rho
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  unfold rlc_twoChannelForcedDualEventMass FK.bcEventMass
  calc
    (∑ rho : ConfigSpace (Sym2 (RlcConnectorVertex n)),
        Aᶜ.indicator (fun _ => (1 : Real)) rho *
          rlc_twoChannelForcedDualProb gamma gamma'
            (BeffaraDC.selfDualPoint q) q rho) =
        ∑ rho : source,
          rlc_twoChannelForcedDualProb gamma gamma'
            (BeffaraDC.selfDualPoint q) q rho.1 := by
      calc
        _ = ∑ rho ∈ Finset.univ.filter (fun rho => rho ∉ A),
            rlc_twoChannelForcedDualProb gamma gamma'
              (BeffaraDC.selfDualPoint q) q rho := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro rho _
          by_cases hrho : rho ∈ A <;> simp [hrho]
        _ = _ := Finset.sum_subtype
          (Finset.univ.filter (fun rho => rho ∉ A))
            (by intro rho; simp only [Finset.mem_filter, Finset.mem_univ,
              true_and]) (fun rho =>
            rlc_twoChannelForcedDualProb gamma gamma'
              (BeffaraDC.selfDualPoint q) q rho)
    _ ≤ ∑ rho : source,
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q (D rho) := by
      exact Finset.sum_le_sum fun rho _ => hprob rho
    _ = ∑ eta : range,
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q eta.1 := by
      exact Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = ∑ eta ∈ Finset.univ.filter (fun eta => eta ∈ range),
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q eta :=
      (Finset.sum_subtype
        (Finset.univ.filter (fun eta => eta ∈ range))
          (by
            intro eta
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            change eta ∈ Set.range D ↔ eta ∈ Set.range D
            rfl) (fun eta =>
          FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (BeffaraDC.selfDualPoint q) q eta)).symm
    _ ≤ ∑ eta ∈ Finset.univ.filter (fun eta => eta ∈ A),
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q eta := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro eta heta
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at heta ⊢
        exact hrange heta
      · intro eta _ _
        exact FK.bcProb_nonneg (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma') hp hp1 hq0 eta
    _ = ∑ eta : {eta : ConfigSpace (Sym2 (RlcConnectorVertex n)) // eta ∈ A},
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q eta.1 :=
      Finset.sum_subtype
        (Finset.univ.filter (fun eta => eta ∈ A))
          (by intro eta; simp only [Finset.mem_filter, Finset.mem_univ,
            true_and]) (fun eta =>
          FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (BeffaraDC.selfDualPoint q) q eta)
    _ = ∑ eta : ConfigSpace (Sym2 (RlcConnectorVertex n)),
        A.indicator (fun _ => (1 : Real)) eta *
          FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (BeffaraDC.selfDualPoint q) q eta := by
      rw [← Finset.sum_subtype
        (Finset.univ.filter (fun eta => eta ∈ A))
          (by intro eta; simp only [Finset.mem_filter, Finset.mem_univ,
            true_and]) (fun eta =>
          FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (BeffaraDC.selfDualPoint q) q eta), Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro eta _
      by_cases heta : eta ∈ A <;> simp [heta]




theorem
    rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_injection
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q distortion : Real} (hq : 1 ≤ q) (hdistortion : 0 ≤ distortion)
    (D : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} →
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hinj : Function.Injective D)
    (hsuccess : ∀ rho,
      D rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hprob : ∀ rho,
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q rho.1 ≤
        distortion *
          FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (BeffaraDC.selfDualPoint q) q (D rho)) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ ≤
      distortion *
        FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  classical
  let A := rlc_finiteTwoChannelConnectorEvent gamma gamma'
  let source := {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) // rho ∉ A}
  let targetWeight := fun eta : ConfigSpace (Sym2 (RlcConnectorVertex n)) =>
    A.indicator (fun eta =>
      FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q eta) eta
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  have hsum := Fintype.sum_le_mul_sum_of_injective
    D hinj
    (fun rho : source =>
      rlc_twoChannelForcedDualProb gamma gamma'
        (BeffaraDC.selfDualPoint q) q rho.1)
    targetWeight distortion hdistortion
    (fun eta => by
      by_cases heta : eta ∈ A
      · simp only [targetWeight, Set.indicator_of_mem heta]
        exact FK.bcProb_nonneg
          (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma') hp hp1 hq0 eta
      · simp [targetWeight, heta])
    (fun rho => by
      have htargetD : targetWeight (D rho) =
          FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (BeffaraDC.selfDualPoint q) q (D rho) := by
        have hDA : D rho ∈ A := hsuccess rho
        simp [targetWeight, hDA]
      rw [htargetD]
      exact hprob rho)
  unfold rlc_twoChannelForcedDualEventMass FK.bcEventMass
  calc
    (∑ rho : ConfigSpace (Sym2 (RlcConnectorVertex n)),
        Aᶜ.indicator (fun _ => (1 : Real)) rho *
          rlc_twoChannelForcedDualProb gamma gamma'
            (BeffaraDC.selfDualPoint q) q rho) =
        ∑ rho : source,
          rlc_twoChannelForcedDualProb gamma gamma'
            (BeffaraDC.selfDualPoint q) q rho.1 := by
      calc
        _ = ∑ rho ∈ Finset.univ.filter (fun rho => rho ∉ A),
            rlc_twoChannelForcedDualProb gamma gamma'
              (BeffaraDC.selfDualPoint q) q rho := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro rho _
          by_cases hrho : rho ∈ A <;> simp [hrho]
        _ = _ := Finset.sum_subtype
          (Finset.univ.filter (fun rho => rho ∉ A))
            (by
              intro rho
              simp only [Finset.mem_filter, Finset.mem_univ, true_and])
            (fun rho => rlc_twoChannelForcedDualProb gamma gamma'
              (BeffaraDC.selfDualPoint q) q rho)
    _ ≤ distortion * ∑ eta, targetWeight eta := hsum
    _ = distortion *
        ∑ eta : ConfigSpace (Sym2 (RlcConnectorVertex n)),
          A.indicator (fun _ => (1 : Real)) eta *
            FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
              (rlc_connectorMergedWiring gamma gamma')
              (BeffaraDC.selfDualPoint q) q eta := by
      congr 1
      apply Finset.sum_congr rfl
      intro eta _
      by_cases heta : eta ∈ A <;> simp [targetWeight, heta]



def RlcTwoChannelPIMSFailurePushforwardComparison {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) : Prop :=
  rlc_twoChannelPIMSFailureImageMass gamma gamma' p q ≤
    FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
      (rlc_connectorMergedWiring gamma gamma') p q
      (rlc_finiteTwoChannelConnectorEvent gamma gamma')




def RlcTwoChannelForcedDualFailurePushforwardComparison {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (q : Real) : Prop :=
  rlc_twoChannelForcedDualFailureImageMass gamma gamma'
      (BeffaraDC.selfDualPoint q) q ≤
    FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
      (rlc_connectorMergedWiring gamma gamma')
      (BeffaraDC.selfDualPoint q) q
      (rlc_finiteTwoChannelConnectorEvent gamma gamma')



theorem rlc_twoChannelForcedDualFailurePushforwardComparison_of_equiv
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 ≤ q)
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (D : ConfigSpace (Sym2 (RlcConnectorVertex n)) ≃
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hfailure : ∀ rho,
      rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma' →
        D rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hprob : ∀ rho,
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q rho ≤
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q (D rho)) :
    RlcTwoChannelForcedDualFailurePushforwardComparison
      gamma gamma' q := by
  unfold RlcTwoChannelForcedDualFailurePushforwardComparison
  rw [rlc_twoChannelForcedDualFailureImageMass_eq_compl
    gamma gamma' _ _ hclosure]
  exact rlc_twoChannelForcedDualEventMass_compl_le_merged_of_equiv
    gamma gamma' hq D hfailure hprob



theorem rlc_twoChannelForcedDualFailurePushforwardComparison_of_injection
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 ≤ q)
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (D : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} →
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hinj : Function.Injective D)
    (hsuccess : ∀ rho,
      D rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hprob : ∀ rho,
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q rho.1 ≤
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q (D rho)) :
    RlcTwoChannelForcedDualFailurePushforwardComparison
      gamma gamma' q := by
  unfold RlcTwoChannelForcedDualFailurePushforwardComparison
  rw [rlc_twoChannelForcedDualFailureImageMass_eq_compl
    gamma gamma' _ _ hclosure]
  exact rlc_twoChannelForcedDualEventMass_compl_le_merged_of_injection
    gamma gamma' hq D hinj hsuccess hprob




theorem
    rlc_twoChannelForcedDualFailurePushforwardComparison_q_one_of_injection
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (D : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} →
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hinj : Function.Injective D)
    (hsuccess : ∀ rho,
      D rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    RlcTwoChannelForcedDualFailurePushforwardComparison
      gamma gamma' 1 := by
  apply rlc_twoChannelForcedDualFailurePushforwardComparison_of_injection
    gamma gamma' le_rfl hclosure D hinj hsuccess
  intro rho
  rw [show BeffaraDC.selfDualPoint 1 = (1 / 2 : Real) by
    norm_num [BeffaraDC.selfDualPoint]]
  exact (rlc_twoChannelForcedDualProb_half_q_one_eq_merged
    gamma gamma' rho.1 (D rho)).le



noncomputable def rlc_twoChannelFailureLowestRetainedBoundary
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
      rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'}) :
    RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho.1 :=
  Classical.choice
    (rlc_centralFace_lowestRetainedAnchoredBoundary_of_failure
      gamma gamma' hfaith.toRlcBookPositionedTracePair rho.1 (fun hcentral =>
        rho.2 (rlc_finiteCentralFaceRandomConnectorEvent_subset_twoChannel
          gamma gamma' hcentral)))



def RlcTwoChannelFailureRetainedAnchorTraceIncidence
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
      rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'}) : Prop :=
  RlcCentralFaceRetainedAnchorTraceIncidence
    (rlc_twoChannelFailureLowestRetainedBoundary
      gamma gamma' hfaith rho).boundary



theorem rlc_twoChannelForcedDualEventMass_compl_le_merged_of_partitioned_injections
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (R : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
      rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} -> Prop)
    (Dgood : {rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} // R rho} ->
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (Dbad : {rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} // ¬ R rho} ->
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hgoodInj : Function.Injective Dgood)
    (hbadInj : Function.Injective Dbad)
    (hrange : Disjoint (Set.range Dgood) (Set.range Dbad))
    (hgoodSuccess : forall rho,
      Dgood rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hbadSuccess : forall rho,
      Dbad rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hgoodProb : forall rho,
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q rho.1.1 <=
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q (Dgood rho))
    (hbadProb : forall rho,
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q rho.1.1 <=
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q (Dbad rho)) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  classical
  let source := {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
    rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'}
  let D : source -> ConfigSpace (Sym2 (RlcConnectorVertex n)) := fun rho =>
    if h : R rho then Dgood ⟨rho, h⟩ else Dbad ⟨rho, h⟩
  have hDinj : Function.Injective D := by
    intro rho eta hD
    by_cases hrho : R rho
    · by_cases heta : R eta
      · simp only [D, dif_pos hrho, dif_pos heta] at hD
        have hsub := hgoodInj hD
        exact Subtype.ext (congrArg (fun z => z.1.1) hsub)
      · simp only [D, dif_pos hrho, dif_neg heta] at hD
        exfalso
        exact Set.disjoint_left.mp hrange
          ⟨⟨rho, hrho⟩, rfl⟩ ⟨⟨eta, heta⟩, hD.symm⟩
    · by_cases heta : R eta
      · simp only [D, dif_neg hrho, dif_pos heta] at hD
        exfalso
        exact Set.disjoint_left.mp hrange
          ⟨⟨eta, heta⟩, rfl⟩ ⟨⟨rho, hrho⟩, hD⟩
      · simp only [D, dif_neg hrho, dif_neg heta] at hD
        have hsub := hbadInj hD
        exact Subtype.ext (congrArg (fun z => z.1.1) hsub)
  apply rlc_twoChannelForcedDualEventMass_compl_le_merged_of_injection
    gamma gamma' hq D hDinj
  · intro rho
    by_cases hrho : R rho
    · simpa only [D, dif_pos hrho] using hgoodSuccess ⟨rho, hrho⟩
    · simpa only [D, dif_neg hrho] using hbadSuccess ⟨rho, hrho⟩
  · intro rho
    by_cases hrho : R rho
    · simpa only [D, dif_pos hrho] using hgoodProb ⟨rho, hrho⟩
    · simpa only [D, dif_neg hrho] using hbadProb ⟨rho, hrho⟩



theorem rlc_twoChannelForcedDualFailurePushforwardComparison_of_anchoredIncidenceInjections
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {q : Real} (hq : 1 <= q)
    (Dincidence : {rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} //
          RlcTwoChannelFailureRetainedAnchorTraceIncidence
            gamma gamma' hfaith rho} ->
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (Dmissing : {rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} //
          ¬ RlcTwoChannelFailureRetainedAnchorTraceIncidence
            gamma gamma' hfaith rho} ->
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hincidenceInj : Function.Injective Dincidence)
    (hmissingInj : Function.Injective Dmissing)
    (hrange : Disjoint (Set.range Dincidence) (Set.range Dmissing))
    (hincidenceSuccess : forall rho,
      Dincidence rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hmissingSuccess : forall rho,
      Dmissing rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hincidenceProb : forall rho,
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q rho.1.1 <=
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q (Dincidence rho))
    (hmissingProb : forall rho,
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q rho.1.1 <=
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q (Dmissing rho)) :
    RlcTwoChannelForcedDualFailurePushforwardComparison gamma gamma' q := by
  classical
  unfold RlcTwoChannelForcedDualFailurePushforwardComparison
  calc
    rlc_twoChannelForcedDualFailureImageMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q <=
      rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ := by
      unfold rlc_twoChannelForcedDualFailureImageMass
        rlc_twoChannelForcedDualEventMass
      apply Finset.sum_le_sum
      intro rho _
      have hq0 : 0 < q := zero_lt_one.trans_le hq
      obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
      by_cases hsource :
          rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma'
      · simp [hsource]
      · have hcomp : rho ∈
            (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ := by
          simpa using hsource
        simp only [Set.indicator_of_mem hcomp, one_mul]
        by_cases hpims : rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
            rlc_finiteTwoChannelConnectorEvent gamma gamma'
        · simp [hpims]
        · simp only [Set.indicator_of_notMem hpims, zero_mul]
          exact rlc_twoChannelForcedDualProb_nonneg
            gamma gamma' hp hp1 hq0 rho
    _ <= FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
      apply rlc_twoChannelForcedDualEventMass_compl_le_merged_of_partitioned_injections
        gamma gamma' hq
        (RlcTwoChannelFailureRetainedAnchorTraceIncidence
          gamma gamma' hfaith)
        Dincidence Dmissing hincidenceInj hmissingInj hrange
        hincidenceSuccess hmissingSuccess hincidenceProb hmissingProb



theorem rlc_twoChannelForcedDualFailurePushforwardComparison_q_one_of_anchoredIncidenceInjections
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (Dincidence : {rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} //
          RlcTwoChannelFailureRetainedAnchorTraceIncidence
            gamma gamma' hfaith rho} ->
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (Dmissing : {rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} //
          ¬ RlcTwoChannelFailureRetainedAnchorTraceIncidence
            gamma gamma' hfaith rho} ->
      ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hincidenceInj : Function.Injective Dincidence)
    (hmissingInj : Function.Injective Dmissing)
    (hrange : Disjoint (Set.range Dincidence) (Set.range Dmissing))
    (hincidenceSuccess : forall rho,
      Dincidence rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma')
    (hmissingSuccess : forall rho,
      Dmissing rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    RlcTwoChannelForcedDualFailurePushforwardComparison gamma gamma' 1 := by
  apply rlc_twoChannelForcedDualFailurePushforwardComparison_of_anchoredIncidenceInjections
    gamma gamma' hfaith le_rfl Dincidence Dmissing hincidenceInj hmissingInj
      hrange hincidenceSuccess hmissingSuccess
  · intro rho
    rw [show BeffaraDC.selfDualPoint 1 = (1 / 2 : Real) by
      norm_num [BeffaraDC.selfDualPoint]]
    exact (rlc_twoChannelForcedDualProb_half_q_one_eq_merged
      gamma gamma' rho.1.1 (Dincidence rho)).le
  · intro rho
    rw [show BeffaraDC.selfDualPoint 1 = (1 / 2 : Real) by
      norm_num [BeffaraDC.selfDualPoint]]
    exact (rlc_twoChannelForcedDualProb_half_q_one_eq_merged
      gamma gamma' rho.1.1 (Dmissing rho)).le




theorem rlc_twoChannelConnector_glues_horizontal (n : Int) (_hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_pathOpen gamma.1 ∩ rlc_pathOpen gamma'.1 ∩
        (rlc_connectorRestrictConfig ⁻¹'
          rlc_finiteTwoChannelConnectorEvent gamma gamma') ⊆
      horizontalCrossingEvent (-2 * n) (2 * n) (-n) n := by
  intro omega homega
  obtain ⟨⟨hgamma, hgamma'⟩, x, y, hx, hy, hxy⟩ := homega
  obtain ⟨_hxSmall, hxToRightSmall⟩ :=
    rlc_pathOpen_connected_finish gamma.1 omega hgamma hx
  obtain ⟨_hySmall, hleftToYSmall⟩ :=
    rlc_pathOpen_connected_start gamma'.1 omega hgamma' hy
  have hrightSub : rect 0 (2 * n) (-n) n ⊆
      rect (-2 * n) (2 * n) (-n) n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  have hleftSub : rect (-2 * n) 0 (-n) n ⊆
      rect (-2 * n) (2 * n) (-n) n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  have hxToRight := StatMech.RSW.Strip.connectedWithin_mono_set omega
    hrightSub hxToRightSmall
  have hleftToY := StatMech.RSW.Strip.connectedWithin_mono_set omega
    hleftSub hleftToYSmall
  let hom : FK.openSub (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorRestrictConfig omega) →g
      openSubgraphInduce 2 omega
        (rect (-2 * n) (2 * n) (-n) n) := {
    toFun z := ⟨z.1, z.2⟩
    map_rel' := by
      intro a b hab
      rw [FK.openSub_adj] at hab
      rcases hab with ⟨habGraph, habOpen⟩
      have habLat : (hypercubicLattice 2).Adj a.1 b.1 := by
        rcases habGraph.1 with habCentral | habReflected
        · exact habCentral.1
        · exact habReflected.1
      exact ⟨habLat, by simpa [rlc_connectorRestrictConfig,
        Sym2.map_mk] using habOpen⟩
  }
  have hxyAmbient : ConnectedWithin 2 omega
      (rect (-2 * n) (2 * n) (-n) n) ⟨x.1, x.2⟩ ⟨y.1, y.2⟩ :=
    hxy.map hom
  let xL : leftSide (-2 * n) (2 * n) (-n) n :=
    ⟨gamma'.1.1, by
      rw [mem_leftSide, mem_rect]
      have h := gamma'.1.1.2
      rw [mem_leftSide, mem_rect] at h
      exact ⟨⟨by omega, by omega, h.1.2.2.1, h.1.2.2.2⟩, h.2⟩⟩
  let yR : rightSide (-2 * n) (2 * n) (-n) n :=
    ⟨gamma.1.2.1, by
      rw [mem_rightSide, mem_rect]
      have h := gamma.1.2.1.2
      rw [mem_rightSide, mem_rect] at h
      exact ⟨⟨by omega, by omega, h.1.2.2.1, h.1.2.2.2⟩, h.2⟩⟩
  refine ⟨xL, yR, ?_⟩
  exact hleftToY.trans (hxyAmbient.symm.trans hxToRight)




def RlcTwoChannelFailureMassComparison {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) : Prop :=
  FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
      (rlc_connectorSeparateWiring gamma gamma') p q
      (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ ≤
    FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
      (rlc_connectorMergedWiring gamma gamma') p q
      (rlc_finiteTwoChannelConnectorEvent gamma gamma')



theorem rlc_twoChannelFailureMassComparison_of_PIMS {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (hfailure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (hpush : RlcTwoChannelPIMSFailurePushforwardComparison
      gamma gamma' p q) :
    RlcTwoChannelFailureMassComparison gamma gamma' p q := by
  unfold RlcTwoChannelFailureMassComparison
  unfold RlcTwoChannelPIMSFailurePushforwardComparison at hpush
  rw [rlc_twoChannel_failureMass_eq_PIMSFailureImageMass
    gamma gamma' p q hfailure]
  exact hpush



theorem rlc_finiteTwoChannelConnectorMass_ge_one_div_one_add_q {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hdual : RlcTwoChannelFailureMassComparison gamma gamma' p q) :
    1 / (1 + q) ≤
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  apply FrontierD.bcEventMass_ge_one_div_one_add_q_of_compl_le_sup_edge
    (rlc_connectorTwoChannelGraph gamma gamma')
    (rlc_connectorSeparateWiring gamma gamma')
    (rlc_connectorRightAnchor gamma) (rlc_connectorLeftAnchor gamma')
    hp hp1 hq (rlc_finiteTwoChannelConnectorEvent gamma gamma')
  simpa only [rlc_connectorMergedWiring] using hdual



theorem rlc_finiteTwoChannelConnectorMass_ge_one_div_one_add_mul {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q distortion : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (hdistortion : 0 <= distortion)
    (hdual :
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') p q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
        distortion *
          FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma') p q
            (rlc_finiteTwoChannelConnectorEvent gamma gamma')) :
    1 / (1 + distortion * q) <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') p q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  apply
    FrontierD.bcEventMass_ge_one_div_one_add_mul_of_compl_le_mul_sup_edge
      (rlc_connectorTwoChannelGraph gamma gamma')
      (rlc_connectorSeparateWiring gamma gamma')
      (rlc_connectorRightAnchor gamma) (rlc_connectorLeftAnchor gamma')
      hp hp1 hq hdistortion
      (rlc_finiteTwoChannelConnectorEvent gamma gamma')
  simpa only [rlc_connectorMergedWiring] using hdual




theorem
    rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_distorted_forcedDual
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q distortion : Real} (hq : 1 <= q) (hdistortion : 0 <= distortion)
    (hfailure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (hpush :
      rlc_twoChannelForcedDualEventMass gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
        distortion *
          FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (BeffaraDC.selfDualPoint q) q
            (rlc_finiteTwoChannelConnectorEvent gamma gamma')) :
    1 / (1 + distortion * q) <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  apply rlc_finiteTwoChannelConnectorMass_ge_one_div_one_add_mul
    gamma gamma' hp hp1 hq hdistortion
  calc
    FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ =
      rlc_twoChannelPIMSFailureImageMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q :=
      rlc_twoChannel_failureMass_eq_PIMSFailureImageMass
        gamma gamma' _ _ hfailure
    _ = rlc_twoChannelForcedDualFailureImageMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q :=
      rlc_twoChannelPIMSFailureImageMass_eq_forcedDual
        gamma gamma' hq0
    _ = rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ :=
      rlc_twoChannelForcedDualFailureImageMass_eq_compl
        gamma gamma' _ _ hfailure
    _ <= distortion *
        FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma') := hpush




theorem rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_PIMS {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 ≤ q)
    (hfailure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (hpush : RlcTwoChannelForcedDualFailurePushforwardComparison
      gamma gamma' q) :
    1 / (1 + q) ≤
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨hp, hp1⟩ := BeffaraDC.selfDualPoint_mem_Ioo hq0
  apply rlc_finiteTwoChannelConnectorMass_ge_one_div_one_add_q
    gamma gamma' hp hp1 hq
  unfold RlcTwoChannelFailureMassComparison
  calc
    FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ =
      rlc_twoChannelPIMSFailureImageMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q :=
      rlc_twoChannel_failureMass_eq_PIMSFailureImageMass
        gamma gamma' _ _ hfailure
    _ = rlc_twoChannelForcedDualFailureImageMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q :=
      rlc_twoChannelPIMSFailureImageMass_eq_forcedDual
        gamma gamma' hq0
    _ ≤ FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := hpush

end

end StatMech.Universality
