/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.FiniteActiveDuality
import Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation










open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section



theorem rlc_twoChannelEdgeConfigExtend_eq_extendActive
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelEdgeConfigExtend gamma gamma' omega =
      FK.extendActive (rlc_connectorTwoChannelGraph gamma gamma') omega := by
  funext e
  by_cases he : e ∈
      (rlc_connectorTwoChannelGraph gamma gamma').edgeSet
  · simp [rlc_twoChannelEdgeConfigExtend, rlc_twoChannelConfigSplitEquiv,
      FK.extendActive, he]
  · simp [rlc_twoChannelEdgeConfigExtend, rlc_twoChannelConfigSplitEquiv,
      FK.extendActive, he]



theorem rlc_twoChannelFullPhysicalPermConfig_activeOpenCount
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    FK.activeOpenCount (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega) =
      Fintype.card
          (rlc_connectorTwoChannelGraph gamma gamma').edgeSet -
        FK.activeOpenCount (rlc_connectorTwoChannelGraph gamma gamma')
          omega := by
  change FK.activeOpenCount (rlc_connectorTwoChannelGraph gamma gamma')
      (FK.activeDualConfig
        (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_twoChannelFullPhysicalEdgePerm gamma gamma').symm omega) = _
  exact FK.activeOpenCount_dualConfig
    (rlc_connectorTwoChannelGraph gamma gamma')
    (rlc_connectorTwoChannelGraph gamma gamma')
    (rlc_twoChannelFullPhysicalEdgePerm gamma gamma').symm omega


theorem rlc_twoChannelFullPhysicalPermConfig_openCount
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    FK.openCount (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_twoChannelEdgeConfigExtend gamma gamma'
          (rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega)) =
      (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset.card -
        FK.openCount (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) := by
  rw [rlc_twoChannelEdgeConfigExtend_eq_extendActive,
    rlc_twoChannelEdgeConfigExtend_eq_extendActive,
    FK.openCount_extendActive_eq_activeOpenCount,
    FK.openCount_extendActive_eq_activeOpenCount,
    rlc_twoChannelFullPhysicalPermConfig_activeOpenCount,
    SimpleGraph.edgeFinset_card]




theorem rlc_twoChannelForced_clusterEuler {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'
    let K := FK.openSub P.G
      (rlc_connectorForceTraceConfig gamma gamma' rho)
    Nat.card P.V +
        Nat.card (BeffaraDC.pfdClosedDual P K).ConnectedComponent =
      K.edgeSet.ncard +
        FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') rho + 1 := by
  dsimp only
  let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'
  let K := FK.openSub P.G
    (rlc_connectorForceTraceConfig gamma gamma' rho)
  have heuler := BeffaraDC.pfd_clusterEuler P K
    (FK.openSub_le P.G (rlc_connectorForceTraceConfig gamma gamma' rho))
  have hk : Nat.card K.ConnectedComponent =
      FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorSeparateWiring gamma gamma') rho := by
    calc
      Nat.card K.ConnectedComponent = Fintype.card K.ConnectedComponent :=
        Nat.card_eq_fintype_card
      _ = FK.numClusters P.G
          (rlc_connectorForceTraceConfig gamma gamma' rho) := rfl
      _ = FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorTraceWiring gamma gamma') rho :=
        rlc_twoChannel_numClusters_augmented_forceTrace_eq_traceBC
          gamma gamma' rho
      _ = FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') rho :=
        rlc_twoChannel_numClustersBC_traceWiring_eq_separateWiring
          gamma gamma' rho
  simpa only [P, K, hk] using heuler



theorem rlc_twoChannelForced_openCount {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openCount
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma' rho) =
      FK.openCount (rlc_connectorTwoChannelGraph gamma gamma') rho +
        (rlc_connectorTraceWiring gamma gamma').edgeFinset.card := by
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
  have hEdges :
      (rlc_connectorTwoChannelAugmentedPlanarDomain
        gamma gamma').G.edgeFinset = G.edgeFinset ∪ T.edgeFinset := by
    simp [rlc_connectorTwoChannelAugmentedPlanarDomain, G, T]
  unfold FK.openCount
  rw [hEdges]
  change ((G.edgeFinset ∪ T.edgeFinset).filter (fun e =>
      rlc_connectorForceTraceConfig gamma gamma' rho e = true)).card =
    (G.edgeFinset.filter (fun e => rho e = true)).card +
      T.edgeFinset.card
  rw [Finset.filter_union,
    Finset.card_union_of_disjoint
      (hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
  congr 1
  · apply congrArg Finset.card
    apply Finset.filter_congr
    intro e heG
    have hnot : e ∉ T.edgeFinset := Finset.disjoint_left.mp hd heG
    simp [rlc_connectorForceTraceConfig, T, hnot]
  · have hfilter :
        T.edgeFinset.filter (fun e =>
          rlc_connectorForceTraceConfig gamma gamma' rho e = true) =
          T.edgeFinset := by
      apply Finset.filter_eq_self.mpr
      intro e heT
      simp [rlc_connectorForceTraceConfig, T, heT]
    rw [hfilter]



theorem rlc_twoChannelForced_clusterEuler_openCount {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'
    let K := FK.openSub P.G
      (rlc_connectorForceTraceConfig gamma gamma' rho)
    Nat.card P.V +
        Nat.card (BeffaraDC.pfdClosedDual P K).ConnectedComponent =
      FK.openCount (rlc_connectorTwoChannelGraph gamma gamma') rho +
        (rlc_connectorTraceWiring gamma gamma').edgeFinset.card +
        FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') rho + 1 := by
  dsimp only
  rw [rlc_twoChannelForced_clusterEuler,
    BeffaraDC.pfd_openSub_edge_ncard,
    rlc_twoChannelForced_openCount]



def RlcTwoChannelFullPhysicalEulerScoreBound {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (N : Nat) : Prop :=
  ∀ rho : RlcTwoChannelEdgeFailure gamma gamma',
    2 * FK.openCount (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) +
        2 * FK.numClustersBC
          (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma')
          (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) ≤
      (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset.card +
        2 * FK.numClustersBC
          (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (rlc_twoChannelEdgeConfigExtend gamma gamma'
            (rlc_twoChannelFullPhysicalPermConfig gamma gamma' rho.1)) + N




theorem rlc_twoChannelFullPhysicalPermutationScoreDefect_iff_eulerScoreBound
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) (N : Nat) :
    RlcTwoChannelFullPhysicalPermutationScoreDefect gamma gamma' N ↔
      RlcTwoChannelFullPhysicalEulerScoreBound gamma gamma' N := by
  constructor <;> intro h rho
  · have hopen : FK.openCount
        (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) ≤
          (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset.card := by
      unfold FK.openCount
      exact Finset.card_filter_le _ _
    have hscore := h rho
    rw [rlc_twoChannelFullPhysicalPermConfig_openCount] at hscore
    omega
  · have hopen : FK.openCount
        (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) ≤
          (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset.card := by
      unfold FK.openCount
      exact Finset.card_filter_le _ _
    have heuler := h rho
    rw [rlc_twoChannelFullPhysicalPermConfig_openCount]
    omega

end

end StatMech.Universality
