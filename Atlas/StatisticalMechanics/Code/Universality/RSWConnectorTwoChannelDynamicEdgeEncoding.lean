/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWConnectorTwoChannelEdgeEncoding
import Code.FK.SelfDualPointMassScore
import Code.FK.BoundaryScoreLipschitz
import Code.FrontierD.FKBoundarySingleMerge











open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

abbrev RlcTwoChannelEdgeFailure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  {omega : RlcTwoChannelEdgeConfig gamma gamma' //
    rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma'}

abbrev RlcTwoChannelEdgeSuccess {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  {eta : RlcTwoChannelEdgeConfig gamma gamma' //
    rlc_twoChannelEdgeConfigExtend gamma gamma' eta ∈
      rlc_finiteTwoChannelConnectorEvent gamma gamma'}




structure RlcTwoChannelDynamicRoutePlan {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) where
  Route : Type
  reservedEdges : Route →
    Finset (rlc_connectorTwoChannelGraph gamma gamma').edgeSet
  payloadSlots : Route →
    Finset (rlc_connectorTwoChannelGraph gamma gamma').edgeSet
  reservedEdges_disjoint_payloadSlots : ∀ route,
    Disjoint (reservedEdges route) (payloadSlots route)
  tagState : Route → RlcTwoChannelEdgeConfig gamma gamma'
  success_of_reserved : ∀ route eta,
    (∀ e, e ∈ reservedEdges route → eta e = true) →
      rlc_twoChannelEdgeConfigExtend gamma gamma' eta ∈
        rlc_finiteTwoChannelConnectorEvent gamma gamma'

def RlcTwoChannelDynamicRoutePlan.codeSet {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (P : RlcTwoChannelDynamicRoutePlan gamma gamma')
    (route : P.Route) : Set (RlcTwoChannelEdgeConfig gamma gamma') :=
  {eta | (∀ e, e ∈ P.reservedEdges route → eta e = true) ∧
    ∀ e, e ∉ P.reservedEdges route → e ∉ P.payloadSlots route →
      eta e = P.tagState route e}

abbrev RlcTwoChannelDynamicRoutePlan.Code {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (P : RlcTwoChannelDynamicRoutePlan gamma gamma')
    (route : P.Route) :=
  {eta : RlcTwoChannelEdgeConfig gamma gamma' // eta ∈ P.codeSet route}

abbrev RlcTwoChannelDynamicRoutePlan.Payload {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (P : RlcTwoChannelDynamicRoutePlan gamma gamma')
    (route : P.Route) :=
  ConfigSpace {e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet //
    e ∈ P.payloadSlots route}




noncomputable def RlcTwoChannelDynamicRoutePlan.codeEquivPayload {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (P : RlcTwoChannelDynamicRoutePlan gamma gamma')
    (route : P.Route) : P.Code route ≃ P.Payload route where
  toFun eta e := eta.1 e.1
  invFun bits :=
    ⟨fun e =>
      if hreserved : e ∈ P.reservedEdges route then true
      else if hslot : e ∈ P.payloadSlots route then bits ⟨e, hslot⟩
      else P.tagState route e,
    by
      constructor
      · intro e he
        simp [he]
      · intro e hreserved hslot
        simp [hreserved, hslot]⟩
  left_inv eta := by
    apply Subtype.ext
    funext e
    by_cases hreserved : e ∈ P.reservedEdges route
    · simp [hreserved, eta.2.1 e hreserved]
    · by_cases hslot : e ∈ P.payloadSlots route
      · simp [hreserved, hslot]
      · simp [hreserved, hslot, eta.2.2 e hreserved hslot]
  right_inv bits := by
    funext e
    have hreserved : e.1 ∉ P.reservedEdges route := by
      intro he
      exact Finset.disjoint_left.mp
        (P.reservedEdges_disjoint_payloadSlots route) he e.2
    simp [hreserved, e.2]


theorem RlcTwoChannelDynamicRoutePlan.code_card {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (P : RlcTwoChannelDynamicRoutePlan gamma gamma')
    (route : P.Route) :
    Fintype.card (P.Code route) = 2 ^ (P.payloadSlots route).card := by
  rw [Fintype.card_congr (P.codeEquivPayload route), Fintype.card_fun,
    Fintype.card_bool, Fintype.card_coe]



noncomputable def RlcTwoChannelEdgeCodeHall {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (Compatible : RlcTwoChannelEdgeFailure gamma gamma' →
      RlcTwoChannelEdgeSuccess gamma gamma' → Prop) : Prop := by
  classical
  exact ∀ failures : Finset (RlcTwoChannelEdgeFailure gamma gamma'),
      failures.card <=
        (Finset.univ.filter fun eta : RlcTwoChannelEdgeSuccess gamma gamma' =>
          ∃ rho ∈ failures, Compatible rho eta).card



theorem rlc_twoChannelEdgeCodeHall_iff_exists_compatibleEmbedding {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (Compatible : RlcTwoChannelEdgeFailure gamma gamma' →
      RlcTwoChannelEdgeSuccess gamma gamma' → Prop) :
    RlcTwoChannelEdgeCodeHall gamma gamma' Compatible ↔
      ∃ J : RlcTwoChannelEdgeFailure gamma gamma' ↪
          RlcTwoChannelEdgeSuccess gamma gamma',
        ∀ rho, Compatible rho (J rho) := by
  classical
  have hhall := Fintype.all_card_le_filter_rel_iff_exists_injective Compatible
  constructor
  · intro h
    have h' : ∀ failures :
        Finset (RlcTwoChannelEdgeFailure gamma gamma'),
        failures.card <=
          (Finset.univ.filter fun eta :
            RlcTwoChannelEdgeSuccess gamma gamma' =>
              ∃ rho ∈ failures, Compatible rho eta).card := by
      simpa only [RlcTwoChannelEdgeCodeHall] using h
    obtain ⟨J, hJ, hcompatible⟩ := hhall.mp h'
    exact ⟨⟨J, hJ⟩, hcompatible⟩
  · rintro ⟨J, hcompatible⟩
    simpa only [RlcTwoChannelEdgeCodeHall] using
      (hhall.mpr ⟨J, J.injective, hcompatible⟩)


theorem rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_edgeCodeHall
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (Compatible : RlcTwoChannelEdgeFailure gamma gamma' →
      RlcTwoChannelEdgeSuccess gamma gamma' → Prop)
    (hHall : RlcTwoChannelEdgeCodeHall gamma gamma' Compatible) :
    rlc_twoChannelForcedDualEventMass gamma gamma' (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  obtain ⟨J, _hcompatible⟩ :=
    (rlc_twoChannelEdgeCodeHall_iff_exists_compatibleEmbedding
      gamma gamma' Compatible).mp hHall
  exact
    rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_edgeEmbedding
      gamma gamma' J



theorem rlc_twoChannelForcedDualEventMass_compl_le_merged_of_edgeCodeHall
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (Compatible : RlcTwoChannelEdgeFailure gamma gamma' →
      RlcTwoChannelEdgeSuccess gamma gamma' → Prop)
    (hHall : RlcTwoChannelEdgeCodeHall gamma gamma' Compatible)
    (hdom : ∀ rho eta, Compatible rho eta →
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <=
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1)) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  obtain ⟨J, hcompatible⟩ :=
    (rlc_twoChannelEdgeCodeHall_iff_exists_compatibleEmbedding
      gamma gamma' Compatible).mp hHall
  apply rlc_twoChannelForcedDualEventMass_compl_le_merged_of_edgeEmbedding
    gamma gamma' hq J
  intro rho
  exact hdom rho (J rho) (hcompatible rho)




theorem
    rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_edgeCodeHall
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q distortion : Real} (hq : 1 <= q) (hdistortion : 0 <= distortion)
    (Compatible : RlcTwoChannelEdgeFailure gamma gamma' ->
      RlcTwoChannelEdgeSuccess gamma gamma' -> Prop)
    (hHall : RlcTwoChannelEdgeCodeHall gamma gamma' Compatible)
    (hdom : forall rho eta, Compatible rho eta ->
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <=
        distortion *
          FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (BeffaraDC.selfDualPoint q) q
            (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1)) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      distortion *
        FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  obtain ⟨J, hcompatible⟩ :=
    (rlc_twoChannelEdgeCodeHall_iff_exists_compatibleEmbedding
      gamma gamma' Compatible).mp hHall
  apply
    rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_edgeEmbedding
      gamma gamma' hq hdistortion J
  intro rho
  exact hdom rho (J rho) (hcompatible rho)






theorem
    rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_edgeCodeHall_score
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q) (N : Nat)
    (Compatible : RlcTwoChannelEdgeFailure gamma gamma' ->
      RlcTwoChannelEdgeSuccess gamma gamma' -> Prop)
    (hHall : RlcTwoChannelEdgeCodeHall gamma gamma' Compatible)
    (hscore : forall rho eta, Compatible rho eta ->
      FK.openCount (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) +
          2 * FK.numClustersBC
            (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorSeparateWiring gamma gamma')
            (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <=
        FK.openCount (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) +
          2 * FK.numClustersBC
            (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) + N) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      (Real.sqrt q) ^ N *
        FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  apply
    rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_edgeCodeHall
      gamma gamma' hq (pow_nonneg (Real.sqrt_nonneg q) N) Compatible hHall
  intro rho eta hcompatible
  rw [← rlc_twoChannel_bcProb_separate_selfDual_eq_forcedDualProb
    gamma gamma' _ (zero_lt_one.trans_le hq)]
  exact FK.bcProb_selfDualPoint_le_sqrt_pow_of_score_le
    (rlc_connectorTwoChannelGraph gamma gamma')
    (rlc_connectorSeparateWiring gamma gamma')
    (rlc_connectorMergedWiring gamma gamma')
    le_sup_left hq N _ _ (hscore rho eta hcompatible)




theorem rlc_twoChannel_score_le_hamming_add_two
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega eta : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openCount (rlc_connectorTwoChannelGraph gamma gamma') omega +
        2 * FK.numClustersBC
          (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') omega <=
      FK.openCount (rlc_connectorTwoChannelGraph gamma gamma') eta +
        2 * FK.numClustersBC
          (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma') eta +
        FK.configHammingCount (rlc_connectorTwoChannelGraph gamma gamma')
          omega eta + 2 := by
  apply FK.bcScore_le_add_configHammingCount_add_boundaryGap
    (rlc_connectorTwoChannelGraph gamma gamma')
    (rlc_connectorSeparateWiring gamma gamma')
    (rlc_connectorMergedWiring gamma gamma') 1 omega eta
  simpa only [rlc_connectorMergedWiring, Nat.add_comm] using
    StatMech.FrontierD.numClustersBC_le_sup_edge_add_one
      (rlc_connectorTwoChannelGraph gamma gamma')
      (rlc_connectorSeparateWiring gamma gamma')
      (rlc_connectorRightAnchor gamma) (rlc_connectorLeftAnchor gamma') eta



theorem
    rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_edgeCodeHall_hamming
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q) (K : Nat)
    (Compatible : RlcTwoChannelEdgeFailure gamma gamma' ->
      RlcTwoChannelEdgeSuccess gamma gamma' -> Prop)
    (hHall : RlcTwoChannelEdgeCodeHall gamma gamma' Compatible)
    (hHamming : forall rho eta, Compatible rho eta ->
      FK.configHammingCount (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1)
        (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) <= K) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      (Real.sqrt q) ^ (K + 2) *
        FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  apply
    rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_edgeCodeHall_score
      gamma gamma' hq (K + 2) Compatible hHall
  intro rho eta hcompatible
  have hScore := rlc_twoChannel_score_le_hamming_add_two gamma gamma'
    (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1)
    (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1)
  have hDistance := hHamming rho eta hcompatible
  omega


theorem
    rlc_twoChannelForcedDualEventMass_compl_le_qpow_merged_of_edgeCodeHall_score
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q) (N : Nat)
    (Compatible : RlcTwoChannelEdgeFailure gamma gamma' ->
      RlcTwoChannelEdgeSuccess gamma gamma' -> Prop)
    (hHall : RlcTwoChannelEdgeCodeHall gamma gamma' Compatible)
    (hscore : forall rho eta, Compatible rho eta ->
      FK.openCount (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) +
          2 * FK.numClustersBC
            (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorSeparateWiring gamma gamma')
            (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <=
        FK.openCount (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) +
          2 * FK.numClustersBC
            (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) + N) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      q ^ N *
        FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  apply
    rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_edgeCodeHall
      gamma gamma' hq (pow_nonneg (by linarith) N) Compatible hHall
  intro rho eta hcompatible
  rw [← rlc_twoChannel_bcProb_separate_selfDual_eq_forcedDualProb
    gamma gamma' _ (zero_lt_one.trans_le hq)]
  exact FK.bcProb_selfDualPoint_le_qpow_of_score_le
    (rlc_connectorTwoChannelGraph gamma gamma')
    (rlc_connectorSeparateWiring gamma gamma')
    (rlc_connectorMergedWiring gamma gamma')
    le_sup_left hq N _ _ (hscore rho eta hcompatible)



def RlcTwoChannelDynamicRoutePlan.Compatible {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (P : RlcTwoChannelDynamicRoutePlan gamma gamma')
    (routeAvailable : RlcTwoChannelEdgeFailure gamma gamma' → P.Route → Prop)
    (rho : RlcTwoChannelEdgeFailure gamma gamma')
    (eta : RlcTwoChannelEdgeSuccess gamma gamma') : Prop :=
  ∃ route : P.Route, routeAvailable rho route ∧ eta.1 ∈ P.codeSet route

def RlcTwoChannelDynamicRoutePlan.HasCodeHall {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (P : RlcTwoChannelDynamicRoutePlan gamma gamma')
    (routeAvailable : RlcTwoChannelEdgeFailure gamma gamma' → P.Route → Prop) :
    Prop :=
  RlcTwoChannelEdgeCodeHall gamma gamma'
    (P.Compatible routeAvailable)


theorem
    rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_dynamicRouteHall
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (P : RlcTwoChannelDynamicRoutePlan gamma gamma')
    (routeAvailable : RlcTwoChannelEdgeFailure gamma gamma' → P.Route → Prop)
    (hHall : P.HasCodeHall routeAvailable) :
    rlc_twoChannelForcedDualEventMass gamma gamma' (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  exact rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_edgeCodeHall
    gamma gamma' (P.Compatible routeAvailable) hHall


theorem rlc_twoChannelForcedDualEventMass_compl_le_merged_of_dynamicRouteHall
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (P : RlcTwoChannelDynamicRoutePlan gamma gamma')
    (routeAvailable : RlcTwoChannelEdgeFailure gamma gamma' → P.Route → Prop)
    (hHall : P.HasCodeHall routeAvailable)
    (hdom : ∀ rho eta, P.Compatible routeAvailable rho eta →
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <=
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1)) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  exact rlc_twoChannelForcedDualEventMass_compl_le_merged_of_edgeCodeHall
    gamma gamma' hq (P.Compatible routeAvailable) hHall hdom



theorem
    rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_dynamicRouteHall
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q distortion : Real} (hq : 1 <= q) (hdistortion : 0 <= distortion)
    (P : RlcTwoChannelDynamicRoutePlan gamma gamma')
    (routeAvailable : RlcTwoChannelEdgeFailure gamma gamma' -> P.Route -> Prop)
    (hHall : P.HasCodeHall routeAvailable)
    (hdom : forall rho eta, P.Compatible routeAvailable rho eta ->
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <=
        distortion *
          FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (BeffaraDC.selfDualPoint q) q
            (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1)) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      distortion *
        FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  exact
    rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_edgeCodeHall
      gamma gamma' hq hdistortion (P.Compatible routeAvailable) hHall hdom



theorem
    rlc_twoChannelForcedDualEventMass_compl_le_qpow_merged_of_dynamicRouteHall_score
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q) (N : Nat)
    (P : RlcTwoChannelDynamicRoutePlan gamma gamma')
    (routeAvailable : RlcTwoChannelEdgeFailure gamma gamma' -> P.Route -> Prop)
    (hHall : P.HasCodeHall routeAvailable)
    (hscore : forall rho eta, P.Compatible routeAvailable rho eta ->
      FK.openCount (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) +
          2 * FK.numClustersBC
            (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorSeparateWiring gamma gamma')
            (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <=
        FK.openCount (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) +
          2 * FK.numClustersBC
            (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) + N) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      q ^ N *
        FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  exact
    rlc_twoChannelForcedDualEventMass_compl_le_qpow_merged_of_edgeCodeHall_score
      gamma gamma' hq N (P.Compatible routeAvailable) hHall hscore


theorem
    rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_dynamicRouteHall_score
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q) (N : Nat)
    (P : RlcTwoChannelDynamicRoutePlan gamma gamma')
    (routeAvailable : RlcTwoChannelEdgeFailure gamma gamma' -> P.Route -> Prop)
    (hHall : P.HasCodeHall routeAvailable)
    (hscore : forall rho eta, P.Compatible routeAvailable rho eta ->
      FK.openCount (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) +
          2 * FK.numClustersBC
            (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorSeparateWiring gamma gamma')
            (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) <=
        FK.openCount (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) +
          2 * FK.numClustersBC
            (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) + N) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      (Real.sqrt q) ^ N *
        FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  exact
    rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_edgeCodeHall_score
      gamma gamma' hq N (P.Compatible routeAvailable) hHall hscore


theorem
    rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_dynamicRouteHall_hamming
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q) (K : Nat)
    (P : RlcTwoChannelDynamicRoutePlan gamma gamma')
    (routeAvailable : RlcTwoChannelEdgeFailure gamma gamma' -> P.Route -> Prop)
    (hHall : P.HasCodeHall routeAvailable)
    (hHamming : forall rho eta, P.Compatible routeAvailable rho eta ->
      FK.configHammingCount (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1)
        (rlc_twoChannelEdgeConfigExtend gamma gamma' eta.1) <= K) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      (Real.sqrt q) ^ (K + 2) *
        FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  exact
    rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_edgeCodeHall_hamming
      gamma gamma' hq K (P.Compatible routeAvailable) hHall hHamming

end

end StatMech.Universality
