/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWConnectorTwoChannel











open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

abbrev RlcTwoChannelEdgeConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  ConfigSpace (rlc_connectorTwoChannelGraph gamma gamma').edgeSet

abbrev RlcTwoChannelOffGraphConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  ConfigSpace {e : Sym2 (RlcConnectorVertex n) //
    e ∉ (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}



noncomputable def rlc_twoChannelConfigSplitEquiv {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) ≃
      RlcTwoChannelEdgeConfig gamma gamma' ×
        RlcTwoChannelOffGraphConfig gamma gamma' where
  toFun rho :=
    (fun e => rho e.1, fun e => rho e.1)
  invFun pair e := if he : e ∈
      (rlc_connectorTwoChannelGraph gamma gamma').edgeSet then
    pair.1 ⟨e, he⟩
  else
    pair.2 ⟨e, he⟩
  left_inv rho := by
    funext e
    by_cases he : e ∈
        (rlc_connectorTwoChannelGraph gamma gamma').edgeSet <;>
      simp [he]
  right_inv pair := by
    apply Prod.ext
    · funext e
      simp [e.2]
    · funext e
      simp [e.2]


noncomputable def rlc_twoChannelEdgeConfigExtend {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  (rlc_twoChannelConfigSplitEquiv gamma gamma').symm
    (omega, fun _ => false)


noncomputable def rlc_twoChannelEdgeConfigCombine {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (outside : RlcTwoChannelOffGraphConfig gamma gamma') :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  (rlc_twoChannelConfigSplitEquiv gamma gamma').symm (omega, outside)

@[simp] theorem rlc_twoChannelEdgeConfigCombine_edge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (outside : RlcTwoChannelOffGraphConfig gamma gamma')
    (e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet) :
    rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside e.1 =
      omega e := by
  simp [rlc_twoChannelEdgeConfigCombine, rlc_twoChannelConfigSplitEquiv,
    e.2]

theorem rlc_openSub_twoChannel_edgeConfigCombine {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (outside : RlcTwoChannelOffGraphConfig gamma gamma') :
    FK.openSub (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside) =
      FK.openSub (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) := by
  ext x y
  rw [FK.openSub_adj, FK.openSub_adj]
  constructor
  · rintro ⟨hxy, hopen⟩
    refine ⟨hxy, ?_⟩
    have he : s(x, y) ∈
        (rlc_connectorTwoChannelGraph gamma gamma').edgeSet := by
      rw [SimpleGraph.mem_edgeSet]
      exact hxy
    simpa [rlc_twoChannelEdgeConfigCombine,
      rlc_twoChannelEdgeConfigExtend, rlc_twoChannelConfigSplitEquiv, he]
      using hopen
  · rintro ⟨hxy, hopen⟩
    refine ⟨hxy, ?_⟩
    have he : s(x, y) ∈
        (rlc_connectorTwoChannelGraph gamma gamma').edgeSet := by
      rw [SimpleGraph.mem_edgeSet]
      exact hxy
    simpa [rlc_twoChannelEdgeConfigCombine,
      rlc_twoChannelEdgeConfigExtend, rlc_twoChannelConfigSplitEquiv, he]
      using hopen

theorem rlc_twoChannel_edgeConfigCombine_mem_event_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (outside : RlcTwoChannelOffGraphConfig gamma gamma') :
    rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside ∈
        rlc_finiteTwoChannelConnectorEvent gamma gamma' ↔
      rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∈
        rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
  change (∃ x y, rlc_connectorOnRight gamma x ∧
      rlc_connectorOnLeft gamma' y ∧
        (FK.openSub (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside)).Reachable x y) ↔
    ∃ x y, rlc_connectorOnRight gamma x ∧
      rlc_connectorOnLeft gamma' y ∧
        (FK.openSub (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)).Reachable x y
  rw [rlc_openSub_twoChannel_edgeConfigCombine]



theorem rlc_twoChannel_split_fst_mem_event_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_twoChannelEdgeConfigExtend gamma gamma'
          ((rlc_twoChannelConfigSplitEquiv gamma gamma' rho).1) ∈
        rlc_finiteTwoChannelConnectorEvent gamma gamma' ↔
      rho ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
  let split := rlc_twoChannelConfigSplitEquiv gamma gamma'
  have hrho : rlc_twoChannelEdgeConfigCombine gamma gamma'
      (split rho).1 (split rho).2 = rho := split.symm_apply_apply rho
  constructor
  · intro hedge
    have hcombine := (rlc_twoChannel_edgeConfigCombine_mem_event_iff
      gamma gamma' (split rho).1 (split rho).2).mpr hedge
    simpa only [hrho] using hcombine
  · intro hfull
    apply (rlc_twoChannel_edgeConfigCombine_mem_event_iff
      gamma gamma' (split rho).1 (split rho).2).mp
    simpa only [hrho] using hfull



noncomputable def rlc_twoChannelLiftEdgeFailureEmbedding {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (J : {omega : RlcTwoChannelEdgeConfig gamma gamma' //
          rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
            rlc_finiteTwoChannelConnectorEvent gamma gamma'} ↪
        {eta : RlcTwoChannelEdgeConfig gamma gamma' //
          rlc_twoChannelEdgeConfigExtend gamma gamma' eta ∈
            rlc_finiteTwoChannelConnectorEvent gamma gamma'}) :
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
        rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'} ↪
      ConfigSpace (Sym2 (RlcConnectorVertex n)) where
  toFun rho :=
    let split := rlc_twoChannelConfigSplitEquiv gamma gamma'
    let edgeFailure : {omega : RlcTwoChannelEdgeConfig gamma gamma' //
        rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
          rlc_finiteTwoChannelConnectorEvent gamma gamma'} :=
      ⟨(split rho.1).1, fun hedge =>
        rho.2 ((rlc_twoChannel_split_fst_mem_event_iff
          gamma gamma' rho.1).mp hedge)⟩
    rlc_twoChannelEdgeConfigCombine gamma gamma'
      (J edgeFailure).1 (split rho.1).2
  inj' := by
    intro rho sigma hrs
    let split := rlc_twoChannelConfigSplitEquiv gamma gamma'
    let rhoEdge : {omega : RlcTwoChannelEdgeConfig gamma gamma' //
        rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
          rlc_finiteTwoChannelConnectorEvent gamma gamma'} :=
      ⟨(split rho.1).1, fun hedge =>
        rho.2 ((rlc_twoChannel_split_fst_mem_event_iff
          gamma gamma' rho.1).mp hedge)⟩
    let sigmaEdge : {omega : RlcTwoChannelEdgeConfig gamma gamma' //
        rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
          rlc_finiteTwoChannelConnectorEvent gamma gamma'} :=
      ⟨(split sigma.1).1, fun hedge =>
        sigma.2 ((rlc_twoChannel_split_fst_mem_event_iff
          gamma gamma' sigma.1).mp hedge)⟩
    change rlc_twoChannelEdgeConfigCombine gamma gamma' (J rhoEdge).1
        (split rho.1).2 =
      rlc_twoChannelEdgeConfigCombine gamma gamma' (J sigmaEdge).1
        (split sigma.1).2 at hrs
    have hsplit := congrArg split hrs
    dsimp only [split] at hsplit
    simp only [rlc_twoChannelEdgeConfigCombine,
      Equiv.apply_symm_apply] at hsplit
    rw [Prod.mk.injEq] at hsplit
    have hedge : rhoEdge = sigmaEdge := J.injective (Subtype.ext hsplit.1)
    apply Subtype.ext
    apply split.injective
    exact Prod.ext (congrArg Subtype.val hedge) hsplit.2

theorem rlc_twoChannelLiftEdgeFailureEmbedding_success {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (J : {omega : RlcTwoChannelEdgeConfig gamma gamma' //
          rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
            rlc_finiteTwoChannelConnectorEvent gamma gamma'} ↪
        {eta : RlcTwoChannelEdgeConfig gamma gamma' //
          rlc_twoChannelEdgeConfigExtend gamma gamma' eta ∈
            rlc_finiteTwoChannelConnectorEvent gamma gamma'})
    (rho : {rho : ConfigSpace (Sym2 (RlcConnectorVertex n)) //
      rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma'}) :
    rlc_twoChannelLiftEdgeFailureEmbedding gamma gamma' J rho ∈
      rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
  let split := rlc_twoChannelConfigSplitEquiv gamma gamma'
  let edgeFailure : {omega : RlcTwoChannelEdgeConfig gamma gamma' //
      rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
        rlc_finiteTwoChannelConnectorEvent gamma gamma'} :=
    ⟨(split rho.1).1, fun hedge =>
      rho.2 ((rlc_twoChannel_split_fst_mem_event_iff
        gamma gamma' rho.1).mp hedge)⟩
  exact (rlc_twoChannel_edgeConfigCombine_mem_event_iff
    gamma gamma' (J edgeFailure).1 (split rho.1).2).mpr
      (J edgeFailure).2

theorem rlc_twoChannelForcedDualProb_edgeConfigCombine {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (outside : RlcTwoChannelOffGraphConfig gamma gamma') :
    rlc_twoChannelForcedDualProb gamma gamma' p q
        (rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside) =
      rlc_twoChannelForcedDualProb gamma gamma' p q
        (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) := by
  unfold rlc_twoChannelForcedDualProb
  dsimp only
  congr 1
  rw [rlc_openSub_twoChannelAugmented_forceTrace,
    rlc_openSub_twoChannelAugmented_forceTrace,
    rlc_openSub_twoChannel_edgeConfigCombine]

theorem rlc_twoChannel_bcWeight_edgeConfigCombine {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (C : SimpleGraph (RlcConnectorVertex n)) [DecidableRel C.Adj]
    (p q : Real) (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (outside : RlcTwoChannelOffGraphConfig gamma gamma') :
    FK.bcWeight (rlc_connectorTwoChannelGraph gamma gamma') C p q
        (rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside) =
      FK.bcWeight (rlc_connectorTwoChannelGraph gamma gamma') C p q
        (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) := by
  unfold FK.bcWeight
  have hclusters : FK.numClustersBC
      (rlc_connectorTwoChannelGraph gamma gamma') C
        (rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside) =
      FK.numClustersBC (rlc_connectorTwoChannelGraph gamma gamma') C
        (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) := by
    unfold FK.numClustersBC
    rw [rlc_openSub_twoChannel_edgeConfigCombine]
  have hproduct : FK.edgeProduct
      (rlc_connectorTwoChannelGraph gamma gamma') p
        (rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside) =
      FK.edgeProduct (rlc_connectorTwoChannelGraph gamma gamma') p
        (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) := by
    unfold FK.edgeProduct
    apply Finset.prod_congr rfl
    intro e he
    have heset : e ∈
        (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
      SimpleGraph.mem_edgeFinset.mp he
    simp [rlc_twoChannelEdgeConfigCombine,
      rlc_twoChannelEdgeConfigExtend, rlc_twoChannelConfigSplitEquiv, heset]
  rw [hclusters, hproduct]

theorem rlc_twoChannel_bcProb_edgeConfigCombine {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (C : SimpleGraph (RlcConnectorVertex n)) [DecidableRel C.Adj]
    (p q : Real) (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (outside : RlcTwoChannelOffGraphConfig gamma gamma') :
    FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma') C p q
        (rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside) =
      FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma') C p q
        (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) := by
  unfold FK.bcProb
  rw [rlc_twoChannel_bcWeight_edgeConfigCombine]




theorem rlc_twoChannelForcedDualEventMass_compl_le_merged_of_edgeEmbedding
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q : Real} (hq : 1 <= q)
    (J : {omega : RlcTwoChannelEdgeConfig gamma gamma' //
          rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
            rlc_finiteTwoChannelConnectorEvent gamma gamma'} ↪
        {eta : RlcTwoChannelEdgeConfig gamma gamma' //
          rlc_twoChannelEdgeConfigExtend gamma gamma' eta ∈
            rlc_finiteTwoChannelConnectorEvent gamma gamma'})
    (hprob : forall omega,
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega.1) <=
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_twoChannelEdgeConfigExtend gamma gamma' (J omega).1)) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  let D := rlc_twoChannelLiftEdgeFailureEmbedding gamma gamma' J
  apply rlc_twoChannelForcedDualEventMass_compl_le_merged_of_injection
    gamma gamma' hq D D.injective
      (rlc_twoChannelLiftEdgeFailureEmbedding_success gamma gamma' J)
  intro rho
  let split := rlc_twoChannelConfigSplitEquiv gamma gamma'
  let edgeFailure : {omega : RlcTwoChannelEdgeConfig gamma gamma' //
      rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
        rlc_finiteTwoChannelConnectorEvent gamma gamma'} :=
    ⟨(split rho.1).1, fun hedge =>
      rho.2 ((rlc_twoChannel_split_fst_mem_event_iff
        gamma gamma' rho.1).mp hedge)⟩
  calc
    rlc_twoChannelForcedDualProb gamma gamma'
        (BeffaraDC.selfDualPoint q) q rho.1 =
      rlc_twoChannelForcedDualProb gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_twoChannelEdgeConfigExtend gamma gamma' edgeFailure.1) := by
      have hrho : rlc_twoChannelEdgeConfigCombine gamma gamma'
          edgeFailure.1 (split rho.1).2 = rho.1 :=
        split.symm_apply_apply rho.1
      rw [← hrho, rlc_twoChannelForcedDualProb_edgeConfigCombine]
    _ <= FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q
        (rlc_twoChannelEdgeConfigExtend gamma gamma' (J edgeFailure).1) :=
      hprob edgeFailure
    _ = FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q (D rho) := by
      exact (rlc_twoChannel_bcProb_edgeConfigCombine gamma gamma'
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q (J edgeFailure).1
        (split rho.1).2).symm




theorem
    rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_edgeEmbedding
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {q distortion : Real} (hq : 1 <= q) (hdistortion : 0 <= distortion)
    (J : {omega : RlcTwoChannelEdgeConfig gamma gamma' //
          rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
            rlc_finiteTwoChannelConnectorEvent gamma gamma'} ↪
        {eta : RlcTwoChannelEdgeConfig gamma gamma' //
          rlc_twoChannelEdgeConfigExtend gamma gamma' eta ∈
            rlc_finiteTwoChannelConnectorEvent gamma gamma'})
    (hprob : forall omega,
      rlc_twoChannelForcedDualProb gamma gamma'
          (BeffaraDC.selfDualPoint q) q
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega.1) <=
        distortion *
          FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
            (rlc_connectorMergedWiring gamma gamma')
            (BeffaraDC.selfDualPoint q) q
            (rlc_twoChannelEdgeConfigExtend gamma gamma' (J omega).1)) :
    rlc_twoChannelForcedDualEventMass gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      distortion *
        FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  let D := rlc_twoChannelLiftEdgeFailureEmbedding gamma gamma' J
  apply
    rlc_twoChannelForcedDualEventMass_compl_le_mul_merged_of_injection
      gamma gamma' hq hdistortion D D.injective
        (rlc_twoChannelLiftEdgeFailureEmbedding_success gamma gamma' J)
  intro rho
  let split := rlc_twoChannelConfigSplitEquiv gamma gamma'
  let edgeFailure : {omega : RlcTwoChannelEdgeConfig gamma gamma' //
      rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
        rlc_finiteTwoChannelConnectorEvent gamma gamma'} :=
    ⟨(split rho.1).1, fun hedge =>
      rho.2 ((rlc_twoChannel_split_fst_mem_event_iff
        gamma gamma' rho.1).mp hedge)⟩
  calc
    rlc_twoChannelForcedDualProb gamma gamma'
        (BeffaraDC.selfDualPoint q) q rho.1 =
      rlc_twoChannelForcedDualProb gamma gamma'
        (BeffaraDC.selfDualPoint q) q
        (rlc_twoChannelEdgeConfigExtend gamma gamma' edgeFailure.1) := by
      have hrho : rlc_twoChannelEdgeConfigCombine gamma gamma'
          edgeFailure.1 (split rho.1).2 = rho.1 :=
        split.symm_apply_apply rho.1
      rw [← hrho, rlc_twoChannelForcedDualProb_edgeConfigCombine]
    _ <= distortion *
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q
          (rlc_twoChannelEdgeConfigExtend gamma gamma'
            (J edgeFailure).1) := hprob edgeFailure
    _ = distortion *
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorMergedWiring gamma gamma')
          (BeffaraDC.selfDualPoint q) q (D rho) := by
      congr 1
      exact (rlc_twoChannel_bcProb_edgeConfigCombine gamma gamma'
        (rlc_connectorMergedWiring gamma gamma')
        (BeffaraDC.selfDualPoint q) q (J edgeFailure).1
        (split rho.1).2).symm



theorem rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_edgeEmbedding
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (J : {omega : RlcTwoChannelEdgeConfig gamma gamma' //
          rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
            rlc_finiteTwoChannelConnectorEvent gamma gamma'} ↪
        {eta : RlcTwoChannelEdgeConfig gamma gamma' //
          rlc_twoChannelEdgeConfigExtend gamma gamma' eta ∈
            rlc_finiteTwoChannelConnectorEvent gamma gamma'}) :
    rlc_twoChannelForcedDualEventMass gamma gamma' (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  rw [show (1 / 2 : Real) = BeffaraDC.selfDualPoint 1 by
    norm_num [BeffaraDC.selfDualPoint]]
  apply rlc_twoChannelForcedDualEventMass_compl_le_merged_of_edgeEmbedding
    gamma gamma' le_rfl J
  intro omega
  rw [show BeffaraDC.selfDualPoint 1 = (1 / 2 : Real) by
    norm_num [BeffaraDC.selfDualPoint]]
  exact (rlc_twoChannelForcedDualProb_half_q_one_eq_merged
    gamma gamma'
    (rlc_twoChannelEdgeConfigExtend gamma gamma' omega.1)
    (rlc_twoChannelEdgeConfigExtend gamma gamma' (J omega).1)).le



theorem rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_edgeCapacity
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hcard : Fintype.card
        {omega : RlcTwoChannelEdgeConfig gamma gamma' //
          rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
            rlc_finiteTwoChannelConnectorEvent gamma gamma'} <=
      Fintype.card
        {eta : RlcTwoChannelEdgeConfig gamma gamma' //
          rlc_twoChannelEdgeConfigExtend gamma gamma' eta ∈
            rlc_finiteTwoChannelConnectorEvent gamma gamma'}) :
    rlc_twoChannelForcedDualEventMass gamma gamma' (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <=
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  obtain ⟨J⟩ := Function.Embedding.nonempty_iff_card_le.mpr hcard
  exact
    rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_edgeEmbedding
      gamma gamma' J

end

end StatMech.Universality
