/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding











open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section





theorem rlc_connectorCentralFacePIMSConfig_congr_of_centralEdges {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {rho sigma : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (hcentral : ∀ (e : Sym2 (Site 2))
      (he : e ∈ rlc_connectorCentralFaceEdges gamma gamma'),
      rho (rlc_connectorCentralFaceEdgeLift e he) =
        sigma (rlc_connectorCentralFaceEdgeLift e he)) :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho =
      rlc_connectorCentralFacePIMSConfig gamma gamma' sigma := by
  funext target
  rw [rlc_connectorCentralFacePIMSConfig_apply,
    rlc_connectorCentralFacePIMSConfig_apply]
  unfold rlc_connectorCentralFaceAmbientConfig
  split
  · rename_i he
    rw [hcentral _ he]
  · rfl



def RlcTwoChannelPIMSCoversCentralEdges {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) : Prop :=
  ∀ source : (rlc_connectorCentralFaceFiniteGraph gamma gamma').edgeSet,
    ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
      rlc_pimsEdgeEquiv (target.1.map Subtype.val) =
        source.1.map Subtype.val



abbrev RlcTwoChannelDiscardedEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  {e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet //
    e.1 ∉ (rlc_connectorCentralFaceFiniteGraph gamma gamma').edgeSet}

private theorem rlc_centralFaceGraph_edge_site_mem {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (e : (rlc_connectorCentralFaceFiniteGraph gamma gamma').edgeSet) :
    e.1.map Subtype.val ∈
      rlc_connectorCentralFaceEdges gamma gamma' := by
  induction heq : e.1 using Sym2.inductionOn with
  | _ x y =>
      have he := e.2
      rw [heq, SimpleGraph.mem_edgeSet] at he
      simpa [heq, Sym2.map_mk] using he.2

private theorem rlc_centralFaceEdgeLift_graphEdge {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (e : (rlc_connectorCentralFaceFiniteGraph gamma gamma').edgeSet) :
    rlc_connectorCentralFaceEdgeLift (e.1.map Subtype.val)
        (rlc_centralFaceGraph_edge_site_mem e) = e.1 := by
  apply Sym2.map.injective Subtype.val_injective
  rw [rlc_connectorCentralFaceEdgeLift_map]



theorem rlc_twoChannel_centralBits_eq_of_PIMS_eq {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hcover : RlcTwoChannelPIMSCoversCentralEdges gamma gamma')
    {rho sigma : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (hpims : rlc_connectorCentralFacePIMSConfig gamma gamma' rho =
      rlc_connectorCentralFacePIMSConfig gamma gamma' sigma)
    (source : (rlc_connectorCentralFaceFiniteGraph gamma gamma').edgeSet) :
    rho source.1 = sigma source.1 := by
  obtain ⟨target, htarget⟩ := hcover source
  have happ := congrFun hpims target.1
  have hsourceMem := rlc_centralFaceGraph_edge_site_mem source
  rw [rlc_connectorCentralFacePIMSConfig_apply,
    rlc_connectorCentralFacePIMSConfig_apply, htarget,
    rlc_connectorCentralFaceAmbientConfig_support
      gamma gamma' rho hsourceMem,
    rlc_connectorCentralFaceAmbientConfig_support
      gamma gamma' sigma hsourceMem,
    rlc_centralFaceEdgeLift_graphEdge] at happ
  have hdouble := congrArg (fun b : Bool => !b) happ
  simpa using hdouble




theorem rlc_twoChannel_PIMS_and_discardedBits_injective {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hcover : RlcTwoChannelPIMSCoversCentralEdges gamma gamma') :
    Function.Injective (fun omega : RlcTwoChannelEdgeConfig gamma gamma' =>
      (rlc_connectorCentralFacePIMSConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega),
        fun e : RlcTwoChannelDiscardedEdge gamma gamma' => omega e.1)) := by
  intro rho sigma hpair
  have hpims := congrArg Prod.fst hpair
  have hdiscarded := congrArg Prod.snd hpair
  funext e
  by_cases hcentral : e.1 ∈
      (rlc_connectorCentralFaceFiniteGraph gamma gamma').edgeSet
  · let source :
        (rlc_connectorCentralFaceFiniteGraph gamma gamma').edgeSet :=
      ⟨e.1, hcentral⟩
    have hsource := rlc_twoChannel_centralBits_eq_of_PIMS_eq hcover hpims source
    simpa [source, rlc_twoChannelEdgeConfigExtend,
      rlc_twoChannelConfigSplitEquiv, e.2] using hsource
  · let discarded : RlcTwoChannelDiscardedEdge gamma gamma' :=
      ⟨e, hcentral⟩
    exact congrFun hdiscarded discarded






abbrev RlcTwoChannelPIMSVariableTargetEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  {e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet //
    rlc_pimsEdgeEquiv (e.1.map Subtype.val) ∈
      rlc_connectorCentralFaceEdges gamma gamma'}

private theorem rlc_twoChannelEdge_site_mem_lattice {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet) :
    e.1.map Subtype.val ∈ (hypercubicLattice 2).edgeSet := by
  induction heq : e.1 using Sym2.inductionOn with
  | _ x y =>
      have he := e.2
      rw [heq, SimpleGraph.mem_edgeSet] at he
      rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
      exact he.1.elim (fun h => h.1) (fun h => h.1)

private theorem rlc_centralFaceEdgeLift_mem_graph {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (e : Sym2 (Site 2))
    (he : e ∈ rlc_connectorCentralFaceEdges gamma gamma')
    (hlat : e ∈ (hypercubicLattice 2).edgeSet) :
    rlc_connectorCentralFaceEdgeLift e he ∈
      (rlc_connectorCentralFaceFiniteGraph gamma gamma').edgeSet := by
  let lift := rlc_connectorCentralFaceEdgeLift e he
  change lift ∈
    (rlc_connectorCentralFaceFiniteGraph gamma gamma').edgeSet
  induction hlift : lift using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet]
      have hmap := rlc_connectorCentralFaceEdgeLift_map e he
      change lift.map Subtype.val = e at hmap
      rw [hlift, Sym2.map_mk] at hmap
      have hlat' : s((x : Site 2), (y : Site 2)) ∈
          (hypercubicLattice 2).edgeSet := by simpa [hmap] using hlat
      exact ⟨(SimpleGraph.mem_edgeSet _).mp hlat', by simpa [hmap] using he⟩



noncomputable def rlc_twoChannelPIMSSourceEdge {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelPIMSVariableTargetEdge gamma gamma') :
    (rlc_connectorTwoChannelGraph gamma gamma').edgeSet := by
  let sourceSite := rlc_pimsEdgeEquiv (target.1.1.map Subtype.val)
  let sourceLift := rlc_connectorCentralFaceEdgeLift sourceSite target.2
  have hlat : sourceSite ∈ (hypercubicLattice 2).edgeSet :=
    rlc_pimsEdgeEquiv_mem_latticeEdge
      (rlc_twoChannelEdge_site_mem_lattice target.1)
  have hcentral : sourceLift ∈
      (rlc_connectorCentralFaceFiniteGraph gamma gamma').edgeSet :=
    rlc_centralFaceEdgeLift_mem_graph sourceSite target.2 hlat
  exact ⟨sourceLift, SimpleGraph.edgeSet_mono
    (rlc_connectorCentralFaceFiniteGraph_le_twoChannel gamma gamma')
      hcentral⟩

@[simp] theorem rlc_twoChannelPIMSSourceEdge_map {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelPIMSVariableTargetEdge gamma gamma') :
    (rlc_twoChannelPIMSSourceEdge target).1.map Subtype.val =
      rlc_pimsEdgeEquiv (target.1.1.map Subtype.val) := by
  exact rlc_connectorCentralFaceEdgeLift_map _ target.2

theorem rlc_twoChannelPIMSSourceEdge_injective {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n} :
    Function.Injective
      (rlc_twoChannelPIMSSourceEdge (gamma := gamma) (gamma' := gamma')) := by
  intro target target' hsource
  apply Subtype.ext
  apply Subtype.ext
  apply Sym2.map.injective Subtype.val_injective
  apply rlc_pimsEdgeEquiv.injective
  rw [← rlc_twoChannelPIMSSourceEdge_map target,
    ← rlc_twoChannelPIMSSourceEdge_map target']
  exact congrArg (fun e :
    (rlc_connectorTwoChannelGraph gamma gamma').edgeSet =>
      e.1.map Subtype.val) hsource

theorem rlc_twoChannelPIMSSourceEdge_mem_central {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelPIMSVariableTargetEdge gamma gamma') :
    (rlc_twoChannelPIMSSourceEdge target).1 ∈
      (rlc_connectorCentralFaceFiniteGraph gamma gamma').edgeSet := by
  let sourceSite := rlc_pimsEdgeEquiv (target.1.1.map Subtype.val)
  have hlat : sourceSite ∈ (hypercubicLattice 2).edgeSet :=
    rlc_pimsEdgeEquiv_mem_latticeEdge
      (rlc_twoChannelEdge_site_mem_lattice target.1)
  exact rlc_centralFaceEdgeLift_mem_graph sourceSite target.2 hlat



abbrev RlcTwoChannelPIMSDiscardedSourceEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  {e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet //
    e ∉ Set.range
      (rlc_twoChannelPIMSSourceEdge (gamma := gamma) (gamma' := gamma'))}

abbrev RlcTwoChannelPIMSFixedTargetEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  {e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet //
    rlc_pimsEdgeEquiv (e.1.map Subtype.val) ∉
      rlc_connectorCentralFaceEdges gamma gamma'}

abbrev RlcTwoChannelPIMSVisibleSourceEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  {e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet //
    e ∈ Set.range
      (rlc_twoChannelPIMSSourceEdge (gamma := gamma) (gamma' := gamma'))}



noncomputable def rlc_twoChannelPIMSVariableVisibleEquiv {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n} :
    RlcTwoChannelPIMSVariableTargetEdge gamma gamma' ≃
      RlcTwoChannelPIMSVisibleSourceEdge gamma gamma' :=
  Equiv.ofInjective rlc_twoChannelPIMSSourceEdge
    rlc_twoChannelPIMSSourceEdge_injective



noncomputable def rlc_twoChannelPIMSEdgePerm {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Equiv.Perm (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
  (rlc_twoChannelPIMSVariableVisibleEquiv
    (gamma := gamma) (gamma' := gamma')).extendSubtype

theorem rlc_twoChannelPIMSEdgePerm_variable {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (e : RlcTwoChannelPIMSVariableTargetEdge gamma gamma') :
    rlc_twoChannelPIMSEdgePerm gamma gamma' e.1 =
      rlc_twoChannelPIMSSourceEdge e := by
  rw [rlc_twoChannelPIMSEdgePerm, Equiv.extendSubtype_apply_of_mem]
  rfl


noncomputable def rlc_twoChannelFullPIMSConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    RlcTwoChannelEdgeConfig gamma gamma' :=
  fun e => !(omega (rlc_twoChannelPIMSEdgePerm gamma gamma' e))

theorem rlc_twoChannelFullPIMSConfig_injective {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n} :
    Function.Injective (rlc_twoChannelFullPIMSConfig gamma gamma') := by
  intro rho sigma hfull
  funext e
  have happ : Bool.not (rho e) = Bool.not (sigma e) := by
    simpa only [rlc_twoChannelFullPIMSConfig,
      Equiv.apply_symm_apply] using
      congrFun hfull ((rlc_twoChannelPIMSEdgePerm gamma gamma').symm e)
  have hdouble := congrArg (fun b : Bool => !b) happ
  simpa using hdouble



noncomputable def rlc_twoChannelPIMSDiscardedEquivDiscarded_of_cover
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hcover : RlcTwoChannelPIMSCoversCentralEdges gamma gamma') :
    RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma' ≃
      RlcTwoChannelDiscardedEdge gamma gamma' where
  toFun e := ⟨e.1, by
    intro hcentral
    let source :
        (rlc_connectorCentralFaceFiniteGraph gamma gamma').edgeSet :=
      ⟨e.1.1, hcentral⟩
    obtain ⟨target, htarget⟩ := hcover source
    let variableTarget : RlcTwoChannelPIMSVariableTargetEdge gamma gamma' :=
      ⟨target, by
        rw [htarget]
        exact rlc_centralFaceGraph_edge_site_mem source⟩
    apply e.2
    refine ⟨variableTarget, ?_⟩
    apply Subtype.ext
    apply Sym2.map.injective Subtype.val_injective
    rw [rlc_twoChannelPIMSSourceEdge_map, htarget]⟩
  invFun e := ⟨e.1, by
    rintro ⟨target, htarget⟩
    apply e.2
    rw [← htarget]
    exact rlc_twoChannelPIMSSourceEdge_mem_central target⟩
  left_inv e := rfl
  right_inv e := rfl

theorem rlc_twoChannelPIMSConfig_variableTarget_apply {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (target : RlcTwoChannelPIMSVariableTargetEdge gamma gamma') :
    rlc_connectorCentralFacePIMSConfig gamma gamma'
        (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) target.1.1 =
      !(omega (rlc_twoChannelPIMSSourceEdge target)) := by
  rw [rlc_connectorCentralFacePIMSConfig_apply,
    rlc_connectorCentralFaceAmbientConfig_support
      gamma gamma'
      (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) target.2]
  have hlift : rlc_connectorCentralFaceEdgeLift
      (rlc_pimsEdgeEquiv (target.1.1.map Subtype.val)) target.2 =
        (rlc_twoChannelPIMSSourceEdge target).1 := by
    rfl
  rw [hlift]
  have hedge := (rlc_twoChannelPIMSSourceEdge target).2
  simp [rlc_twoChannelEdgeConfigExtend, rlc_twoChannelConfigSplitEquiv,
    hedge]




theorem rlc_twoChannel_PIMS_and_exactDiscardedBits_injective {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n} :
    Function.Injective (fun omega : RlcTwoChannelEdgeConfig gamma gamma' =>
      (rlc_connectorCentralFacePIMSConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega),
        fun e : RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma' =>
          omega e.1)) := by
  intro rho sigma hpair
  have hpims := congrArg Prod.fst hpair
  have hdiscarded := congrArg Prod.snd hpair
  change rlc_connectorCentralFacePIMSConfig gamma gamma'
      (rlc_twoChannelEdgeConfigExtend gamma gamma' rho) =
    rlc_connectorCentralFacePIMSConfig gamma gamma'
      (rlc_twoChannelEdgeConfigExtend gamma gamma' sigma) at hpims
  change (fun e : RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma' =>
      rho e.1) =
    (fun e : RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma' =>
      sigma e.1) at hdiscarded
  funext e
  by_cases hvisible : e ∈ Set.range
      (rlc_twoChannelPIMSSourceEdge (gamma := gamma) (gamma' := gamma'))
  · obtain ⟨target, rfl⟩ := hvisible
    have happ := congrFun hpims target.1.1
    rw [rlc_twoChannelPIMSConfig_variableTarget_apply,
      rlc_twoChannelPIMSConfig_variableTarget_apply] at happ
    have hdouble := congrArg (fun b : Bool => !b) happ
    simpa using hdouble
  · let discarded : RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma' :=
      ⟨e, hvisible⟩
    exact congrFun hdiscarded discarded


noncomputable def rlc_twoChannelPIMSEdgeProjection {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    RlcTwoChannelEdgeConfig gamma gamma' :=
  (rlc_twoChannelConfigSplitEquiv gamma gamma'
    (rlc_connectorCentralFacePIMSConfig gamma gamma'
      (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))).1

@[simp] theorem rlc_twoChannelPIMSEdgeProjection_apply {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet) :
    rlc_twoChannelPIMSEdgeProjection gamma gamma' omega e =
      rlc_connectorCentralFacePIMSConfig gamma gamma'
        (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) e.1 := by
  rfl



theorem rlc_twoChannel_PIMSEdgeProjection_and_exactDiscardedBits_injective
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n} :
    Function.Injective (fun omega : RlcTwoChannelEdgeConfig gamma gamma' =>
      (rlc_twoChannelPIMSEdgeProjection gamma gamma' omega,
        fun e : RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma' =>
          omega e.1)) := by
  intro rho sigma hpair
  have hpims := congrArg Prod.fst hpair
  have hdiscarded := congrArg Prod.snd hpair
  change rlc_twoChannelPIMSEdgeProjection gamma gamma' rho =
    rlc_twoChannelPIMSEdgeProjection gamma gamma' sigma at hpims
  change (fun e : RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma' =>
      rho e.1) =
    (fun e : RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma' =>
      sigma e.1) at hdiscarded
  funext e
  by_cases hvisible : e ∈ Set.range
      (rlc_twoChannelPIMSSourceEdge (gamma := gamma) (gamma' := gamma'))
  · obtain ⟨target, rfl⟩ := hvisible
    have happ := congrFun hpims target.1
    rw [rlc_twoChannelPIMSEdgeProjection_apply,
      rlc_twoChannelPIMSEdgeProjection_apply,
      rlc_twoChannelPIMSConfig_variableTarget_apply,
      rlc_twoChannelPIMSConfig_variableTarget_apply] at happ
    have hdouble := congrArg (fun b : Bool => !b) happ
    simpa using hdouble
  · let discarded : RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma' :=
      ⟨e, hvisible⟩
    exact congrFun hdiscarded discarded


theorem rlc_twoChannelPIMSEdgeProjection_fixedTarget_eq {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (rho sigma : RlcTwoChannelEdgeConfig gamma gamma')
    (e : RlcTwoChannelPIMSFixedTargetEdge gamma gamma') :
    rlc_twoChannelPIMSEdgeProjection gamma gamma' rho e.1 =
      rlc_twoChannelPIMSEdgeProjection gamma gamma' sigma e.1 := by
  rw [rlc_twoChannelPIMSEdgeProjection_apply,
    rlc_twoChannelPIMSEdgeProjection_apply,
    rlc_connectorCentralFacePIMSConfig_apply,
    rlc_connectorCentralFacePIMSConfig_apply]
  unfold rlc_connectorCentralFaceAmbientConfig
  rw [dif_neg e.2, dif_neg e.2]



theorem rlc_twoChannelFullPIMSConfig_variable_eq_projection {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (e : RlcTwoChannelPIMSVariableTargetEdge gamma gamma') :
    rlc_twoChannelFullPIMSConfig gamma gamma' omega e.1 =
      rlc_twoChannelPIMSEdgeProjection gamma gamma' omega e.1 := by
  rw [rlc_twoChannelFullPIMSConfig,
    rlc_twoChannelPIMSEdgePerm_variable,
    rlc_twoChannelPIMSEdgeProjection_apply,
    rlc_twoChannelPIMSConfig_variableTarget_apply]

noncomputable instance rlc_twoChannelEdgeSuccessLinearOrder {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    LinearOrder (RlcTwoChannelEdgeSuccess gamma gamma') :=
  LinearOrder.lift'
    (Fintype.equivFin (RlcTwoChannelEdgeSuccess gamma gamma'))
    (Fintype.equivFin _).injective


def rlc_twoChannelOpenEdgeSet {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    Finset (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
  Finset.univ.filter fun e => omega e = true

@[simp] theorem rlc_mem_twoChannelOpenEdgeSet_iff {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet) :
    e ∈ rlc_twoChannelOpenEdgeSet omega ↔ omega e = true := by
  simp [rlc_twoChannelOpenEdgeSet]



def rlc_twoChannelSuccessfulSubconfigs {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (eta : RlcTwoChannelEdgeSuccess gamma gamma') :
    Finset (RlcTwoChannelEdgeSuccess gamma gamma') :=
  Finset.univ.filter fun route =>
    rlc_twoChannelOpenEdgeSet route.1 ⊆
      rlc_twoChannelOpenEdgeSet eta.1

theorem rlc_twoChannelSuccessfulSubconfigs_nonempty {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (eta : RlcTwoChannelEdgeSuccess gamma gamma') :
    (rlc_twoChannelSuccessfulSubconfigs eta).Nonempty := by
  refine ⟨eta, ?_⟩
  simp [rlc_twoChannelSuccessfulSubconfigs]



noncomputable def rlc_twoChannelCanonicalRoute {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (eta : RlcTwoChannelEdgeSuccess gamma gamma') :
    RlcTwoChannelEdgeSuccess gamma gamma' :=
  (rlc_twoChannelSuccessfulSubconfigs eta).min'
    (rlc_twoChannelSuccessfulSubconfigs_nonempty eta)

theorem rlc_twoChannelCanonicalRoute_mem {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (eta : RlcTwoChannelEdgeSuccess gamma gamma') :
    rlc_twoChannelCanonicalRoute eta ∈
      rlc_twoChannelSuccessfulSubconfigs eta := by
  exact Finset.min'_mem _ _

theorem rlc_twoChannelCanonicalRoute_open_subset {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (eta : RlcTwoChannelEdgeSuccess gamma gamma') :
    rlc_twoChannelOpenEdgeSet (rlc_twoChannelCanonicalRoute eta).1 ⊆
      rlc_twoChannelOpenEdgeSet eta.1 := by
  have hmem := rlc_twoChannelCanonicalRoute_mem eta
  simpa [rlc_twoChannelSuccessfulSubconfigs] using hmem



noncomputable def rlc_twoChannelCanonicalRoutePlan {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcTwoChannelDynamicRoutePlan gamma gamma' where
  Route := RlcTwoChannelEdgeSuccess gamma gamma'
  reservedEdges route := rlc_twoChannelOpenEdgeSet route.1
  payloadSlots route := Finset.univ \ rlc_twoChannelOpenEdgeSet route.1
  reservedEdges_disjoint_payloadSlots route := by
    exact Finset.disjoint_sdiff
  tagState _ := fun _ => false
  success_of_reserved route eta hopen := by
    have hle :
        rlc_twoChannelEdgeConfigExtend gamma gamma' route.1 ≤
          rlc_twoChannelEdgeConfigExtend gamma gamma' eta := by
      intro e
      by_cases hedge : e ∈
          (rlc_connectorTwoChannelGraph gamma gamma').edgeSet
      · let edge : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
          ⟨e, hedge⟩
        cases hroute : route.1 edge with
        | false =>
            simp [rlc_twoChannelEdgeConfigExtend,
              rlc_twoChannelConfigSplitEquiv, hedge, edge, hroute]
        | true =>
            have he : edge ∈ rlc_twoChannelOpenEdgeSet route.1 := by
              simpa using hroute
            have heta := hopen edge he
            simp [rlc_twoChannelEdgeConfigExtend,
              rlc_twoChannelConfigSplitEquiv, hedge, edge, hroute, heta]
      · simp [rlc_twoChannelEdgeConfigExtend,
          rlc_twoChannelConfigSplitEquiv, hedge]
    exact rlc_finiteTwoChannelConnectorEvent_isIncreasing
      gamma gamma' hle route.2


abbrev RlcTwoChannelPIMSFixedPayloadSlot {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (route : RlcTwoChannelEdgeSuccess gamma gamma') :=
  {e : RlcTwoChannelPIMSFixedTargetEdge gamma gamma' //
    e.1 ∉ rlc_twoChannelOpenEdgeSet route.1}

theorem rlc_twoChannelCanonicalRoute_target_mem_codeSet {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (eta : RlcTwoChannelEdgeSuccess gamma gamma') :
    eta.1 ∈ (rlc_twoChannelCanonicalRoutePlan gamma gamma').codeSet
      (rlc_twoChannelCanonicalRoute eta) := by
  constructor
  · intro e he
    have hsubset := rlc_twoChannelCanonicalRoute_open_subset eta
    exact (rlc_mem_twoChannelOpenEdgeSet_iff eta.1 e).mp (hsubset he)
  · intro e hreserved hpayload
    exfalso
    apply hpayload
    simp only [rlc_twoChannelCanonicalRoutePlan]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, hreserved⟩




def rlc_twoChannelCanonicalRouteAvailable {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelEdgeFailure gamma gamma' →
      RlcTwoChannelEdgeSuccess gamma gamma')
    (rho : RlcTwoChannelEdgeFailure gamma gamma')
    (route : (rlc_twoChannelCanonicalRoutePlan gamma gamma').Route) : Prop :=
  route = rlc_twoChannelCanonicalRoute (target rho)

theorem rlc_twoChannelCanonicalRoute_target_compatible {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelEdgeFailure gamma gamma' →
      RlcTwoChannelEdgeSuccess gamma gamma')
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    (rlc_twoChannelCanonicalRoutePlan gamma gamma').Compatible
      (rlc_twoChannelCanonicalRouteAvailable target) rho (target rho) := by
  refine ⟨rlc_twoChannelCanonicalRoute (target rho), rfl, ?_⟩
  exact rlc_twoChannelCanonicalRoute_target_mem_codeSet (target rho)




abbrev RlcTwoChannelTargetFibre {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelEdgeFailure gamma gamma' →
      RlcTwoChannelEdgeSuccess gamma gamma')
    (eta : RlcTwoChannelEdgeSuccess gamma gamma') :=
  {rho : RlcTwoChannelEdgeFailure gamma gamma' // target rho = eta}





structure RlcTwoChannelCanonicalFibrePacking {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelEdgeFailure gamma gamma' →
      RlcTwoChannelEdgeSuccess gamma gamma') where
  recoverBase : RlcTwoChannelEdgeSuccess gamma gamma' →
    RlcTwoChannelEdgeSuccess gamma gamma'
  pack : RlcTwoChannelEdgeFailure gamma gamma' →
    RlcTwoChannelEdgeSuccess gamma gamma'
  recoverBase_pack : ∀ rho, recoverBase (pack rho) = target rho
  pack_injective_on_fibre : ∀ rho sigma,
    target rho = target sigma → pack rho = pack sigma → rho = sigma
  pack_mem_codeSet : ∀ rho,
    (pack rho).1 ∈
      (rlc_twoChannelCanonicalRoutePlan gamma gamma').codeSet
        (rlc_twoChannelCanonicalRoute (target rho))



noncomputable def RlcTwoChannelCanonicalFibrePacking.embedding {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {target : RlcTwoChannelEdgeFailure gamma gamma' →
      RlcTwoChannelEdgeSuccess gamma gamma'}
    (packing : RlcTwoChannelCanonicalFibrePacking target) :
    RlcTwoChannelEdgeFailure gamma gamma' ↪
      RlcTwoChannelEdgeSuccess gamma gamma' where
  toFun := packing.pack
  inj' := by
    intro rho sigma hpack
    have htarget : target rho = target sigma := calc
      target rho = packing.recoverBase (packing.pack rho) :=
        (packing.recoverBase_pack rho).symm
      _ = packing.recoverBase (packing.pack sigma) :=
        congrArg packing.recoverBase hpack
      _ = target sigma := packing.recoverBase_pack sigma
    exact packing.pack_injective_on_fibre rho sigma htarget hpack

theorem RlcTwoChannelCanonicalFibrePacking.embedding_compatible {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {target : RlcTwoChannelEdgeFailure gamma gamma' →
      RlcTwoChannelEdgeSuccess gamma gamma'}
    (packing : RlcTwoChannelCanonicalFibrePacking target)
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    (rlc_twoChannelCanonicalRoutePlan gamma gamma').Compatible
      (rlc_twoChannelCanonicalRouteAvailable target) rho
        (packing.embedding rho) := by
  refine ⟨rlc_twoChannelCanonicalRoute (target rho), rfl, ?_⟩
  exact packing.pack_mem_codeSet rho


theorem RlcTwoChannelCanonicalFibrePacking.hasCodeHall {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {target : RlcTwoChannelEdgeFailure gamma gamma' →
      RlcTwoChannelEdgeSuccess gamma gamma'}
    (packing : RlcTwoChannelCanonicalFibrePacking target) :
    (rlc_twoChannelCanonicalRoutePlan gamma gamma').HasCodeHall
      (rlc_twoChannelCanonicalRouteAvailable target) := by
  apply (rlc_twoChannelEdgeCodeHall_iff_exists_compatibleEmbedding
    gamma gamma'
    ((rlc_twoChannelCanonicalRoutePlan gamma gamma').Compatible
      (rlc_twoChannelCanonicalRouteAvailable target))).mpr
  exact ⟨packing.embedding, packing.embedding_compatible⟩




theorem rlc_twoChannelCanonicalRoute_hasCodeHall_of_injective {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelEdgeFailure gamma gamma' →
      RlcTwoChannelEdgeSuccess gamma gamma')
    (htarget : Function.Injective target) :
    (rlc_twoChannelCanonicalRoutePlan gamma gamma').HasCodeHall
      (rlc_twoChannelCanonicalRouteAvailable target) := by
  apply (rlc_twoChannelEdgeCodeHall_iff_exists_compatibleEmbedding
    gamma gamma'
    ((rlc_twoChannelCanonicalRoutePlan gamma gamma').Compatible
      (rlc_twoChannelCanonicalRouteAvailable target))).mpr
  exact ⟨⟨target, htarget⟩,
    rlc_twoChannelCanonicalRoute_target_compatible target⟩






def RlcBookFaithfulRetainedAnchorIncidence {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) : Prop :=
  RlcBookFaithfulTracePair gamma gamma' ∧
    ∀ (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))),
      rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma' →
        ∃ L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho,
          RlcCentralFaceRetainedAnchorTraceIncidence L.boundary



theorem rlc_centralFaceClosureFailureCertificate_of_retainedAnchorIncidence
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma') :
    RlcCentralFaceClosureFailureCertificate gamma gamma' := by
  intro rho hno
  obtain ⟨L, hL⟩ := hinc.2 rho hno
  exact rlc_centralFacePIMS_success_of_retainedAnchorTraceIncidence
    gamma gamma' rho hL



noncomputable def rlc_twoChannelPIMSEdgeTargetOfClosure {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    RlcTwoChannelEdgeSuccess gamma gamma' := by
  let source := rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1
  let target := rlc_connectorCentralFacePIMSConfig gamma gamma' source
  let targetEdge := (rlc_twoChannelConfigSplitEquiv gamma gamma' target).1
  refine ⟨targetEdge, ?_⟩
  apply (rlc_twoChannel_split_fst_mem_event_iff gamma gamma' target).mpr
  exact rlc_twoChannelPIMS_success_of_closureFailureCertificate
    gamma gamma' hclosure source rho.2

@[simp] theorem rlc_twoChannelPIMSEdgeTargetOfClosure_val {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho).1 =
      rlc_twoChannelPIMSEdgeProjection gamma gamma' rho.1 := by
  rfl



noncomputable def rlc_twoChannelCanonicalForcedFullPIMSConfig {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    RlcTwoChannelEdgeConfig gamma gamma' :=
  fun e =>
    if e ∈ rlc_twoChannelOpenEdgeSet
        (rlc_twoChannelCanonicalRoute
          (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho)).1 then
      true
    else
      rlc_twoChannelFullPIMSConfig gamma gamma' rho.1 e

theorem rlc_twoChannelCanonicalForcedFullPIMSConfig_variable_eq {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (rho : RlcTwoChannelEdgeFailure gamma gamma')
    (e : RlcTwoChannelPIMSVariableTargetEdge gamma gamma') :
    rlc_twoChannelCanonicalForcedFullPIMSConfig hclosure rho e.1 =
      (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho).1 e.1 := by
  classical
  unfold rlc_twoChannelCanonicalForcedFullPIMSConfig
  split
  · rename_i hroute
    have hsubset := rlc_twoChannelCanonicalRoute_open_subset
      (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho)
    exact (rlc_mem_twoChannelOpenEdgeSet_iff _ _).mp (hsubset hroute) |>.symm
  · rw [rlc_twoChannelFullPIMSConfig_variable_eq_projection,
      ← rlc_twoChannelPIMSEdgeTargetOfClosure_val]

theorem rlc_twoChannelCanonicalForcedFullPIMSConfig_reserved_open {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (rho : RlcTwoChannelEdgeFailure gamma gamma') (e :
      (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (he : e ∈ rlc_twoChannelOpenEdgeSet
      (rlc_twoChannelCanonicalRoute
        (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho)).1) :
    rlc_twoChannelCanonicalForcedFullPIMSConfig hclosure rho e = true := by
  simp [rlc_twoChannelCanonicalForcedFullPIMSConfig, he]




def RlcTwoChannelPIMSFixedRouteSourceDetermined {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma') : Prop :=
  ∀ rho sigma : RlcTwoChannelEdgeFailure gamma gamma',
    rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho =
        rlc_twoChannelPIMSEdgeTargetOfClosure hclosure sigma →
      ∀ e : RlcTwoChannelPIMSFixedTargetEdge gamma gamma',
        e.1 ∈ rlc_twoChannelOpenEdgeSet
          (rlc_twoChannelCanonicalRoute
            (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho)).1 →
        rho.1 (rlc_twoChannelPIMSEdgePerm gamma gamma' e.1) =
          sigma.1 (rlc_twoChannelPIMSEdgePerm gamma gamma' e.1)




noncomputable def rlc_twoChannelPIMSTargetFibreDiscardedEmbedding {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (eta : RlcTwoChannelEdgeSuccess gamma gamma') :
    RlcTwoChannelTargetFibre
        (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure) eta ↪
      ConfigSpace (RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma') where
  toFun rho e := rho.1.1 e.1
  inj' := by
    intro rho sigma hbits
    apply Subtype.ext
    apply Subtype.ext
    apply
      rlc_twoChannel_PIMSEdgeProjection_and_exactDiscardedBits_injective
    apply Prod.ext
    · calc
        rlc_twoChannelPIMSEdgeProjection gamma gamma' rho.1.1 =
            (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho.1).1 := by
          rw [rlc_twoChannelPIMSEdgeTargetOfClosure_val]
        _ = eta.1 := congrArg Subtype.val rho.2
        _ = (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure sigma.1).1 :=
          (congrArg Subtype.val sigma.2).symm
        _ = rlc_twoChannelPIMSEdgeProjection gamma gamma' sigma.1.1 := by
          rw [rlc_twoChannelPIMSEdgeTargetOfClosure_val]
    · funext e
      exact congrFun hbits e




def RlcTwoChannelPIMSFixedPayloadCapacity {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma') : Prop :=
  ∀ eta : RlcTwoChannelEdgeSuccess gamma gamma',
    Nat.card (RlcTwoChannelTargetFibre
      (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure) eta) ≤
    Nat.card (ConfigSpace (RlcTwoChannelPIMSFixedPayloadSlot
      (rlc_twoChannelCanonicalRoute eta)))


noncomputable def rlc_twoChannelPIMSFixedPayloadEmbeddingOfCapacity {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (hcapacity : RlcTwoChannelPIMSFixedPayloadCapacity hclosure)
    (eta : RlcTwoChannelEdgeSuccess gamma gamma') :
    RlcTwoChannelTargetFibre
        (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure) eta ↪
      ConfigSpace (RlcTwoChannelPIMSFixedPayloadSlot
        (rlc_twoChannelCanonicalRoute eta)) := by
  letI := Fintype.ofFinite (RlcTwoChannelTargetFibre
    (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure) eta)
  letI := Fintype.ofFinite (ConfigSpace (RlcTwoChannelPIMSFixedPayloadSlot
    (rlc_twoChannelCanonicalRoute eta)))
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Nat.card_eq_fintype_card] using hcapacity eta


noncomputable def rlc_twoChannelPIMSFixedPayloadConfigAt {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (hcapacity : RlcTwoChannelPIMSFixedPayloadCapacity hclosure)
    (eta : RlcTwoChannelEdgeSuccess gamma gamma')
    (rho : RlcTwoChannelTargetFibre
      (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure) eta) :
    RlcTwoChannelEdgeConfig gamma gamma' :=
  let bits := rlc_twoChannelPIMSFixedPayloadEmbeddingOfCapacity
    hcapacity eta rho
  fun e =>
    if hvariable : rlc_pimsEdgeEquiv (e.1.map Subtype.val) ∈
        rlc_connectorCentralFaceEdges gamma gamma' then
      eta.1 e
    else if hroute : e ∈ rlc_twoChannelOpenEdgeSet
        (rlc_twoChannelCanonicalRoute eta).1 then
      true
    else
      bits ⟨⟨e, hvariable⟩, hroute⟩



noncomputable def rlc_twoChannelPIMSFixedPayloadConfigOfCapacity {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (hcapacity : RlcTwoChannelPIMSFixedPayloadCapacity hclosure)
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    RlcTwoChannelEdgeConfig gamma gamma' :=
  rlc_twoChannelPIMSFixedPayloadConfigAt hcapacity
    (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho) ⟨rho, rfl⟩

theorem rlc_twoChannelPIMSFixedPayloadConfigOfCapacity_eq_at {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (hcapacity : RlcTwoChannelPIMSFixedPayloadCapacity hclosure)
    (eta : RlcTwoChannelEdgeSuccess gamma gamma')
    (rho : RlcTwoChannelTargetFibre
      (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure) eta) :
    rlc_twoChannelPIMSFixedPayloadConfigOfCapacity hcapacity rho.1 =
      rlc_twoChannelPIMSFixedPayloadConfigAt hcapacity eta rho := by
  rcases rho with ⟨rho, hrho⟩
  subst eta
  rfl

theorem rlc_twoChannelPIMSFixedPayloadConfigOfCapacity_variable_eq {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (hcapacity : RlcTwoChannelPIMSFixedPayloadCapacity hclosure)
    (rho : RlcTwoChannelEdgeFailure gamma gamma')
    (e : RlcTwoChannelPIMSVariableTargetEdge gamma gamma') :
    rlc_twoChannelPIMSFixedPayloadConfigOfCapacity hcapacity rho e.1 =
      (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho).1 e.1 := by
  simp [rlc_twoChannelPIMSFixedPayloadConfigOfCapacity,
    rlc_twoChannelPIMSFixedPayloadConfigAt, e.2]

theorem rlc_twoChannelPIMSFixedPayloadConfigOfCapacity_reserved_open {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (hcapacity : RlcTwoChannelPIMSFixedPayloadCapacity hclosure)
    (rho : RlcTwoChannelEdgeFailure gamma gamma')
    (e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (he : e ∈ rlc_twoChannelOpenEdgeSet
      (rlc_twoChannelCanonicalRoute
        (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho)).1) :
    rlc_twoChannelPIMSFixedPayloadConfigOfCapacity hcapacity rho e = true := by
  unfold rlc_twoChannelPIMSFixedPayloadConfigOfCapacity
    rlc_twoChannelPIMSFixedPayloadConfigAt
  split
  · rename_i hvariable
    have hsubset := rlc_twoChannelCanonicalRoute_open_subset
      (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho)
    exact (rlc_mem_twoChannelOpenEdgeSet_iff _ _).mp (hsubset he)
  · simp




structure RlcTwoChannelPIMSDiscardedPayloadPacking {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma') where
  packConfig : RlcTwoChannelEdgeFailure gamma gamma' →
    RlcTwoChannelEdgeConfig gamma gamma'
  variable_eq : ∀ rho
    (e : RlcTwoChannelPIMSVariableTargetEdge gamma gamma'),
    packConfig rho e.1 =
      (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho).1 e.1
  reserved_open : ∀ rho e,
    e ∈ rlc_twoChannelOpenEdgeSet
        (rlc_twoChannelCanonicalRoute
          (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho)).1 →
      packConfig rho e = true
  injective_on_fibre : ∀ rho sigma,
    rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho =
        rlc_twoChannelPIMSEdgeTargetOfClosure hclosure sigma →
      packConfig rho = packConfig sigma → rho = sigma




noncomputable def
    rlc_twoChannelCanonicalForcedFullPIMSDiscardedPayloadPacking {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (hfixed : RlcTwoChannelPIMSFixedRouteSourceDetermined hclosure) :
    RlcTwoChannelPIMSDiscardedPayloadPacking hclosure where
  packConfig := rlc_twoChannelCanonicalForcedFullPIMSConfig hclosure
  variable_eq :=
    rlc_twoChannelCanonicalForcedFullPIMSConfig_variable_eq hclosure
  reserved_open :=
    rlc_twoChannelCanonicalForcedFullPIMSConfig_reserved_open hclosure
  injective_on_fibre := by
    intro rho sigma htarget hpack
    apply Subtype.ext
    apply rlc_twoChannelFullPIMSConfig_injective
    funext e
    by_cases hroute : e ∈ rlc_twoChannelOpenEdgeSet
        (rlc_twoChannelCanonicalRoute
          (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho)).1
    · by_cases hvariable : rlc_pimsEdgeEquiv (e.1.map Subtype.val) ∈
          rlc_connectorCentralFaceEdges gamma gamma'
      · let vtarget : RlcTwoChannelPIMSVariableTargetEdge gamma gamma' :=
          ⟨e, hvariable⟩
        calc
          rlc_twoChannelFullPIMSConfig gamma gamma' rho.1 e =
              (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho).1 e := by
            exact rlc_twoChannelFullPIMSConfig_variable_eq_projection
              rho.1 vtarget
          _ = (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure sigma).1 e := by
            rw [htarget]
          _ = rlc_twoChannelFullPIMSConfig gamma gamma' sigma.1 e := by
            exact (rlc_twoChannelFullPIMSConfig_variable_eq_projection
              sigma.1 vtarget).symm
      · let ftarget : RlcTwoChannelPIMSFixedTargetEdge gamma gamma' :=
          ⟨e, hvariable⟩
        exact congrArg Bool.not (hfixed rho sigma htarget ftarget hroute)
    · have hroute' : e ∉ rlc_twoChannelOpenEdgeSet
          (rlc_twoChannelCanonicalRoute
            (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure sigma)).1 := by
        rwa [← htarget]
      have happ := congrFun hpack e
      simpa only [rlc_twoChannelCanonicalForcedFullPIMSConfig,
        if_neg hroute, if_neg hroute'] using happ



noncomputable def rlc_twoChannelPIMSDiscardedPayloadPackingOfCapacity {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (hcapacity : RlcTwoChannelPIMSFixedPayloadCapacity hclosure) :
    RlcTwoChannelPIMSDiscardedPayloadPacking hclosure where
  packConfig := rlc_twoChannelPIMSFixedPayloadConfigOfCapacity hcapacity
  variable_eq :=
    rlc_twoChannelPIMSFixedPayloadConfigOfCapacity_variable_eq hcapacity
  reserved_open :=
    rlc_twoChannelPIMSFixedPayloadConfigOfCapacity_reserved_open hcapacity
  injective_on_fibre := by
    intro rho sigma htarget hpack
    let eta := rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho
    let rhoFibre : RlcTwoChannelTargetFibre
        (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure) eta := ⟨rho, rfl⟩
    let sigmaFibre : RlcTwoChannelTargetFibre
        (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure) eta :=
      ⟨sigma, htarget.symm⟩
    have hpackAt :
        rlc_twoChannelPIMSFixedPayloadConfigAt hcapacity eta rhoFibre =
          rlc_twoChannelPIMSFixedPayloadConfigAt hcapacity eta sigmaFibre :=
      (rlc_twoChannelPIMSFixedPayloadConfigOfCapacity_eq_at
        hcapacity eta rhoFibre).symm.trans <|
        hpack.trans <|
          rlc_twoChannelPIMSFixedPayloadConfigOfCapacity_eq_at
            hcapacity eta sigmaFibre
    have hbits :
        rlc_twoChannelPIMSFixedPayloadEmbeddingOfCapacity
            hcapacity eta rhoFibre =
          rlc_twoChannelPIMSFixedPayloadEmbeddingOfCapacity
            hcapacity eta sigmaFibre := by
      funext e
      have happ := congrFun hpackAt e.1.1
      simp only [rlc_twoChannelPIMSFixedPayloadConfigAt] at happ
      simp only [dif_neg e.1.2, dif_neg e.2] at happ
      simpa only [eta, rhoFibre, sigmaFibre] using happ
    have hfibre :=
      (rlc_twoChannelPIMSFixedPayloadEmbeddingOfCapacity
        hcapacity eta).injective hbits
    exact congrArg (fun fibre => fibre.1) hfibre

theorem RlcTwoChannelPIMSDiscardedPayloadPacking.target_eq_of_pack_eq
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (packing : RlcTwoChannelPIMSDiscardedPayloadPacking hclosure)
    {rho sigma : RlcTwoChannelEdgeFailure gamma gamma'}
    (hpack : packing.packConfig rho = packing.packConfig sigma) :
    rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho =
      rlc_twoChannelPIMSEdgeTargetOfClosure hclosure sigma := by
  apply Subtype.ext
  funext e
  by_cases hvariable : rlc_pimsEdgeEquiv (e.1.map Subtype.val) ∈
      rlc_connectorCentralFaceEdges gamma gamma'
  · let vtarget : RlcTwoChannelPIMSVariableTargetEdge gamma gamma' :=
      ⟨e, hvariable⟩
    exact (packing.variable_eq rho vtarget).symm.trans
      ((congrFun hpack e).trans (packing.variable_eq sigma vtarget))
  · let ftarget : RlcTwoChannelPIMSFixedTargetEdge gamma gamma' :=
      ⟨e, hvariable⟩
    simpa only [rlc_twoChannelPIMSEdgeTargetOfClosure_val] using
      rlc_twoChannelPIMSEdgeProjection_fixedTarget_eq rho.1 sigma.1 ftarget

theorem RlcTwoChannelPIMSDiscardedPayloadPacking.packConfig_success
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (packing : RlcTwoChannelPIMSDiscardedPayloadPacking hclosure)
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    rlc_twoChannelEdgeConfigExtend gamma gamma' (packing.packConfig rho) ∈
      rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
  apply (rlc_twoChannelCanonicalRoutePlan gamma gamma').success_of_reserved
    (rlc_twoChannelCanonicalRoute
      (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho))
  exact packing.reserved_open rho

noncomputable def RlcTwoChannelPIMSDiscardedPayloadPacking.embedding
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (packing : RlcTwoChannelPIMSDiscardedPayloadPacking hclosure) :
    RlcTwoChannelEdgeFailure gamma gamma' ↪
      RlcTwoChannelEdgeSuccess gamma gamma' where
  toFun rho := ⟨packing.packConfig rho, packing.packConfig_success rho⟩
  inj' rho sigma h := by
    have hpack := congrArg Subtype.val h
    exact packing.injective_on_fibre rho sigma
      (packing.target_eq_of_pack_eq hpack) hpack

theorem RlcTwoChannelPIMSDiscardedPayloadPacking.embedding_compatible
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (packing : RlcTwoChannelPIMSDiscardedPayloadPacking hclosure)
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    (rlc_twoChannelCanonicalRoutePlan gamma gamma').Compatible
      (rlc_twoChannelCanonicalRouteAvailable
        (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure)) rho
      (packing.embedding rho) := by
  let route := rlc_twoChannelCanonicalRoute
    (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho)
  refine ⟨route, rfl, ?_⟩
  constructor
  · exact packing.reserved_open rho
  · intro e hreserved hpayload
    exfalso
    apply hpayload
    change e ∈ Finset.univ \ rlc_twoChannelOpenEdgeSet route.1
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, hreserved⟩

theorem RlcTwoChannelPIMSDiscardedPayloadPacking.hasCodeHall
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (packing : RlcTwoChannelPIMSDiscardedPayloadPacking hclosure) :
    (rlc_twoChannelCanonicalRoutePlan gamma gamma').HasCodeHall
      (rlc_twoChannelCanonicalRouteAvailable
        (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure)) := by
  apply (rlc_twoChannelEdgeCodeHall_iff_exists_compatibleEmbedding
    gamma gamma'
    ((rlc_twoChannelCanonicalRoutePlan gamma gamma').Compatible
      (rlc_twoChannelCanonicalRouteAvailable
        (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure)))).mpr
  exact ⟨packing.embedding, packing.embedding_compatible⟩



noncomputable def RlcTwoChannelPIMSDiscardedPayloadPacking.recoverBase
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (packing : RlcTwoChannelPIMSDiscardedPayloadPacking hclosure)
    (eta : RlcTwoChannelEdgeSuccess gamma gamma') :
    RlcTwoChannelEdgeSuccess gamma gamma' :=
  if h : ∃ rho, packing.embedding rho = eta then
    rlc_twoChannelPIMSEdgeTargetOfClosure hclosure h.choose
  else eta

theorem RlcTwoChannelPIMSDiscardedPayloadPacking.recoverBase_embedding
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (packing : RlcTwoChannelPIMSDiscardedPayloadPacking hclosure)
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    packing.recoverBase (packing.embedding rho) =
      rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho := by
  unfold RlcTwoChannelPIMSDiscardedPayloadPacking.recoverBase
  split
  · rename_i h
    have hchosen : packing.embedding h.choose = packing.embedding rho :=
      h.choose_spec
    have hrho : h.choose = rho := packing.embedding.injective hchosen
    rw [hrho]
  · rename_i h
    exact False.elim (h ⟨rho, rfl⟩)



noncomputable def
    RlcTwoChannelPIMSDiscardedPayloadPacking.canonicalFibrePacking
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (packing : RlcTwoChannelPIMSDiscardedPayloadPacking hclosure) :
    RlcTwoChannelCanonicalFibrePacking
      (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure) where
  recoverBase := packing.recoverBase
  pack := packing.embedding
  recoverBase_pack := packing.recoverBase_embedding
  pack_injective_on_fibre := fun rho sigma _hbase hpack =>
    packing.embedding.injective hpack
  pack_mem_codeSet := fun rho => by
    have hcompatible := packing.embedding_compatible rho
    obtain ⟨route, hroute, hcode⟩ := hcompatible
    rw [hroute] at hcode
    exact hcode





def RlcBookFaithfulCanonicalPIMSRouteHall {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma') : Prop :=
  let hcentral :=
    rlc_centralFaceClosureFailureCertificate_of_retainedAnchorIncidence
      hinc
  let hclosure := rlc_twoChannelClosureFailureCertificate_of_centralFace
    gamma gamma' hcentral
  (rlc_twoChannelCanonicalRoutePlan gamma gamma').HasCodeHall
    (rlc_twoChannelCanonicalRouteAvailable
      (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure))



theorem
    rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_faithfulCanonicalPIMSRouteHall
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
    (hHall : RlcBookFaithfulCanonicalPIMSRouteHall hinc) :
    rlc_twoChannelForcedDualEventMass gamma gamma' (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ ≤
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  exact
    rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_dynamicRouteHall
      gamma gamma' (rlc_twoChannelCanonicalRoutePlan gamma gamma')
      (rlc_twoChannelCanonicalRouteAvailable
        (rlc_twoChannelPIMSEdgeTargetOfClosure
          (rlc_twoChannelClosureFailureCertificate_of_centralFace
            gamma gamma'
            (rlc_centralFaceClosureFailureCertificate_of_retainedAnchorIncidence
              hinc)))) hHall



theorem
    rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_faithfulPIMSFibrePacking
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
    (packing : RlcTwoChannelCanonicalFibrePacking
      (rlc_twoChannelPIMSEdgeTargetOfClosure
        (rlc_twoChannelClosureFailureCertificate_of_centralFace
          gamma gamma'
          (rlc_centralFaceClosureFailureCertificate_of_retainedAnchorIncidence
            hinc)))) :
    rlc_twoChannelForcedDualEventMass gamma gamma' (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ ≤
      FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1
        (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
  apply
    rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_faithfulCanonicalPIMSRouteHall
      hinc
  exact packing.hasCodeHall

#print axioms rlc_twoChannelCanonicalRoute_hasCodeHall_of_injective
#print axioms rlc_twoChannel_PIMS_and_exactDiscardedBits_injective
#print axioms
  rlc_twoChannel_PIMSEdgeProjection_and_exactDiscardedBits_injective
#print axioms
  rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_faithfulCanonicalPIMSRouteHall
#print axioms
  rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_faithfulPIMSFibrePacking

end

end StatMech.Universality
