/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.ScratchTwoChannelCanonicalRoute
import Code.FK.IndexedBoundaryCondition










open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box
open StatMech.Walls

noncomputable section


abbrev RlcTwoChannelAmbientSourceEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (e : Sym2 (Site 2)) :=
  {f : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet //
    f.1.map Subtype.val = e}

theorem rlc_twoChannelAmbientSourceEdge_unique {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {e : Sym2 (Site 2)}
    (f g : RlcTwoChannelAmbientSourceEdge gamma gamma' e) : f = g := by
  apply Subtype.ext
  apply Subtype.ext
  exact Sym2.map.injective Subtype.val_injective (f.2.trans g.2.symm)



noncomputable def rlc_twoChannelFullAmbientConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    ConfigSpace (Sym2 (Site 2)) := by
  classical
  exact fun e =>
    if hsource : Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma' e) then
      omega hsource.some.1
    else if e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 then true
    else false

@[simp] theorem rlc_twoChannelFullAmbientConfig_source {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (f : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet) :
    rlc_twoChannelFullAmbientConfig gamma gamma' omega
        (f.1.map Subtype.val) = omega f := by
  unfold rlc_twoChannelFullAmbientConfig
  split
  · rename_i hsource
    have heq : hsource.some =
        (⟨f, rfl⟩ : RlcTwoChannelAmbientSourceEdge gamma gamma'
          (f.1.map Subtype.val)) :=
      rlc_twoChannelAmbientSourceEdge_unique _ _
    rw [heq]
  · rename_i hsource
    exact False.elim (hsource ⟨⟨f, rfl⟩⟩)

theorem rlc_twoChannelFullAmbientConfig_trace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    rlc_twoChannelFullAmbientConfig gamma gamma' omega e = true := by
  unfold rlc_twoChannelFullAmbientConfig
  split
  · rename_i hsource
    obtain ⟨f⟩ := hsource
    exfalso
    induction hf : f.1.1 using Sym2.inductionOn with
    | _ x y =>
        have hfmem := f.1.2
        rw [hf, SimpleGraph.mem_edgeSet] at hfmem
        apply hfmem.2
        refine ⟨?_, ?_⟩
        · have hlat := hfmem.1.elim
            (fun h => h.1) (fun h => h.1)
          exact hlat
        · have heq : e = s((x : Site 2), (y : Site 2)) := by
            simpa [hf, Sym2.map_mk] using f.2.symm
          rw [heq] at he
          exact he
  · simp



noncomputable def rlc_twoChannelFullDualConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  rlc_connectorRestrictConfig
    (rlc_dualReflectConfig
      (rlc_twoChannelFullAmbientConfig gamma gamma' omega))

theorem rlc_twoChannelFullDualConfig_apply {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (e : Sym2 (RlcConnectorVertex n)) :
    rlc_twoChannelFullDualConfig gamma gamma' omega e =
      !(rlc_twoChannelFullAmbientConfig gamma gamma' omega
        (rlc_pimsEdgeEquiv (e.map Subtype.val))) := by
  unfold rlc_twoChannelFullDualConfig rlc_connectorRestrictConfig
  exact rlc_dualReflectConfig_eq_pims _ _



theorem rlc_twoChannelFullDualConfig_of_source {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (e : Sym2 (RlcConnectorVertex n))
    (f : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (hf : f.1.map Subtype.val =
      rlc_pimsEdgeEquiv (e.map Subtype.val)) :
    rlc_twoChannelFullDualConfig gamma gamma' omega e = !(omega f) := by
  rw [rlc_twoChannelFullDualConfig_apply]
  have hsource : rlc_twoChannelFullAmbientConfig gamma gamma' omega
      (rlc_pimsEdgeEquiv (e.map Subtype.val)) = omega f := by
    rw [← hf, rlc_twoChannelFullAmbientConfig_source]
  rw [hsource]



theorem rlc_twoChannelFullDualConfig_of_no_source {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (e : Sym2 (RlcConnectorVertex n))
    (hsource : ¬Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma'
      (rlc_pimsEdgeEquiv (e.map Subtype.val)))) :
    rlc_twoChannelFullDualConfig gamma gamma' omega e =
      if rlc_pimsEdgeEquiv (e.map Subtype.val) ∈
          rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 then
        false
      else true := by
  rw [rlc_twoChannelFullDualConfig_apply]
  unfold rlc_twoChannelFullAmbientConfig
  rw [dif_neg hsource]
  split <;> rfl



theorem rlc_twoChannelFullDualConfig_variable_eq_projection {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (e : RlcTwoChannelPIMSVariableTargetEdge gamma gamma') :
    rlc_twoChannelFullDualConfig gamma gamma' omega e.1 =
      rlc_twoChannelPIMSEdgeProjection gamma gamma' omega e.1 := by
  rw [rlc_twoChannelFullDualConfig_of_source gamma gamma' omega e.1
      (rlc_twoChannelPIMSSourceEdge e)
      (rlc_twoChannelPIMSSourceEdge_map e),
    rlc_twoChannelPIMSEdgeProjection_apply,
    rlc_twoChannelPIMSConfig_variableTarget_apply]





theorem rlc_twoChannelFullAmbientConfig_embeddedEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    rlc_twoChannelFullAmbientConfig gamma gamma' omega
        (Ising.kwg_embeddedEdge
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') f) =
      rlc_connectorForceTraceConfig gamma gamma'
        (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) f.1 := by
  classical
  induction hf : f.1 using Sym2.inductionOn with
  | _ x y =>
      change RlcConnectorVertex n at x y
      have hcarrier :
          (rlc_connectorTwoChannelGraph gamma gamma' ⊔
            rlc_connectorTraceWiring gamma gamma').Adj x y := by
        have hfmem := f.2
        rw [hf, SimpleGraph.mem_edgeSet] at hfmem
        exact hfmem
      rcases hcarrier with htwo | htrace
      · have hedge : s(x, y) ∈
            (rlc_connectorTwoChannelGraph gamma gamma').edgeSet := by
          rw [SimpleGraph.mem_edgeSet]
          exact htwo
        have hnotTrace : s(x, y) ∉
            (rlc_connectorTraceWiring gamma gamma').edgeFinset := by
          intro hmem
          exact htwo.2 ((SimpleGraph.mem_edgeSet _).mp
            (SimpleGraph.mem_edgeFinset.mp hmem))
        rw [Ising.kwg_embeddedEdge]
        simp only [rlc_connectorTwoChannelAugmentedPlanarDomain,
          hf, Sym2.map_mk]
        change rlc_twoChannelFullAmbientConfig gamma gamma' omega
            s((x : Site 2), (y : Site 2)) =
          rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) s(x, y)
        have hsource := rlc_twoChannelFullAmbientConfig_source
          gamma gamma' omega ⟨s(x, y), hedge⟩
        change rlc_twoChannelFullAmbientConfig gamma gamma' omega
            s((x : Site 2), (y : Site 2)) =
          omega ⟨s(x, y), hedge⟩ at hsource
        rw [hsource]
        simp [rlc_connectorForceTraceConfig, hnotTrace,
          rlc_twoChannelEdgeConfigExtend,
          rlc_twoChannelConfigSplitEquiv, hedge]
      · have htraceMem : s(x, y) ∈
            (rlc_connectorTraceWiring gamma gamma').edgeFinset :=
          SimpleGraph.mem_edgeFinset.mpr
            ((SimpleGraph.mem_edgeSet _).mpr htrace)
        rw [Ising.kwg_embeddedEdge]
        simp only [rlc_connectorTwoChannelAugmentedPlanarDomain,
          hf, Sym2.map_mk]
        change rlc_twoChannelFullAmbientConfig gamma gamma' omega
            s((x : Site 2), (y : Site 2)) =
          rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) s(x, y)
        rw [rlc_twoChannelFullAmbientConfig_trace gamma gamma' omega htrace.2]
        simp [rlc_connectorForceTraceConfig, htraceMem]



noncomputable def rlc_twoChannelReflectedDualEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    Sym2 (Site 2) :=
  s(rlc_dualReflect (Ising.kwg_flankLeft
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') f),
    rlc_dualReflect (Ising.kwg_flankRight
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') f))



@[simp] theorem rlc_pimsEdgeEquiv_twoChannelReflectedDualEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    rlc_pimsEdgeEquiv
        (rlc_twoChannelReflectedDualEdge gamma gamma' f) =
      Ising.kwg_embeddedEdge
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') f := by
  rw [rlc_twoChannelReflectedDualEdge,
    rlc_pimsEdgeEquiv_reflected_mk_of_adj
      (Ising.kwg_flanks_adj _ f), Ising.kwg_flanks_shared]



theorem rlc_twoChannelFullAmbientDual_reflectedEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    rlc_dualReflectConfig
        (rlc_twoChannelFullAmbientConfig gamma gamma' omega)
        (rlc_twoChannelReflectedDualEdge gamma gamma' f) =
      !(rlc_connectorForceTraceConfig gamma gamma'
        (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) f.1) := by
  rw [rlc_dualReflectConfig_eq_pims,
    rlc_pimsEdgeEquiv_twoChannelReflectedDualEdge,
    rlc_twoChannelFullAmbientConfig_embeddedEdge]



theorem rlc_twoChannelFullAmbientDual_reflectedEdge_open_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    rlc_dualReflectConfig
        (rlc_twoChannelFullAmbientConfig gamma gamma' omega)
          (rlc_twoChannelReflectedDualEdge gamma gamma' f) = true ↔
      f.1 ∉ (FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))).edgeSet := by
  rw [rlc_twoChannelFullAmbientDual_reflectedEdge]
  let forced := rlc_connectorForceTraceConfig gamma gamma'
    (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)
  constructor
  · intro hopen hmem
    have htrue : forced f.1 = true := by
      induction hf : f.1 using Sym2.inductionOn with
      | _ x y =>
          rw [hf, SimpleGraph.mem_edgeSet, FK.openSub_adj] at hmem
          simpa [forced, hf] using hmem.2
    simp [forced, htrue] at hopen
  · intro hclosed
    have hfalse : forced f.1 = false := by
      apply Bool.eq_false_of_not_eq_true
      intro htrue
      apply hclosed
      induction hf : f.1 using Sym2.inductionOn with
      | _ x y =>
          rw [SimpleGraph.mem_edgeSet, FK.openSub_adj]
          refine ⟨?_, ?_⟩
          · exact (SimpleGraph.mem_edgeSet _).mp (hf ▸ f.2)
          · simpa [forced, hf] using htrue
    simp [forced, hfalse]





theorem rlc_twoChannelFullAmbientConfig_open_mem_planarEdges {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {e : Sym2 (Site 2)}
    (hopen : rlc_twoChannelFullAmbientConfig gamma gamma' omega e = true) :
    e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  classical
  unfold rlc_twoChannelFullAmbientConfig at hopen
  split at hopen
  · rename_i hsource
    obtain ⟨f⟩ := hsource
    induction hf : f.1.1 using Sym2.inductionOn with
    | _ x y =>
        have htwo : (rlc_connectorTwoChannelGraph gamma gamma').Adj x y := by
          have hfmem := f.1.2
          rw [hf, SimpleGraph.mem_edgeSet] at hfmem
          exact hfmem
        have hclosure :
            (rlc_connectorCentralFaceClosureGraph gamma gamma').Adj x y := by
          rw [rlc_connectorCentralFaceClosureGraph_eq_twoChannel_sup_trace]
          exact Or.inl htwo
        have heq : e = s((x : Site 2), (y : Site 2)) := by
          simpa [hf, Sym2.map_mk] using f.2.symm
        rw [heq]
        exact hclosure.2
  · rename_i hsource
    split at hopen
    · rename_i htrace
      rw [rlc_connectorCentralFacePlanarEdges,
        rlc_connectorFourTraceEdges]
      exact Finset.mem_union_right _ (Finset.mem_union_left _ htrace)
    · simp at hopen




theorem rlc_openSub_twoChannelAugmented_forceTrace_eq_fullAmbientInduce
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)) =
      openSubgraphInduce 2
        (rlc_twoChannelFullAmbientConfig gamma gamma' omega)
        (rect (-2 * n) (2 * n) (-n) n) := by
  classical
  ext x y
  change RlcConnectorVertex n at x y
  rw [FK.openSub_adj, openSubgraphInduce_adj]
  constructor
  · rintro ⟨hcarrier, hopen⟩
    let f : Ising.kwg_Edge
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') :=
      ⟨s(x, y), by
        rw [SimpleGraph.mem_edgeSet]
        exact hcarrier⟩
    have hf : f.1 = s(x, y) := rfl
    have hemb : Ising.kwg_embeddedEdge
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') f =
        s((x : Site 2), (y : Site 2)) := by
      rw [Ising.kwg_embeddedEdge, hf]
      rfl
    refine ⟨(rlc_connectorTwoChannelAugmentedPlanarDomain
      gamma gamma').isSub hcarrier, ?_⟩
    have hedge := rlc_twoChannelFullAmbientConfig_embeddedEdge
      gamma gamma' omega f
    rw [← hemb, hedge, hf]
    exact hopen
  · rintro ⟨hadj, hopen⟩
    have hplanar := rlc_twoChannelFullAmbientConfig_open_mem_planarEdges
      gamma gamma' omega hopen
    have hcarrier :
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G.Adj x y := by
      rw [rlc_connectorTwoChannelAugmentedGraph_eq_closure]
      exact ⟨hadj, by simpa [Sym2.map_mk] using hplanar⟩
    refine ⟨hcarrier, ?_⟩
    let f : Ising.kwg_Edge
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') :=
      ⟨s(x, y), by
        rw [SimpleGraph.mem_edgeSet]
        exact hcarrier⟩
    have hf : f.1 = s(x, y) := rfl
    have hemb : Ising.kwg_embeddedEdge
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') f =
        s((x : Site 2), (y : Site 2)) := by
      rw [Ising.kwg_embeddedEdge, hf]
      rfl
    have hedge := rlc_twoChannelFullAmbientConfig_embeddedEdge
      gamma gamma' omega f
    calc
      rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) s(x, y) =
          rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) f.1 :=
        congrArg _ hf.symm
      _ = rlc_twoChannelFullAmbientConfig gamma gamma' omega
          (Ising.kwg_embeddedEdge
            (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') f) :=
        hedge.symm
      _ = rlc_twoChannelFullAmbientConfig gamma gamma' omega
          s((x : Site 2), (y : Site 2)) := congrArg _ hemb
      _ = true := hopen



def rlc_twoChannelFullReachSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') : Set (Site 2) :=
  {z | ∃ hz : z ∈ rect (-2 * n) (2 * n) (-n) n,
    ConnectedWithin 2 (rlc_twoChannelFullAmbientConfig gamma gamma' omega)
      (rect (-2 * n) (2 * n) (-n) n)
      ⟨(rlc_connectorRightAnchor gamma : Site 2),
        (rlc_connectorRightAnchor gamma).2⟩ ⟨z, hz⟩}

theorem rlc_twoChannelFullReachSet_subset_box {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelFullReachSet gamma gamma' omega ⊆
      rect (-2 * n) (2 * n) (-n) n := by
  rintro z ⟨hz, _⟩
  exact hz

theorem rlc_twoChannelFullReachSet_finite {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    (rlc_twoChannelFullReachSet gamma gamma' omega).Finite :=
  (rect_finite (-2 * n) (2 * n) (-n) n).subset
    (rlc_twoChannelFullReachSet_subset_box gamma gamma' omega)



theorem rlc_rightPathVertex_mem_twoChannelFullReachSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {z : Site 2}
    (hz : z ∈ rlc_pathVertices gamma.1) :
    z ∈ rlc_twoChannelFullReachSet gamma gamma' omega := by
  let z' : RlcConnectorVertex n :=
    ⟨z, rlc_rightPathVertex_mem_connectorBox gamma hz⟩
  have htrace := rlc_connectorTraceWiring_reachable_right gamma gamma'
    (rlc_connectorRightAnchor_onRight gamma)
      (show rlc_connectorOnRight gamma z' from hz)
  have hsource :
      (FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))).Reachable
          (rlc_connectorRightAnchor gamma) z' := by
    rw [rlc_openSub_twoChannelAugmented_forceTrace]
    exact htrace.mono le_sup_right
  refine ⟨z'.2, ?_⟩
  change (openSubgraphInduce 2
    (rlc_twoChannelFullAmbientConfig gamma gamma' omega)
    (rect (-2 * n) (2 * n) (-n) n)).Reachable
      ⟨(rlc_connectorRightAnchor gamma : Site 2),
        (rlc_connectorRightAnchor gamma).2⟩ ⟨z, z'.2⟩
  rw [← rlc_openSub_twoChannelAugmented_forceTrace_eq_fullAmbientInduce]
  exact hsource



theorem rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {z : Site 2} (hz : z ∈ rlc_pathVertices gamma'.1) :
    z ∉ rlc_twoChannelFullReachSet gamma gamma' omega := by
  rintro ⟨hzBox, hzReach⟩
  let z' : RlcConnectorVertex n := ⟨z, hzBox⟩
  have hzSource :
      (FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))).Reachable
          (rlc_connectorRightAnchor gamma) z' := by
    rw [rlc_openSub_twoChannelAugmented_forceTrace_eq_fullAmbientInduce]
    exact hzReach
  have hleft := rlc_connectorTraceWiring_reachable_left gamma gamma'
    (show rlc_connectorOnLeft gamma' z' from hz)
      (rlc_connectorLeftAnchor_onLeft gamma')
  rw [rlc_openSub_twoChannelAugmented_forceTrace] at hzSource
  have hanchors := hzSource.trans (hleft.mono
    (show rlc_connectorTraceWiring gamma gamma' ≤
      FK.openSub (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) ⊔
        rlc_connectorTraceWiring gamma gamma' from le_sup_right))
  exact hno ((rlc_exists_connector_iff_traceAnchors gamma gamma'
    (FK.openSub (rlc_connectorTwoChannelGraph gamma gamma')
      (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))).mpr hanchors)


theorem rlc_twoChannelFullReachSet_extend {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {v w : Site 2}
    (hv : v ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hw : w ∈ rect (-2 * n) (2 * n) (-n) n)
    (hadj : (hypercubicLattice 2).Adj v w)
    (hopen : rlc_twoChannelFullAmbientConfig gamma gamma' omega
      s(v, w) = true) :
    w ∈ rlc_twoChannelFullReachSet gamma gamma' omega := by
  obtain ⟨hvBox, hvReach⟩ := hv
  refine ⟨hw, hvReach.trans ?_⟩
  exact (show (openSubgraphInduce 2
    (rlc_twoChannelFullAmbientConfig gamma gamma' omega)
    (rect (-2 * n) (2 * n) (-n) n)).Adj
      ⟨v, hvBox⟩ ⟨w, hw⟩ from ⟨hadj, hopen⟩).reachable



theorem rlc_twoChannelFullReachSet_edgeBoundary_closed {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {v w : Site 2}
    (hvw : (v, w) ∈ edgeBoundary 2
      (rlc_twoChannelFullReachSet gamma gamma' omega)) :
    rlc_twoChannelFullAmbientConfig gamma gamma' omega s(v, w) = false := by
  obtain ⟨hadj, hsplit⟩ := hvw
  by_cases hv : v ∈ rlc_twoChannelFullReachSet gamma gamma' omega
  · have hw : w ∉ rlc_twoChannelFullReachSet gamma gamma' omega := hsplit.mp hv
    by_contra hopen
    rw [Bool.not_eq_false] at hopen
    have hedge := rlc_twoChannelFullAmbientConfig_open_mem_planarEdges
      gamma gamma' omega hopen
    have hwBox := rlc_connectorCentralFacePlanarEdge_endpoints_mem_box
      gamma gamma' hedge (Sym2.mem_mk_right v w)
    exact hw (rlc_twoChannelFullReachSet_extend gamma gamma' omega hv
      (by simpa [rlc_connectorBox] using hwBox) hadj hopen)
  · have hw : w ∈ rlc_twoChannelFullReachSet gamma gamma' omega := by
      by_contra hw
      exact hv (hsplit.mpr hw)
    rw [Sym2.eq_swap]
    by_contra hopen
    rw [Bool.not_eq_false] at hopen
    have hedge := rlc_twoChannelFullAmbientConfig_open_mem_planarEdges
      gamma gamma' omega hopen
    have hvBox := rlc_connectorCentralFacePlanarEdge_endpoints_mem_box
      gamma gamma' hedge (Sym2.mem_mk_right w v)
    exact hv (rlc_twoChannelFullReachSet_extend gamma gamma' omega hw
      (by simpa [rlc_connectorBox] using hvBox) hadj.symm hopen)



theorem rlc_twoChannelFullBoundary_le_openFaceDual {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    faceBoundaryGraph (rlc_twoChannelFullReachSet gamma gamma' omega) ≤
      openSubgraph 2 (fci_faceDualConfig
        (rlc_twoChannelFullAmbientConfig gamma gamma' omega)) := by
  intro f g hfg
  obtain ⟨p, q, hpq, hpqAdj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  have hpqBoundary : (p, q) ∈ edgeBoundary 2
      (rlc_twoChannelFullReachSet gamma gamma' omega) := by
    refine ⟨hpqAdj, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hfg.2
  have hclosed := rlc_twoChannelFullReachSet_edgeBoundary_closed
    gamma gamma' omega hpqBoundary
  refine ⟨hfg.1, ?_⟩
  rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj hfg.1, hpq]
  simpa using hclosed



theorem rlc_twoChannelFullReachSet_edgeBoundary_nonempty {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    (edgeBoundary 2
      (rlc_twoChannelFullReachSet gamma gamma' omega)).Nonempty := by
  let v : Site 2 := gamma.1.2.1
  let w : Site 2 := v + ![1, 0]
  have hvPath : v ∈ rlc_pathVertices gamma.1 :=
    rlc_connector_path_end_mem_vertices gamma.1
  have hv : v ∈ rlc_twoChannelFullReachSet gamma gamma' omega :=
    rlc_rightPathVertex_mem_twoChannelFullReachSet gamma gamma' omega hvPath
  have hvx : v 0 = 2 * n := by
    simpa only [v] using gamma.1.2.1.2.2
  have hw0 : w 0 = v 0 + 1 := by
    change ((v + (![1, 0] : Site 2) : Site 2) 0) = v 0 + 1
    rw [Pi.add_apply]
    rfl
  have hw1 : w 1 = v 1 := by
    change ((v + (![1, 0] : Site 2) : Site 2) 1) = v 1
    rw [Pi.add_apply]
    simp
  have hadj : (hypercubicLattice 2).Adj v w := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two, hw0, hw1]
    simp
  have hw : w ∉ rlc_twoChannelFullReachSet gamma gamma' omega := by
    intro hwReach
    have hwR := rlc_twoChannelFullReachSet_subset_box
      gamma gamma' omega hwReach
    rw [mem_rect] at hwR
    have : w 0 = 2 * n + 1 := by rw [hw0, hvx]
    omega
  exact ⟨(v, w), hadj, iff_of_true hv hw⟩


theorem rlc_twoChannelFullReachSet_dualCircuit {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    ∃ (u : Site 2)
      (c : (faceBoundaryGraph
        (rlc_twoChannelFullReachSet gamma gamma' omega)).Walk u u),
      c.IsCycle := by
  obtain ⟨⟨v, w⟩, hvw⟩ :=
    rlc_twoChannelFullReachSet_edgeBoundary_nonempty gamma gamma' omega
  exact exists_dualCircuit_of_finite_of_edgeBoundary
    (rlc_twoChannelFullReachSet gamma gamma' omega)
    (rlc_twoChannelFullReachSet_finite gamma gamma' omega) hvw


theorem rlc_twoChannelFullReachSet_openFaceDualCircuit {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    ∃ (u : Site 2)
      (c : (openSubgraph 2 (fci_faceDualConfig
        (rlc_twoChannelFullAmbientConfig gamma gamma' omega))).Walk u u),
      c.IsCycle := by
  obtain ⟨u, c, hcyc⟩ :=
    rlc_twoChannelFullReachSet_dualCircuit gamma gamma' omega
  let hle := rlc_twoChannelFullBoundary_le_openFaceDual gamma gamma' omega
  exact ⟨u, c.mapLe hle, hcyc.mapLe hle⟩



theorem rlc_twoChannelFullReachSet_reflectedOpenDualCircuit {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    ∃ (u : Site 2)
      (c : (openSubgraph 2 (rlc_dualReflectConfig
        (rlc_twoChannelFullAmbientConfig gamma gamma' omega))).Walk
          (rlc_dualReflect u) (rlc_dualReflect u)),
      c.IsCycle := by
  obtain ⟨u, c, hcyc⟩ :=
    rlc_twoChannelFullReachSet_openFaceDualCircuit gamma gamma' omega
  exact ⟨u, rlc_dualReflectOpenWalk _ c,
    rlc_dualReflectOpenWalk_isCycle _ hcyc⟩



theorem rlc_twoChannelFullReachSet_axis_boundary_of_failure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    ∃ p q : Site 2,
      (p, q) ∈ edgeBoundary 2
        (rlc_twoChannelFullReachSet gamma gamma' omega) ∧
      p ∈ rect (-2 * n) (2 * n) (-n) n ∧
      q ∈ rect (-2 * n) (2 * n) (-n) n ∧
      p 0 = 0 ∧ q 0 = 0 := by
  let x : Site 2 := gamma.1.1
  let y : Site 2 := gamma'.1.2.1
  have hxPath : x ∈ rlc_pathVertices gamma.1 :=
    rlc_path_start_mem_vertices gamma.1
  have hyPath : y ∈ rlc_pathVertices gamma'.1 :=
    rlc_connector_path_end_mem_vertices gamma'.1
  have hxReach := rlc_rightPathVertex_mem_twoChannelFullReachSet
    gamma gamma' omega hxPath
  have hyNot :=
    rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure
      gamma gamma' omega hno hyPath
  have hx0 : x 0 = 0 := gamma.1.1.2.2
  have hy0 : y 0 = 0 := gamma'.1.2.1.2.2
  have hxx : x = ![0, x 1] := by
    ext i
    fin_cases i <;> simp [hx0]
  have hyy : y = ![0, y 1] := by
    ext i
    fin_cases i <;> simp [hy0]
  let w : (hypercubicLattice 2).Walk x y :=
    (sw_vertSeg 0 (x 1) (y 1)).copy hxx.symm hyy.symm
  obtain ⟨p, q, hpq, hpqEdge⟩ := rlc_walk_mem_edgeBoundary_edges
    (rlc_twoChannelFullReachSet gamma gamma' omega) w hxReach hyNot
  have hpSupp : p ∈ w.support := w.fst_mem_support_of_mem_edges hpqEdge
  have hqSupp : q ∈ w.support := w.snd_mem_support_of_mem_edges hpqEdge
  have hsupport (z : Site 2) (hz : z ∈ w.support) :
      ∃ t : Int, t ∈ Set.uIcc (x 1) (y 1) ∧ z = ![0, t] := by
    change z ∈ ((sw_vertSeg 0 (x 1) (y 1)).copy _ _).support at hz
    rw [SimpleGraph.Walk.support_copy, sw_vertSeg_mem_support] at hz
    exact hz
  obtain ⟨tp, htp, rfl⟩ := hsupport p hpSupp
  obtain ⟨tq, htq, rfl⟩ := hsupport q hqSupp
  have hxRows : -n ≤ x 1 ∧ x 1 ≤ n := by
    have h := gamma.1.1.2.1
    rw [mem_rect] at h
    exact h.2.2
  have hyRows : -n ≤ y 1 ∧ y 1 ≤ n := by
    have h := gamma'.1.2.1.2.1
    rw [mem_rect] at h
    exact h.2.2
  have htpRows : -n ≤ tp ∧ tp ≤ n := by
    rw [Set.mem_uIcc] at htp
    rcases htp with htp | htp <;> omega
  have htqRows : -n ≤ tq ∧ tq ≤ n := by
    rw [Set.mem_uIcc] at htq
    rcases htq with htq | htq <;> omega
  refine ⟨![0, tp], ![0, tq], hpq, ?_, ?_, by simp, by simp⟩
  · rw [mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · rw [mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega



theorem rlc_twoChannelFullReachSet_axis_anchored_dualCircuit {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    ∃ (p q f g u : Site 2)
      (c : (faceBoundaryGraph
        (rlc_twoChannelFullReachSet gamma gamma' omega)).Walk u u),
      (p, q) ∈ edgeBoundary 2
        (rlc_twoChannelFullReachSet gamma gamma' omega) ∧
      p ∈ rect (-2 * n) (2 * n) (-n) n ∧
      q ∈ rect (-2 * n) (2 * n) (-n) n ∧
      p 0 = 0 ∧ q 0 = 0 ∧
      (faceBoundaryGraph
        (rlc_twoChannelFullReachSet gamma gamma' omega)).Adj f g ∧
      sharedPrimalEdge f g = s(p, q) ∧
      c.IsCycle ∧ s(f, g) ∈ c.edges := by
  classical
  obtain ⟨p, q, hpq, hpR, hqR, hp0, hq0⟩ :=
    rlc_twoChannelFullReachSet_axis_boundary_of_failure
      gamma gamma' omega hno
  obtain ⟨f, g, hfgLat, hshared⟩ := jfc_flankingFaces hpq.1
  have hfg : (faceBoundaryGraph
      (rlc_twoChannelFullReachSet gamma gamma' omega)).Adj f g := by
    refine ⟨hfgLat, ?_⟩
    rw [hshared, bdEdge_mk]
    exact hpq.2
  obtain ⟨T, hT⟩ := exists_finset_support_faceBoundaryGraph
    (rlc_twoChannelFullReachSet gamma gamma' omega)
    (rlc_twoChannelFullReachSet_finite gamma gamma' omega)
  obtain ⟨u, c, hcyc, hedge⟩ :=
    EvenDegree.exists_cycle_through_edge_of_even_of_finite_support
      (faceBoundaryGraph (rlc_twoChannelFullReachSet gamma gamma' omega))
      T hT (degree_faceBoundaryGraph_even
        (rlc_twoChannelFullReachSet gamma gamma' omega)) hfg
  exact ⟨p, q, f, g, u, c, hpq, hpR, hqR, hp0, hq0,
    hfg, hshared, hcyc, hedge⟩





theorem rlc_twoChannelFullReachSet_openWalk_lift {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {u v : RlcConnectorVertex n}
    (hu : (u : Site 2) ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (w : (openSubgraphInduce 2
      (rlc_twoChannelFullAmbientConfig gamma gamma' omega)
      (rect (-2 * n) (2 * n) (-n) n)).Walk u v) :
    ∃ hv : (v : Site 2) ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
      ((hypercubicLattice 2).induce
        (rlc_twoChannelFullReachSet gamma gamma' omega)).Reachable
          ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction w with
  | nil => exact ⟨hu, Reachable.refl _⟩
  | @cons a b c hab p ih =>
      have habOpen : (openSubgraph 2
          (rlc_twoChannelFullAmbientConfig gamma gamma' omega)).Adj
          (a : Site 2) (b : Site 2) := hab
      have hb : (b : Site 2) ∈
          rlc_twoChannelFullReachSet gamma gamma' omega :=
        rlc_twoChannelFullReachSet_extend gamma gamma' omega hu b.2
          habOpen.1 habOpen.2
      obtain ⟨hc, hbc⟩ := ih hb
      have habReach : ((hypercubicLattice 2).induce
          (rlc_twoChannelFullReachSet gamma gamma' omega)).Adj
          ⟨a, hu⟩ ⟨b, hb⟩ := habOpen.1
      exact ⟨hc, habReach.reachable.trans hbc⟩


theorem rlc_twoChannelFullReachSet_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {u v : Site 2}
    (hu : u ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hv : v ∈ rlc_twoChannelFullReachSet gamma gamma' omega) :
    ((hypercubicLattice 2).induce
      (rlc_twoChannelFullReachSet gamma gamma' omega)).Reachable
        ⟨u, hu⟩ ⟨v, hv⟩ := by
  have hu0 := hu
  have hv0 := hv
  obtain ⟨_huBox, huSource⟩ := hu
  obtain ⟨_hvBox, hvSource⟩ := hv
  have hsource : (rlc_connectorRightAnchor gamma : Site 2) ∈
      rlc_twoChannelFullReachSet gamma gamma' omega :=
    ⟨(rlc_connectorRightAnchor gamma).2, Reachable.refl _⟩
  obtain ⟨hu', huLift⟩ := rlc_twoChannelFullReachSet_openWalk_lift
    gamma gamma' omega hu0 huSource.some.reverse
  obtain ⟨hv', hvLift⟩ := rlc_twoChannelFullReachSet_openWalk_lift
    gamma gamma' omega hsource hvSource.some
  have huEq :
      (⟨(rlc_connectorRightAnchor gamma : Site 2), hu'⟩ :
        rlc_twoChannelFullReachSet gamma gamma' omega) =
      ⟨(rlc_connectorRightAnchor gamma : Site 2), hsource⟩ := rfl
  have hvEq :
      (⟨v, hv'⟩ : rlc_twoChannelFullReachSet gamma gamma' omega) =
      ⟨v, hv0⟩ := rfl
  rw [huEq] at huLift
  rw [hvEq] at hvLift
  exact huLift.trans hvLift



noncomputable def rlc_twoChannelFullExteriorComponent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    ((hypercubicLattice 2).induce
      (rlc_twoChannelFullReachSet gamma gamma' omega)ᶜ).ConnectedComponent :=
  Classical.choose (unique_infinite_component (by norm_num)
    (rlc_twoChannelFullReachSet gamma gamma' omega)
    (rlc_twoChannelFullReachSet_finite gamma gamma' omega))

theorem rlc_twoChannelFullExteriorComponent_infinite {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    (rlc_twoChannelFullExteriorComponent gamma gamma' omega).supp.Infinite :=
  (Classical.choose_spec (unique_infinite_component (by norm_num)
    (rlc_twoChannelFullReachSet gamma gamma' omega)
    (rlc_twoChannelFullReachSet_finite gamma gamma' omega))).1


def rlc_twoChannelFullExteriorSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') : Set (Site 2) :=
  {z | ∃ hz : z ∈ (rlc_twoChannelFullReachSet gamma gamma' omega)ᶜ,
    ((hypercubicLattice 2).induce
      (rlc_twoChannelFullReachSet gamma gamma' omega)ᶜ).connectedComponentMk
        ⟨z, hz⟩ = rlc_twoChannelFullExteriorComponent gamma gamma' omega}


def rlc_twoChannelFullFilledReachSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') : Set (Site 2) :=
  (rlc_twoChannelFullExteriorSet gamma gamma' omega)ᶜ

theorem rlc_twoChannelFullReachSet_subset_filled {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelFullReachSet gamma gamma' omega ⊆
      rlc_twoChannelFullFilledReachSet gamma gamma' omega := by
  intro z hz hExt
  exact hExt.1 hz

theorem rlc_twoChannelFullExteriorSet_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {u v : Site 2}
    (hu : u ∈ rlc_twoChannelFullExteriorSet gamma gamma' omega)
    (hv : v ∈ rlc_twoChannelFullExteriorSet gamma gamma' omega) :
    ((hypercubicLattice 2).induce
      (rlc_twoChannelFullExteriorSet gamma gamma' omega)).Reachable
        ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨huNot, huComp⟩ := hu
  obtain ⟨hvNot, hvComp⟩ := hv
  have hcomp : ((hypercubicLattice 2).induce
      (rlc_twoChannelFullReachSet gamma gamma' omega)ᶜ).Reachable
      ⟨u, huNot⟩ ⟨v, hvNot⟩ :=
    ConnectedComponent.eq.mp (huComp.trans hvComp.symm)
  obtain ⟨w⟩ := hcomp
  let p : (hypercubicLattice 2).Walk u v :=
    w.map (SimpleGraph.Embedding.induce
      (rlc_twoChannelFullReachSet gamma gamma' omega)ᶜ).toHom
  have hpExt : ∀ z ∈ p.support,
      z ∈ rlc_twoChannelFullExteriorSet gamma gamma' omega := by
    intro z hz
    have hz' : z ∈ (w.map (SimpleGraph.Embedding.induce
        (rlc_twoChannelFullReachSet gamma gamma' omega)ᶜ).toHom).support := hz
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hz'
    obtain ⟨a, ha, rfl⟩ := hz'
    refine ⟨a.2, ?_⟩
    exact (ConnectedComponent.sound
      ⟨(w.takeUntil a ha).reverse⟩).trans huComp
  exact ⟨p.induce (rlc_twoChannelFullExteriorSet gamma gamma' omega) hpExt⟩

theorem rlc_twoChannelFullFilledReachSet_finite {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    (rlc_twoChannelFullFilledReachSet gamma gamma' omega).Finite := by
  let K := rlc_twoChannelFullReachSet gamma gamma' omega
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box K
    (rlc_twoChannelFullReachSet_finite gamma gamma' omega)
  apply (box_finite 2 R).subset
  intro z hzFill
  by_contra hzBox
  have hzExt : z ∈ exterior 2 R := by
    rw [exterior_eq_compl_box]
    exact hzBox
  have hzNotK : z ∈ Kᶜ := exterior_subset_compl K R hR hzExt
  have hzInf : (((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨z, hzNotK⟩).supp.Infinite :=
    exterior_mem_infiniteComponent (by norm_num) K R hR hzExt
  have hzComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨z, hzNotK⟩ = rlc_twoChannelFullExteriorComponent gamma gamma' omega :=
    (unique_infinite_component (by norm_num) K
      (rlc_twoChannelFullReachSet_finite gamma gamma' omega)).unique
        hzInf (rlc_twoChannelFullExteriorComponent_infinite gamma gamma' omega)
  exact hzFill ⟨hzNotK, hzComp⟩


theorem rlc_twoChannelFullFilledReachSet_subset_connectorRect {n : Int}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelFullFilledReachSet gamma gamma' omega ⊆
      rect (-2 * n) (2 * n) (-n) n := by
  let K := rlc_twoChannelFullReachSet gamma gamma' omega
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box K
    (rlc_twoChannelFullReachSet_finite gamma gamma' omega)
  have hKRect : K ⊆ rect (-2 * n) (2 * n) (-n) n :=
    rlc_twoChannelFullReachSet_subset_box gamma gamma' omega
  have promote {z q : Site 2}
      (hzNot : z ∈ Kᶜ) (hqExt : q ∈ exterior 2 R)
      (hzq : ((hypercubicLattice 2).induce Kᶜ).Reachable
        ⟨z, hzNot⟩ ⟨q, exterior_subset_compl K R hR hqExt⟩) :
      z ∈ rlc_twoChannelFullExteriorSet gamma gamma' omega := by
    let hqNot : q ∈ Kᶜ := exterior_subset_compl K R hR hqExt
    have hqInf : (((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
        ⟨q, hqNot⟩).supp.Infinite :=
      exterior_mem_infiniteComponent (by norm_num) K R hR hqExt
    have hqComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
        ⟨q, hqNot⟩ = rlc_twoChannelFullExteriorComponent gamma gamma' omega :=
      (unique_infinite_component (by norm_num) K
        (rlc_twoChannelFullReachSet_finite gamma gamma' omega)).unique
          hqInf (rlc_twoChannelFullExteriorComponent_infinite gamma gamma' omega)
    exact ⟨hzNot, (ConnectedComponent.sound hzq).trans hqComp⟩
  intro z hzFill
  rw [mem_rect]
  by_contra hzRect
  have hzCases : z 0 < -2 * n ∨ 2 * n < z 0 ∨
      z 1 < -n ∨ n < z 1 := by omega
  have hzNot : z ∈ Kᶜ := by
    intro hzK
    exact hzRect (by simpa [mem_rect] using hKRect hzK)
  rcases hzCases with hzLeft | hzRight | hzBottom | hzTop
  · let c : Int := z 0 - R - 1
    let q := Function.update z (0 : Fin 2) c
    have hqExt : q ∈ exterior 2 R := by
      refine ⟨0, ?_⟩
      simp [q, c]
      omega
    have hqNot : q ∈ Kᶜ := exterior_subset_compl K R hR hqExt
    have hreach : ((hypercubicLattice 2).induce Kᶜ).Reachable
        ⟨z, hzNot⟩ ⟨q, hqNot⟩ := by
      apply segment_gen Kᶜ (0 : Fin 2) z c hzNot hqNot
      intro t ht htK
      have htRect := hKRect htK
      rw [mem_rect] at htRect
      simp at htRect
      have hc : c ≤ z 0 := by dsimp only [c]; omega
      have htBounds : c ≤ t ∧ t ≤ z 0 := by
        simpa [min_eq_right hc, max_eq_left hc] using ht
      omega
    exact False.elim (hzFill (promote hzNot hqExt hreach))
  · let c : Int := z 0 + R + 1
    let q := Function.update z (0 : Fin 2) c
    have hqExt : q ∈ exterior 2 R := by
      refine ⟨0, ?_⟩
      simp [q, c]
      omega
    have hqNot : q ∈ Kᶜ := exterior_subset_compl K R hR hqExt
    have hreach : ((hypercubicLattice 2).induce Kᶜ).Reachable
        ⟨z, hzNot⟩ ⟨q, hqNot⟩ := by
      apply segment_gen Kᶜ (0 : Fin 2) z c hzNot hqNot
      intro t ht htK
      have htRect := hKRect htK
      rw [mem_rect] at htRect
      simp at htRect
      have hc : z 0 ≤ c := by dsimp only [c]; omega
      have htBounds : z 0 ≤ t ∧ t ≤ c := by
        simpa [min_eq_left hc, max_eq_right hc] using ht
      omega
    exact False.elim (hzFill (promote hzNot hqExt hreach))
  · let c : Int := z 1 - R - 1
    let q := Function.update z (1 : Fin 2) c
    have hqExt : q ∈ exterior 2 R := by
      refine ⟨1, ?_⟩
      simp [q, c]
      omega
    have hqNot : q ∈ Kᶜ := exterior_subset_compl K R hR hqExt
    have hreach : ((hypercubicLattice 2).induce Kᶜ).Reachable
        ⟨z, hzNot⟩ ⟨q, hqNot⟩ := by
      apply segment_gen Kᶜ (1 : Fin 2) z c hzNot hqNot
      intro t ht htK
      have htRect := hKRect htK
      rw [mem_rect] at htRect
      simp at htRect
      have hc : c ≤ z 1 := by dsimp only [c]; omega
      have htBounds : c ≤ t ∧ t ≤ z 1 := by
        simpa [min_eq_right hc, max_eq_left hc] using ht
      omega
    exact False.elim (hzFill (promote hzNot hqExt hreach))
  · let c : Int := z 1 + R + 1
    let q := Function.update z (1 : Fin 2) c
    have hqExt : q ∈ exterior 2 R := by
      refine ⟨1, ?_⟩
      simp [q, c]
      omega
    have hqNot : q ∈ Kᶜ := exterior_subset_compl K R hR hqExt
    have hreach : ((hypercubicLattice 2).induce Kᶜ).Reachable
        ⟨z, hzNot⟩ ⟨q, hqNot⟩ := by
      apply segment_gen Kᶜ (1 : Fin 2) z c hzNot hqNot
      intro t ht htK
      have htRect := hKRect htK
      rw [mem_rect] at htRect
      simp at htRect
      have hc : z 1 ≤ c := by dsimp only [c]; omega
      have htBounds : z 1 ≤ t ∧ t ≤ c := by
        simpa [min_eq_left hc, max_eq_right hc] using ht
      omega
    exact False.elim (hzFill (promote hzNot hqExt hreach))

private theorem rlc_twoChannelFull_walk_first_exit_set
    (A : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (hx : x ∈ A) (hy : y ∉ A) :
    ∃ (a b : Site 2) (p : (hypercubicLattice 2).Walk x a),
      (hypercubicLattice 2).Adj a b ∧
        (∀ z ∈ p.support, z ∈ A) ∧ b ∉ A := by
  induction w with
  | nil => exact absurd hx hy
  | @cons a b c hab p ih =>
      by_cases hb : b ∈ A
      · obtain ⟨u, v, q, huv, hq, hv⟩ := ih hb hy
        refine ⟨u, v, Walk.cons hab q, huv, ?_, hv⟩
        simp only [SimpleGraph.Walk.support_cons, List.forall_mem_cons]
        exact ⟨hx, hq⟩
      · exact ⟨a, b, Walk.nil, hab, by simpa, hb⟩



theorem rlc_twoChannelFullFilledReachSet_reaches_reachSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {u : Site 2}
    (hu : u ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
    ∃ z : Site 2,
      ∃ hz : z ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
      ((hypercubicLattice 2).induce
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Reachable
          ⟨u, hu⟩
          ⟨z, rlc_twoChannelFullReachSet_subset_filled
            gamma gamma' omega hz⟩ := by
  let K := rlc_twoChannelFullReachSet gamma gamma' omega
  let H := rlc_twoChannelFullFilledReachSet gamma gamma' omega
  by_cases huK : u ∈ K
  · exact ⟨u, huK, Reachable.refl _⟩
  let A : Set (Site 2) := {z | ∃ hz : z ∈ Kᶜ,
    ((hypercubicLattice 2).induce Kᶜ).Reachable
      ⟨u, huK⟩ ⟨z, hz⟩}
  have huA : u ∈ A := ⟨huK, Reachable.refl _⟩
  let k : Site 2 := gamma.1.1
  have hkK : k ∈ K :=
    rlc_rightPathVertex_mem_twoChannelFullReachSet gamma gamma' omega
      (rlc_path_start_mem_vertices gamma.1)
  have hkNotA : k ∉ A := by
    rintro ⟨hkNot, _⟩
    exact hkNot hkK
  obtain ⟨w⟩ := pbs_reach_all u k
  obtain ⟨a, b, q, hab, hqA, hbNotA⟩ :=
    rlc_twoChannelFull_walk_first_exit_set A w huA hkNotA
  have haA : a ∈ A := hqA a q.end_mem_support
  obtain ⟨haNotK, hua⟩ := haA
  have hbK : b ∈ K := by
    by_contra hbNotK
    have habK : ((hypercubicLattice 2).induce Kᶜ).Adj
        ⟨a, haNotK⟩ ⟨b, hbNotK⟩ := hab
    exact hbNotA ⟨hbNotK, hua.trans habK.reachable⟩
  have hAinH : A ⊆ H := by
    intro z hzA hzExt
    obtain ⟨hzNotK, huz⟩ := hzA
    obtain ⟨_hzNotK', hzComp⟩ := hzExt
    have huComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
        ⟨u, huK⟩ = rlc_twoChannelFullExteriorComponent gamma gamma' omega :=
      (ConnectedComponent.sound huz).trans hzComp
    exact hu ⟨huK, huComp⟩
  have hqH : ∀ z ∈ q.support, z ∈ H := by
    intro z hz
    exact hAinH (hqA z hz)
  have huaH : ((hypercubicLattice 2).induce H).Reachable
      ⟨u, hu⟩ ⟨a, hAinH ⟨haNotK, hua⟩⟩ := ⟨q.induce H hqH⟩
  have hbH : b ∈ H :=
    rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega hbK
  have habH : ((hypercubicLattice 2).induce H).Adj
      ⟨a, hAinH ⟨haNotK, hua⟩⟩ ⟨b, hbH⟩ := hab
  exact ⟨b, hbK, huaH.trans habH.reachable⟩

theorem rlc_twoChannelFullFilledReachSet_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {u v : Site 2}
    (hu : u ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (hv : v ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
    ((hypercubicLattice 2).induce
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Reachable
        ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨zu, hzu, huz⟩ :=
    rlc_twoChannelFullFilledReachSet_reaches_reachSet gamma gamma' omega hu
  obtain ⟨zv, hzv, hvz⟩ :=
    rlc_twoChannelFullFilledReachSet_reaches_reachSet gamma gamma' omega hv
  have hmiddle := (rlc_twoChannelFullReachSet_reachable
    gamma gamma' omega hzu hzv).map
      ((hypercubicLattice 2).induceHomOfLE
        (rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega)).toHom
  exact huz.trans (hmiddle.trans hvz.symm)

theorem rlc_twoChannelFullFilledReachSet_reachable_in_barrier {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {u v : Site 2}
    (hu : u ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (hv : v ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
    (latticeMinusBarrier
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Reachable u v := by
  let hom : ((hypercubicLattice 2).induce
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)) →g
      latticeMinusBarrier
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega) := {
    toFun z := (z : Site 2)
    map_rel' := by
      intro a b hab
      exact latticeMinusBarrier_adj_of_both_mem _ hab a.2 b.2
  }
  have h := (rlc_twoChannelFullFilledReachSet_reachable
    gamma gamma' omega hu hv).map hom
  simpa [hom] using h

theorem rlc_twoChannelFullExteriorSet_reachable_in_filledBarrier {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {u v : Site 2}
    (hu : u ∈ rlc_twoChannelFullExteriorSet gamma gamma' omega)
    (hv : v ∈ rlc_twoChannelFullExteriorSet gamma gamma' omega) :
    (latticeMinusBarrier
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Reachable u v := by
  let hom : ((hypercubicLattice 2).induce
      (rlc_twoChannelFullExteriorSet gamma gamma' omega)) →g
      latticeMinusBarrier
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega) := {
    toFun z := (z : Site 2)
    map_rel' := by
      intro a b hab
      exact latticeMinusBarrier_adj_of_both_not_mem _ hab
        (by
          simp only [rlc_twoChannelFullFilledReachSet, Set.mem_compl_iff]
          exact not_not_intro a.2)
        (by
          simp only [rlc_twoChannelFullFilledReachSet, Set.mem_compl_iff]
          exact not_not_intro b.2)
  }
  have h := (rlc_twoChannelFullExteriorSet_reachable
    gamma gamma' omega hu hv).map hom
  simpa [hom] using h


theorem rlc_twoChannelFullFilledReachSet_faceBoundaryConnected {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    FaceBoundaryConnected
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)
      (phb_boundarySupport
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)
        (rlc_twoChannelFullFilledReachSet_finite gamma gamma' omega)) := by
  let H := rlc_twoChannelFullFilledReachSet gamma gamma' omega
  let hH := rlc_twoChannelFullFilledReachSet_finite gamma gamma' omega
  let x : Site 2 := gamma.1.1
  have hxK : x ∈ rlc_twoChannelFullReachSet gamma gamma' omega :=
    rlc_rightPathVertex_mem_twoChannelFullReachSet gamma gamma' omega
      (rlc_path_start_mem_vertices gamma.1)
  have hxH : x ∈ H :=
    rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega hxK
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box H hH
  let y : Site 2 := beacon 2 R
  have hyExt : y ∈ exterior 2 R := beacon_mem_exterior R (by norm_num)
  have hyBox : y ∉ box 2 R := by
    simpa [exterior_eq_compl_box] using hyExt
  have hyH : y ∉ H := fun hy => hyBox (hR hy)
  apply faceBoundaryConnected_of_connected_complement H hH hxH hyH
  · intro a b ha hb
    exact rlc_twoChannelFullFilledReachSet_reachable_in_barrier
      gamma gamma' omega ha hb
  · intro a b ha hb
    apply rlc_twoChannelFullExteriorSet_reachable_in_filledBarrier
      gamma gamma' omega
    · simpa [H, rlc_twoChannelFullFilledReachSet] using ha
    · simpa [H, rlc_twoChannelFullFilledReachSet] using hb


theorem rlc_twoChannelFullFilledBoundary_inside_mem_reachSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {p q : Site 2}
    (hp : p ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (hq : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (hpq : (hypercubicLattice 2).Adj p q) :
    p ∈ rlc_twoChannelFullReachSet gamma gamma' omega := by
  let K := rlc_twoChannelFullReachSet gamma gamma' omega
  by_contra hpK
  have hqExt : q ∈ rlc_twoChannelFullExteriorSet gamma gamma' omega := by
    simpa [rlc_twoChannelFullFilledReachSet] using hq
  obtain ⟨hqK, hqComp⟩ := hqExt
  have hpqK : ((hypercubicLattice 2).induce Kᶜ).Adj
      ⟨p, hpK⟩ ⟨q, hqK⟩ := hpq
  have hpComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨p, hpK⟩ = rlc_twoChannelFullExteriorComponent gamma gamma' omega :=
    (ConnectedComponent.sound hpqK.reachable).trans hqComp
  exact hp ⟨hpK, hpComp⟩

theorem rlc_twoChannelFullFilled_edgeBoundary_subset_reachSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {p q : Site 2}
    (hpq : (p, q) ∈ edgeBoundary 2
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)) :
    (p, q) ∈ edgeBoundary 2
      (rlc_twoChannelFullReachSet gamma gamma' omega) := by
  refine ⟨hpq.1, ?_⟩
  by_cases hp : p ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega
  · have hq : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega :=
      hpq.2.mp hp
    have hpK := rlc_twoChannelFullFilledBoundary_inside_mem_reachSet
      gamma gamma' omega hp hq hpq.1
    have hqK : q ∉ rlc_twoChannelFullReachSet gamma gamma' omega := by
      intro hqK
      exact hq (rlc_twoChannelFullReachSet_subset_filled
        gamma gamma' omega hqK)
    exact iff_of_true hpK hqK
  · have hq : q ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega := by
      by_contra hq
      exact hp (hpq.2.mpr hq)
    have hqK := rlc_twoChannelFullFilledBoundary_inside_mem_reachSet
      gamma gamma' omega hq hp hpq.1.symm
    have hpK : p ∉ rlc_twoChannelFullReachSet gamma gamma' omega := by
      intro hpK
      exact hp (rlc_twoChannelFullReachSet_subset_filled
        gamma gamma' omega hpK)
    simp [hpK, hqK]



theorem rlc_twoChannelFullFilledFaceBoundaryGraph_le_reachFaceBoundaryGraph
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega) ≤
      faceBoundaryGraph
        (rlc_twoChannelFullReachSet gamma gamma' omega) := by
  intro f g hfg
  refine ⟨hfg.1, ?_⟩
  obtain ⟨p, q, hpq, hadj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  have hpqFilled : (p, q) ∈ edgeBoundary 2
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega) := by
    refine ⟨hadj, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hfg.2
  have hpqReach :=
    rlc_twoChannelFullFilled_edgeBoundary_subset_reachSet
      gamma gamma' omega hpqFilled
  rw [hpq, bdEdge_mk]
  exact hpqReach.2



theorem rlc_twoChannelFullFilledBoundary_le_openFaceDual {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega) ≤
      openSubgraph 2 (fci_faceDualConfig
        (rlc_twoChannelFullAmbientConfig gamma gamma' omega)) :=
  (rlc_twoChannelFullFilledFaceBoundaryGraph_le_reachFaceBoundaryGraph
    gamma gamma' omega).trans
      (rlc_twoChannelFullBoundary_le_openFaceDual gamma gamma' omega)



theorem rlc_leftPathVertex_mem_twoChannelFullExteriorSet_of_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hposition : RlcBookPositionedTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {z : Site 2} (hzPath : z ∈ rlc_pathVertices gamma'.1) :
    z ∈ rlc_twoChannelFullExteriorSet gamma gamma' omega := by
  classical
  let K := rlc_twoChannelFullReachSet gamma gamma' omega
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box K
    (rlc_twoChannelFullReachSet_finite gamma gamma' omega)
  let a : Site 2 := gamma'.1.1
  have haPath : a ∈ rlc_pathVertices gamma'.1 :=
    rlc_path_start_mem_vertices gamma'.1
  have haNot : a ∈ Kᶜ :=
    rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure
      gamma gamma' omega hno haPath
  have ha0 : a 0 = -2 * n := gamma'.1.1.2.2
  have hn : 0 < n := by
    have hbox := gamma.1.1.2.1
    rw [mem_rect] at hbox
    have hs := hposition.right_axis_strict
    omega
  let c : Int := -2 * n - R - 1
  let q : Site 2 := ![c, a 1]
  have hqExt : q ∈ exterior 2 R := by
    refine ⟨0, ?_⟩
    simp [q, c]
    omega
  have hqNot : q ∈ Kᶜ := exterior_subset_compl K R hR hqExt
  let W := rlc_ambientCrossingWalk gamma'.1
  have hzW : z ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 z).2
      hzPath
  let wTrace : (hypercubicLattice 2).Walk z a :=
    (W.takeUntil z hzW).reverse
  have haEq : a = ![-2 * n, a 1] := by
    ext i
    fin_cases i <;> simp [ha0]
  let wRay : (hypercubicLattice 2).Walk a q :=
    (sw_horizSeg (a 1) (-2 * n) c).copy haEq.symm rfl
  let w := wTrace.append wRay
  have hwNot : ∀ v ∈ w.support, v ∈ Kᶜ := by
    intro v hv
    dsimp only [w] at hv
    rw [SimpleGraph.Walk.mem_support_append_iff] at hv
    rcases hv with hvTrace | hvRay
    · have hvW : v ∈ W.support := by
        dsimp only [wTrace] at hvTrace
        have hvTake : v ∈ (W.takeUntil z hzW).support := by
          simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse]
            using hvTrace
        exact W.support_takeUntil_subset_support hzW hvTake
      have hvPath :=
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
          gamma'.1 v).1 hvW
      exact rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure
        gamma gamma' omega hno hvPath
    · change v ∈ ((sw_horizSeg (a 1) (-2 * n) c).copy _ _).support at hvRay
      rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hvRay
      obtain ⟨t, ht, rfl⟩ := hvRay
      rw [Set.mem_uIcc] at ht
      have htLe : t ≤ -2 * n := by
        rcases ht with ht | ht <;> dsimp only [c] at ht <;> omega
      by_cases hteq : t = -2 * n
      · subst t
        rw [← haEq]
        exact haNot
      · intro htK
        have htRect := rlc_twoChannelFullReachSet_subset_box
          gamma gamma' omega htK
        rw [mem_rect] at htRect
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at htRect
        omega
  have hzNot : z ∈ Kᶜ := hwNot z w.start_mem_support
  have hreach : ((hypercubicLattice 2).induce Kᶜ).Reachable
      ⟨z, hzNot⟩ ⟨q, hqNot⟩ := ⟨w.induce Kᶜ hwNot⟩
  have hqInf : (((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨q, hqNot⟩).supp.Infinite :=
    exterior_mem_infiniteComponent (by norm_num) K R hR hqExt
  have hqComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨q, hqNot⟩ = rlc_twoChannelFullExteriorComponent gamma gamma' omega :=
    (unique_infinite_component (by norm_num) K
      (rlc_twoChannelFullReachSet_finite gamma gamma' omega)).unique
        hqInf (rlc_twoChannelFullExteriorComponent_infinite gamma gamma' omega)
  exact ⟨hzNot, (ConnectedComponent.sound hreach).trans hqComp⟩


def RlcTwoChannelFullFilledBoundaryContacts {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') : Prop :=
  ∃ x y : Site 2,
    x ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support ∧
    y ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support ∧
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
    rlc_dualReflect y ∈ rlc_pathVertices gamma'.1



theorem rlc_twoChannelFullFilledBoundaryContacts_of_faithful_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    RlcTwoChannelFullFilledBoundaryContacts gamma gamma' omega := by
  let H := rlc_twoChannelFullFilledReachSet gamma gamma' omega
  obtain ⟨z, hzRight, hzFlipLeft⟩ :=
    rlc_bookFlippedTraceIntersection_of_faithful gamma gamma' hfaith
  have hrightStartFlip :
      rlc_flipX (gamma.1.1 : Site 2) = (gamma.1.1 : Site 2) :=
    rlc_flipX_eq_self_of_zero gamma.1.1.2.2
  have hrightStartH : rlc_flipX (gamma.1.1 : Site 2) ∈ H := by
    rw [hrightStartFlip]
    exact rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega
      (rlc_rightPathVertex_mem_twoChannelFullReachSet gamma gamma' omega
        (rlc_path_start_mem_vertices gamma.1))
  have hzFlipExt :=
    rlc_leftPathVertex_mem_twoChannelFullExteriorSet_of_failure
      gamma gamma' hfaith.toRlcBookPositionedTracePair omega hno hzFlipLeft
  have hzFlipOut : rlc_flipX z ∉ H := by
    simpa [H, rlc_twoChannelFullFilledReachSet] using hzFlipExt
  obtain ⟨x, hxSupp, hxPath⟩ :=
    rlc_faceBoundary_contact_of_flippedTrace_exit gamma.1 H
      (rlc_path_start_mem_vertices gamma.1) hrightStartH hzRight hzFlipOut
  let u : Site 2 := rlc_flipX z
  have huLeft : u ∈ rlc_pathVertices gamma'.1 := hzFlipLeft
  have huFlipH : rlc_flipX u ∈ H := by
    have huFlip : rlc_flipX u = z := by simp [u]
    rw [huFlip]
    exact rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega
      (rlc_rightPathVertex_mem_twoChannelFullReachSet
        gamma gamma' omega hzRight)
  have hleftEndPath : (gamma'.1.2.1 : Site 2) ∈
      rlc_pathVertices gamma'.1 :=
    rlc_connector_path_end_mem_vertices gamma'.1
  have hleftEndExt :=
    rlc_leftPathVertex_mem_twoChannelFullExteriorSet_of_failure
      gamma gamma' hfaith.toRlcBookPositionedTracePair omega hno hleftEndPath
  have hleftEndFlip :
      rlc_flipX (gamma'.1.2.1 : Site 2) =
        (gamma'.1.2.1 : Site 2) :=
    rlc_flipX_eq_self_of_zero gamma'.1.2.1.2.2
  have hleftEndOut : rlc_flipX (gamma'.1.2.1 : Site 2) ∉ H := by
    rw [hleftEndFlip]
    simpa [H, rlc_twoChannelFullFilledReachSet] using hleftEndExt
  obtain ⟨y, hySupp, hyPath⟩ :=
    rlc_faceBoundary_contact_of_flippedTrace_exit gamma'.1 H
      huLeft huFlipH hleftEndPath hleftEndOut
  exact ⟨x, y, hxSupp, hySupp, hxPath, hyPath⟩



theorem rlc_twoChannelFullFilledFaceBoundary_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {f g : Site 2}
    (hf : f ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
    (hg : g ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support) :
    (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Reachable f g := by
  let H := rlc_twoChannelFullFilledReachSet gamma gamma' omega
  let hH := rlc_twoChannelFullFilledReachSet_finite gamma gamma' omega
  have hconn := rlc_twoChannelFullFilledReachSet_faceBoundaryConnected
    gamma gamma' omega
  rw [FaceBoundaryConnected, SimpleGraph.connected_iff] at hconn
  have hfT : f ∈ phb_boundarySupport H hH := by simpa [H, hH] using hf
  have hgT : g ∈ phb_boundarySupport H hH := by simpa [H, hH] using hg
  have hreach := hconn.1 ⟨f, hfT⟩ ⟨g, hgT⟩
  exact hreach.map (SimpleGraph.Embedding.induce
    (phb_boundarySupport H hH : Set (Site 2))).toHom



theorem rlc_twoChannelFull_reflectedOpenDualWalk_of_faithful_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    ∃ x y : Site 2,
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      Nonempty ((openSubgraph 2 (rlc_dualReflectConfig
        (rlc_twoChannelFullAmbientConfig gamma gamma' omega))).Walk
          (rlc_dualReflect x) (rlc_dualReflect y)) := by
  obtain ⟨x, y, hx, hy, hxPath, hyPath⟩ :=
    rlc_twoChannelFullFilledBoundaryContacts_of_faithful_failure
      gamma gamma' hfaith omega hno
  obtain ⟨a⟩ := rlc_twoChannelFullFilledFaceBoundary_reachable
    gamma gamma' omega hx hy
  let hle := rlc_twoChannelFullFilledBoundary_le_openFaceDual
    gamma gamma' omega
  exact ⟨x, y, hxPath, hyPath,
    ⟨rlc_dualReflectOpenWalk _ (a.mapLe hle)⟩⟩





def rlc_twoChannelFullOuterBox (n : Int) : Set (Site 2) :=
  rect (-2 * n - 1) (2 * n) (-n) (n + 1)

abbrev RlcTwoChannelFullOuterVertex (n : Int) :=
  rlc_twoChannelFullOuterBox n


def rlc_twoChannelFullOuterGraph (n : Int) :
    SimpleGraph (RlcTwoChannelFullOuterVertex n) :=
  (hypercubicLattice 2).induce (rlc_twoChannelFullOuterBox n)

noncomputable instance rlc_twoChannelFullOuterGraphDecidableAdj (n : Int) :
    DecidableRel (rlc_twoChannelFullOuterGraph n).Adj :=
  Classical.decRel _


def rlc_twoChannelFullOuterConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    ConfigSpace (Sym2 (RlcTwoChannelFullOuterVertex n)) :=
  fun e => rlc_dualReflectConfig
    (rlc_twoChannelFullAmbientConfig gamma gamma' omega)
      (e.map Subtype.val)

theorem rlc_openSub_twoChannelFullOuter_eq_induce {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    FK.openSub (rlc_twoChannelFullOuterGraph n)
        (rlc_twoChannelFullOuterConfig gamma gamma' omega) =
      openSubgraphInduce 2
        (rlc_dualReflectConfig
          (rlc_twoChannelFullAmbientConfig gamma gamma' omega))
        (rlc_twoChannelFullOuterBox n) := by
  ext x y
  simp only [FK.openSub_adj, openSubgraphInduce_adj, openSubgraph_adj]
  rfl

def rlc_twoChannelFullOuterOnRight {n : Int}
    (gamma : RlcRightDiagonalPath n)
    (x : RlcTwoChannelFullOuterVertex n) : Prop :=
  (x : Site 2) ∈ rlc_pathVertices gamma.1

def rlc_twoChannelFullOuterOnLeft {n : Int}
    (gamma' : RlcLeftDiagonalPath n)
    (x : RlcTwoChannelFullOuterVertex n) : Prop :=
  (x : Site 2) ∈ rlc_pathVertices gamma'.1


def rlc_twoChannelFullOuterConnectorEvent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (ConfigSpace (Sym2 (RlcTwoChannelFullOuterVertex n))) :=
  {eta | ∃ x y : RlcTwoChannelFullOuterVertex n,
    rlc_twoChannelFullOuterOnRight gamma x ∧
      rlc_twoChannelFullOuterOnLeft gamma' y ∧
      (FK.openSub (rlc_twoChannelFullOuterGraph n) eta).Reachable x y}

theorem rlc_dualReflect_faces_mem_fullOuterBox_of_shared_endpoint {n : Int}
    {f g x : Site 2} (hfg : (hypercubicLattice 2).Adj f g)
    (hx : x ∈ sharedPrimalEdge f g)
    (hxRect : x ∈ rect (-2 * n) (2 * n) (-n) n) :
    rlc_dualReflect f ∈ rlc_twoChannelFullOuterBox n ∧
      rlc_dualReflect g ∈ rlc_twoChannelFullOuterBox n :=
  rlc_reflectedCarrierFaces_mem_crossedBoxInterior hfg hx hxRect



theorem rlc_twoChannelFullFilledBoundary_reflect_mem_outerBox {n : Int}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g) :
    rlc_dualReflect f ∈ rlc_twoChannelFullOuterBox n ∧
      rlc_dualReflect g ∈ rlc_twoChannelFullOuterBox n := by
  obtain ⟨p, q, hpq, hpqAdj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  have hpqBoundary : (p, q) ∈ edgeBoundary 2
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega) := by
    refine ⟨hpqAdj, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hfg.2
  by_cases hp : p ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega
  · have hpRect := rlc_twoChannelFullFilledReachSet_subset_connectorRect
      hn gamma gamma' omega hp
    apply rlc_dualReflect_faces_mem_fullOuterBox_of_shared_endpoint hfg.1
      (x := p) _ hpRect
    rw [hpq]
    exact Sym2.mem_mk_left p q
  · have hq : q ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega := by
      by_contra hq
      exact hp (hpqBoundary.2.mpr hq)
    have hqRect := rlc_twoChannelFullFilledReachSet_subset_connectorRect
      hn gamma gamma' omega hq
    apply rlc_dualReflect_faces_mem_fullOuterBox_of_shared_endpoint hfg.1
      (x := q) _ hqRect
    rw [hpq]
    exact Sym2.mem_mk_right p q



theorem rlc_twoChannelFullFilledBoundaryWalk_reflect_mem_outerBox {n : Int}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {x y z : Site 2}
    (a : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk x y)
    (hy : y ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
    (hz : z ∈ a.support) :
    rlc_dualReflect z ∈ rlc_twoChannelFullOuterBox n := by
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hz
  rcases hz with rfl | ⟨e, he, hze⟩
  · obtain ⟨g, hyg⟩ := hy
    exact (rlc_twoChannelFullFilledBoundary_reflect_mem_outerBox
      hn gamma gamma' omega hyg).1
  · induction e using Sym2.inductionOn with
    | _ u v =>
        have huvAdj := a.adj_of_mem_edges he
        have hb := rlc_twoChannelFullFilledBoundary_reflect_mem_outerBox
          hn gamma gamma' omega huvAdj
        rw [Sym2.mem_iff] at hze
        rcases hze with rfl | rfl
        · exact hb.1
        · exact hb.2



theorem rlc_twoChannelFullOuter_success_of_faithful_failure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    rlc_twoChannelFullOuterConfig gamma gamma' omega ∈
      rlc_twoChannelFullOuterConnectorEvent gamma gamma' := by
  have hn : 0 < n := by
    have hbox := gamma.1.1.2.1
    rw [mem_rect] at hbox
    have hs := hfaith.right_axis_strict
    omega
  obtain ⟨x, y, hx, hy, hxPath, hyPath⟩ :=
    rlc_twoChannelFullFilledBoundaryContacts_of_faithful_failure
      gamma gamma' hfaith omega hno
  obtain ⟨a⟩ := rlc_twoChannelFullFilledFaceBoundary_reachable
    gamma gamma' omega hx hy
  let hle := rlc_twoChannelFullFilledBoundary_le_openFaceDual
    gamma gamma' omega
  let c := rlc_dualReflectOpenWalk
    (rlc_twoChannelFullAmbientConfig gamma gamma' omega) (a.mapLe hle)
  have hcBox : ∀ z ∈ c.support,
      z ∈ rlc_twoChannelFullOuterBox n := by
    intro z hz
    change z ∈ ((a.mapLe hle).map
      (rlc_dualReflectOpenHom
        (rlc_twoChannelFullAmbientConfig gamma gamma' omega))).support at hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨f, hf, rfl⟩ := hz
    exact rlc_twoChannelFullFilledBoundaryWalk_reflect_mem_outerBox
      hn gamma gamma' omega a hy (by
        simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hf)
  let cOuter := c.induce (rlc_twoChannelFullOuterBox n) hcBox
  have hreach : (FK.openSub (rlc_twoChannelFullOuterGraph n)
      (rlc_twoChannelFullOuterConfig gamma gamma' omega)).Reachable
      ⟨rlc_dualReflect x, hcBox _ c.start_mem_support⟩
      ⟨rlc_dualReflect y, hcBox _ c.end_mem_support⟩ := by
    rw [rlc_openSub_twoChannelFullOuter_eq_induce]
    exact ⟨cOuter⟩
  exact ⟨⟨rlc_dualReflect x, hcBox _ c.start_mem_support⟩,
    ⟨rlc_dualReflect y, hcBox _ c.end_mem_support⟩,
    hxPath, hyPath, hreach⟩


theorem rlc_twoChannelReflectedDualEdge_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective (rlc_twoChannelReflectedDualEdge gamma gamma') := by
  intro e f hef
  have hemb := congrArg rlc_pimsEdgeEquiv hef
  simp only [rlc_pimsEdgeEquiv_twoChannelReflectedDualEdge] at hemb
  apply Subtype.ext
  apply Sym2.map.injective Subtype.val_injective
  simpa [Ising.kwg_embeddedEdge,
    rlc_connectorTwoChannelAugmentedPlanarDomain] using hemb




noncomputable def rlc_twoChannelFullVariableGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y := (rlc_connectorTwoChannelGraph gamma gamma').Adj x y ∧
    Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma'
      (rlc_pimsEdgeEquiv (s(x, y).map Subtype.val)))
  symm := by
    rintro x y ⟨hxy, hsource⟩
    refine ⟨hxy.symm, ?_⟩
    simpa [Sym2.eq_swap] using hsource
  loopless := ⟨fun x hxx => hxx.1.ne rfl⟩

noncomputable instance rlc_twoChannelFullVariableGraphDecidableAdj
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_twoChannelFullVariableGraph gamma gamma').Adj :=
  Classical.decRel _




noncomputable def rlc_twoChannelFullExteriorGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y := (rlc_connectorTwoChannelGraph gamma gamma').Adj x y ∧
    ¬Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma'
      (rlc_pimsEdgeEquiv (s(x, y).map Subtype.val))) ∧
    rlc_pimsEdgeEquiv (s(x, y).map Subtype.val) ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
  symm := by
    rintro x y ⟨hxy, hsource, htrace⟩
    refine ⟨hxy.symm, ?_, ?_⟩
    · simpa [Sym2.eq_swap] using hsource
    · simpa [Sym2.eq_swap] using htrace
  loopless := ⟨fun x hxx => hxx.1.ne rfl⟩

noncomputable instance rlc_twoChannelFullExteriorGraphDecidableAdj
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_twoChannelFullExteriorGraph gamma gamma').Adj :=
  Classical.decRel _





theorem rlc_openSub_twoChannelFullDual_eq_variable_sup_exterior {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    FK.openSub (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_twoChannelFullDualConfig gamma gamma' omega) =
      FK.openSub (rlc_twoChannelFullVariableGraph gamma gamma')
          (rlc_twoChannelFullDualConfig gamma gamma' omega) ⊔
        rlc_twoChannelFullExteriorGraph gamma gamma' := by
  classical
  ext x y
  simp only [FK.openSub_adj, SimpleGraph.sup_adj]
  let e : Sym2 (RlcConnectorVertex n) := s(x, y)
  let source := RlcTwoChannelAmbientSourceEdge gamma gamma'
    (rlc_pimsEdgeEquiv (e.map Subtype.val))
  constructor
  · rintro ⟨htarget, hopen⟩
    by_cases hsource : Nonempty source
    · have hs : Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma'
          (rlc_pimsEdgeEquiv (s(x, y).map Subtype.val))) := by
          simpa only [source, e] using hsource
      exact Or.inl ⟨⟨htarget, hs⟩, hopen⟩
    · by_cases htrace : rlc_pimsEdgeEquiv (e.map Subtype.val) ∈
          rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
      · have hclosed := rlc_twoChannelFullDualConfig_of_no_source
          gamma gamma' omega e (by simpa [source] using hsource)
        rw [if_pos htrace] at hclosed
        exact False.elim (by simpa [e, hclosed] using hopen)
      · exact Or.inr ⟨htarget, by simpa [source, e] using hsource,
          by simpa [e] using htrace⟩
  · rintro (hvariable | hexterior)
    · exact ⟨hvariable.1.1, hvariable.2⟩
    · refine ⟨hexterior.1, ?_⟩
      have hopen := rlc_twoChannelFullDualConfig_of_no_source
        gamma gamma' omega e (by simpa [source, e] using hexterior.2.1)
      rw [if_neg hexterior.2.2] at hopen
      simpa [e] using hopen

abbrev RlcTwoChannelFullVariableTargetEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  (rlc_twoChannelFullVariableGraph gamma gamma').edgeSet


theorem rlc_twoChannelFullSourceEdge_exists {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelFullVariableTargetEdge gamma gamma') :
    ∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
      source.1.map Subtype.val =
        rlc_pimsEdgeEquiv (target.1.map Subtype.val) := by
  classical
  induction ht : target.1 using Sym2.inductionOn with
  | _ x y =>
      have hadj := target.2
      rw [ht, SimpleGraph.mem_edgeSet] at hadj
      have hsource : Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma'
          (rlc_pimsEdgeEquiv (s(x, y).map Subtype.val))) := hadj.2
      obtain ⟨source⟩ := hsource
      exact ⟨source.1, by simpa [ht] using source.2⟩


noncomputable def rlc_twoChannelFullSourceEdge {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelFullVariableTargetEdge gamma gamma') :
    (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
  Classical.choose (rlc_twoChannelFullSourceEdge_exists target)

@[simp] theorem rlc_twoChannelFullSourceEdge_map {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelFullVariableTargetEdge gamma gamma') :
    (rlc_twoChannelFullSourceEdge target).1.map Subtype.val =
      rlc_pimsEdgeEquiv (target.1.map Subtype.val) := by
  exact Classical.choose_spec (rlc_twoChannelFullSourceEdge_exists target)

theorem rlc_twoChannelFullSourceEdge_injective {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n} :
    Function.Injective
      (rlc_twoChannelFullSourceEdge (gamma := gamma) (gamma' := gamma')) := by
  intro target target' hsource
  apply Subtype.ext
  apply Sym2.map.injective Subtype.val_injective
  apply rlc_pimsEdgeEquiv.injective
  rw [← rlc_twoChannelFullSourceEdge_map target,
    ← rlc_twoChannelFullSourceEdge_map target', hsource]

abbrev RlcTwoChannelFullVisibleSourceEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  {source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet //
    source ∈ Set.range
      (rlc_twoChannelFullSourceEdge (gamma := gamma) (gamma' := gamma'))}

abbrev RlcTwoChannelFullDiscardedSourceEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  {source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet //
    source ∉ Set.range
      (rlc_twoChannelFullSourceEdge (gamma := gamma) (gamma' := gamma'))}


noncomputable def rlc_twoChannelFullVariableVisibleEquiv {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcTwoChannelFullVariableTargetEdge gamma gamma' ≃
      RlcTwoChannelFullVisibleSourceEdge gamma gamma' :=
  Equiv.ofInjective rlc_twoChannelFullSourceEdge
    rlc_twoChannelFullSourceEdge_injective



theorem rlc_twoChannel_fullDualProjection_and_discardedBits_injective
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective (fun omega : RlcTwoChannelEdgeConfig gamma gamma' =>
      ((fun e : RlcTwoChannelFullVariableTargetEdge gamma gamma' =>
          rlc_twoChannelFullDualConfig gamma gamma' omega e.1),
        fun e : RlcTwoChannelFullDiscardedSourceEdge gamma gamma' =>
          omega e.1)) := by
  intro omega omega' hpair
  have hvisible := congrArg Prod.fst hpair
  have hdiscarded := congrArg Prod.snd hpair
  funext source
  by_cases hrange : source ∈ Set.range
      (rlc_twoChannelFullSourceEdge (gamma := gamma) (gamma' := gamma'))
  · obtain ⟨target, htarget⟩ := hrange
    have hcoord := congrFun hvisible target
    change rlc_twoChannelFullDualConfig gamma gamma' omega target.1 =
      rlc_twoChannelFullDualConfig gamma gamma' omega' target.1 at hcoord
    rw [rlc_twoChannelFullDualConfig_of_source gamma gamma' omega target.1
        source (by rw [← htarget, rlc_twoChannelFullSourceEdge_map]),
      rlc_twoChannelFullDualConfig_of_source gamma gamma' omega' target.1
        source (by rw [← htarget, rlc_twoChannelFullSourceEdge_map])] at hcoord
    exact Bool.not_injective hcoord
  · exact congrFun hdiscarded ⟨source, hrange⟩


noncomputable def rlc_twoChannelFullVariableProjection {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    ConfigSpace (rlc_twoChannelFullVariableGraph gamma gamma').edgeSet :=
  fun e => rlc_twoChannelFullDualConfig gamma gamma' omega e.1



def rlc_twoChannelFullVariableExteriorEvent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (ConfigSpace
      (rlc_twoChannelFullVariableGraph gamma gamma').edgeSet) :=
  {eta | ∃ x y : RlcConnectorVertex n,
    rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
      (FK.openSub (rlc_twoChannelFullVariableGraph gamma gamma')
          (FK.extendActive
            (rlc_twoChannelFullVariableGraph gamma gamma') eta) ⊔
        rlc_twoChannelFullExteriorGraph gamma gamma').Reachable x y}



theorem rlc_twoChannelFullDual_mem_event_iff_variableExterior {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelFullDualConfig gamma gamma' omega ∈
        rlc_finiteTwoChannelConnectorEvent gamma gamma' ↔
      rlc_twoChannelFullVariableProjection gamma gamma' omega ∈
        rlc_twoChannelFullVariableExteriorEvent gamma gamma' := by
  have hvariable : FK.openSub
      (rlc_twoChannelFullVariableGraph gamma gamma')
        (rlc_twoChannelFullDualConfig gamma gamma' omega) =
      FK.openSub (rlc_twoChannelFullVariableGraph gamma gamma')
        (FK.extendActive (rlc_twoChannelFullVariableGraph gamma gamma')
          (rlc_twoChannelFullVariableProjection gamma gamma' omega)) := by
    ext x y
    simp only [FK.openSub_adj]
    constructor <;> rintro ⟨hxy, hopen⟩ <;> refine ⟨hxy, ?_⟩
    · have he : s(x, y) ∈
          (rlc_twoChannelFullVariableGraph gamma gamma').edgeSet := by
          rw [SimpleGraph.mem_edgeSet]
          exact hxy
      simpa [FK.extendActive, rlc_twoChannelFullVariableProjection, he]
        using hopen
    · have he : s(x, y) ∈
          (rlc_twoChannelFullVariableGraph gamma gamma').edgeSet := by
          rw [SimpleGraph.mem_edgeSet]
          exact hxy
      simpa [FK.extendActive, rlc_twoChannelFullVariableProjection, he]
        using hopen
  unfold rlc_finiteTwoChannelConnectorEvent
    rlc_twoChannelFullVariableExteriorEvent
  simp only [Set.mem_setOf_eq]
  rw [rlc_openSub_twoChannelFullDual_eq_variable_sup_exterior,
    hvariable]



abbrev RlcTwoChannelIndexedOuterVertex {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  RlcConnectorVertex n ⊕
    ((Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') × Bool) ⊕
      Ising.kwg_Face
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'))

noncomputable instance rlc_twoChannelIndexedOuterVertexFintype {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Fintype (RlcTwoChannelIndexedOuterVertex gamma gamma') := by
  letI : Fintype (Ising.kwg_Face
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :=
    Fintype.ofFinite _
  infer_instance

noncomputable instance rlc_twoChannelIndexedOuterVertexDecidableEq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableEq (RlcTwoChannelIndexedOuterVertex gamma gamma') :=
  Classical.decEq _

def rlc_twoChannelIndexedOuterTarget {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcConnectorVertex n → RlcTwoChannelIndexedOuterVertex gamma gamma' :=
  Sum.inl

theorem rlc_twoChannelIndexedOuterTarget_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective (rlc_twoChannelIndexedOuterTarget gamma gamma') :=
  Sum.inl_injective

def rlc_twoChannelIndexedOuterPort {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'))
    (side : Bool) : RlcTwoChannelIndexedOuterVertex gamma gamma' :=
  Sum.inr (Sum.inl (f, side))

def rlc_twoChannelIndexedOuterFace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (C : Ising.kwg_Face
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    RlcTwoChannelIndexedOuterVertex gamma gamma' :=
  Sum.inr (Sum.inr C)

def RlcTwoChannelIndexedRetainedEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) : Prop :=
  ∃ e : RlcTwoChannelFullVariableTargetEdge gamma gamma',
    e.1.map Subtype.val = rlc_twoChannelReflectedDualEdge gamma gamma' f

noncomputable instance rlc_twoChannelIndexedRetainedEdgeDecidable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    Decidable (RlcTwoChannelIndexedRetainedEdge gamma gamma' f) :=
  Classical.dec _

noncomputable def rlc_twoChannelIndexedOuterEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma') :=
  if h : RlcTwoChannelIndexedRetainedEdge gamma gamma' f then
    h.choose.1.map (rlc_twoChannelIndexedOuterTarget gamma gamma')
  else
    s(rlc_twoChannelIndexedOuterPort gamma gamma' f false,
      rlc_twoChannelIndexedOuterPort gamma gamma' f true)


noncomputable def rlc_twoChannelIndexedAugmentedEdge {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelFullVariableTargetEdge gamma gamma') :
    Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') :=
  let source := rlc_twoChannelFullSourceEdge target
  ⟨source.1, SimpleGraph.edgeSet_mono le_sup_left source.2⟩

theorem rlc_twoChannelIndexedAugmentedEdge_reflected {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelFullVariableTargetEdge gamma gamma') :
    rlc_twoChannelReflectedDualEdge gamma gamma'
        (rlc_twoChannelIndexedAugmentedEdge target) =
      target.1.map Subtype.val := by
  apply rlc_pimsEdgeEquiv.injective
  rw [rlc_pimsEdgeEquiv_twoChannelReflectedDualEdge]
  change (rlc_twoChannelFullSourceEdge target).1.map Subtype.val =
    rlc_pimsEdgeEquiv (target.1.map Subtype.val)
  exact rlc_twoChannelFullSourceEdge_map target

theorem rlc_twoChannelIndexedOuterEdge_variable {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelFullVariableTargetEdge gamma gamma') :
    rlc_twoChannelIndexedOuterEdge gamma gamma'
        (rlc_twoChannelIndexedAugmentedEdge target) =
      target.1.map (rlc_twoChannelIndexedOuterTarget gamma gamma') := by
  have hret : RlcTwoChannelIndexedRetainedEdge gamma gamma'
      (rlc_twoChannelIndexedAugmentedEdge target) :=
    ⟨target, (rlc_twoChannelIndexedAugmentedEdge_reflected target).symm⟩
  unfold rlc_twoChannelIndexedOuterEdge
  rw [dif_pos hret]
  have hedge : hret.choose.1 = target.1 := by
    apply Sym2.map.injective Subtype.val_injective
    exact hret.choose_spec.trans
      (rlc_twoChannelIndexedAugmentedEdge_reflected target)
  exact congrArg (Sym2.map
    (rlc_twoChannelIndexedOuterTarget gamma gamma')) hedge

theorem rlc_twoChannelIndexedOuterEdge_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective (rlc_twoChannelIndexedOuterEdge gamma gamma') := by
  intro f g hfg
  unfold rlc_twoChannelIndexedOuterEdge at hfg
  split at hfg <;> split at hfg
  · rename_i hf hg
    have hedge : hf.choose.1 = hg.choose.1 := by
      apply Sym2.map.injective
        (rlc_twoChannelIndexedOuterTarget_injective gamma gamma')
      exact hfg
    apply rlc_twoChannelReflectedDualEdge_injective gamma gamma'
    rw [← hf.choose_spec, ← hg.choose_spec, hedge]
  · rename_i hf hg
    revert hfg
    induction hf.choose.1 using Sym2.inductionOn with
    | _ x y =>
        intro hfg
        rw [Sym2.map_mk, Sym2.eq_iff] at hfg
        simp [rlc_twoChannelIndexedOuterTarget,
          rlc_twoChannelIndexedOuterPort] at hfg
  · rename_i hf hg
    revert hfg
    induction hg.choose.1 using Sym2.inductionOn with
    | _ x y =>
        intro hfg
        rw [Sym2.map_mk, Sym2.eq_iff] at hfg
        simp [rlc_twoChannelIndexedOuterTarget,
          rlc_twoChannelIndexedOuterPort] at hfg
  · simpa [rlc_twoChannelIndexedOuterPort, Sym2.eq_iff] using hfg

noncomputable def rlc_twoChannelIndexedFaceProjection {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcTwoChannelIndexedOuterVertex gamma gamma' →
      Ising.kwg_Face
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
  | Sum.inl x => BeffaraDC.pfdFace
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (rlc_dualReflect.symm x.1)
  | Sum.inr (Sum.inl (f, false)) => BeffaraDC.pfdFace
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (Ising.kwg_flankLeft
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') f)
  | Sum.inr (Sum.inl (f, true)) => BeffaraDC.pfdFace
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (Ising.kwg_flankRight
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') f)
  | Sum.inr (Sum.inr C) => C


theorem rlc_twoChannelIndexedFaceProjection_outerEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    (rlc_twoChannelIndexedOuterEdge gamma gamma' f).map
        (rlc_twoChannelIndexedFaceProjection gamma gamma') =
      Ising.kwg_dualEnds
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') f := by
  unfold rlc_twoChannelIndexedOuterEdge
  split
  · rename_i hret
    have hphysical := hret.choose_spec
    have hmapped := congrArg
      (Sym2.map (fun z : Site 2 => BeffaraDC.pfdFace
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
        (rlc_dualReflect.symm z))) hphysical
    simpa [rlc_twoChannelIndexedOuterTarget,
      rlc_twoChannelIndexedFaceProjection,
      rlc_twoChannelReflectedDualEdge, Ising.kwg_dualEnds,
      BeffaraDC.pfdFace, Sym2.map_map] using hmapped
  · simp [rlc_twoChannelIndexedOuterPort,
      rlc_twoChannelIndexedFaceProjection, Ising.kwg_dualEnds,
      BeffaraDC.pfdFace]

def RlcTwoChannelIndexedIsFace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcTwoChannelIndexedOuterVertex gamma gamma' → Prop
  | Sum.inr (Sum.inr _) => True
  | _ => False

noncomputable def rlc_twoChannelIndexedSpokeGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcTwoChannelIndexedOuterVertex gamma gamma') where
  Adj x y := x ≠ y ∧
    rlc_twoChannelIndexedFaceProjection gamma gamma' x =
      rlc_twoChannelIndexedFaceProjection gamma gamma' y ∧
    (RlcTwoChannelIndexedIsFace gamma gamma' x ∨
      RlcTwoChannelIndexedIsFace gamma gamma' y)
  symm := by
    rintro x y ⟨hne, hface, hghost⟩
    exact ⟨hne.symm, hface.symm, hghost.symm⟩
  loopless := ⟨fun x h => h.1 rfl⟩

noncomputable instance rlc_twoChannelIndexedSpokeGraphDecidableAdj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_twoChannelIndexedSpokeGraph gamma gamma').Adj :=
  Classical.decRel _

@[simp] theorem rlc_twoChannelIndexedFaceProjection_face {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (C : Ising.kwg_Face
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    rlc_twoChannelIndexedFaceProjection gamma gamma'
        (rlc_twoChannelIndexedOuterFace gamma gamma' C) = C :=
  rfl



theorem rlc_twoChannelIndexedSpoke_adj_face {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x : RlcTwoChannelIndexedOuterVertex gamma gamma')
    (hx : ¬RlcTwoChannelIndexedIsFace gamma gamma' x) :
    (rlc_twoChannelIndexedSpokeGraph gamma gamma').Adj x
      (rlc_twoChannelIndexedOuterFace gamma gamma'
        (rlc_twoChannelIndexedFaceProjection gamma gamma' x)) := by
  refine ⟨?_, rfl, Or.inr trivial⟩
  intro h
  rw [h] at hx
  exact hx trivial



theorem rlc_twoChannelIndexedFaceProjection_eq_of_spoke {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcTwoChannelIndexedOuterVertex gamma gamma'}
    (hxy : (rlc_twoChannelIndexedSpokeGraph gamma gamma').Adj x y) :
    rlc_twoChannelIndexedFaceProjection gamma gamma' x =
      rlc_twoChannelIndexedFaceProjection gamma gamma' y :=
  hxy.2.1

noncomputable def rlc_twoChannelIndexedRandomGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcTwoChannelIndexedOuterVertex gamma gamma') where
  Adj x y := x ≠ y ∧ ∃ f,
    rlc_twoChannelIndexedOuterEdge gamma gamma' f = s(x, y)
  symm := by
    rintro x y ⟨hne, f, hf⟩
    exact ⟨hne.symm, f, hf.trans Sym2.eq_swap⟩
  loopless := ⟨fun x h => h.1 rfl⟩

noncomputable instance rlc_twoChannelIndexedRandomGraphDecidableAdj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_twoChannelIndexedRandomGraph gamma gamma').Adj :=
  Classical.decRel _

noncomputable def rlc_twoChannelIndexedOuterGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcTwoChannelIndexedOuterVertex gamma gamma') :=
  rlc_twoChannelIndexedRandomGraph gamma gamma' ⊔
    rlc_twoChannelIndexedSpokeGraph gamma gamma'

noncomputable instance rlc_twoChannelIndexedOuterGraphDecidableAdj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_twoChannelIndexedOuterGraph gamma gamma').Adj :=
  Classical.decRel _




noncomputable def rlc_twoChannelIndexedOuterConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    ConfigSpace (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma')) :=
  fun e => if h : ∃ f,
      rlc_twoChannelIndexedOuterEdge gamma gamma' f = e then
    !(rlc_connectorForceTraceConfig gamma gamma'
      (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) h.choose.1)
  else decide
    (e ∈ (rlc_twoChannelIndexedSpokeGraph gamma gamma').edgeSet)

@[simp] theorem rlc_twoChannelIndexedOuterConfig_randomEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    rlc_twoChannelIndexedOuterConfig gamma gamma' omega
        (rlc_twoChannelIndexedOuterEdge gamma gamma' f) =
      !(rlc_connectorForceTraceConfig gamma gamma'
        (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) f.1) := by
  unfold rlc_twoChannelIndexedOuterConfig
  split
  · rename_i h
    have hf : h.choose = f :=
      rlc_twoChannelIndexedOuterEdge_injective gamma gamma' h.choose_spec
    rw [hf]
  · rename_i h
    exact (h ⟨f, rfl⟩).elim


def rlc_twoChannelIndexedFaceTag {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcTwoChannelIndexedOuterVertex gamma gamma' → Bool
  | Sum.inr (Sum.inr _) => true
  | _ => false

@[simp] theorem rlc_twoChannelIndexedFaceTag_eq_true_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x : RlcTwoChannelIndexedOuterVertex gamma gamma') :
    rlc_twoChannelIndexedFaceTag gamma gamma' x = true ↔
      RlcTwoChannelIndexedIsFace gamma gamma' x := by
  rcases x with x | (x | x) <;>
    simp [rlc_twoChannelIndexedFaceTag, RlcTwoChannelIndexedIsFace]

@[simp] theorem rlc_twoChannelIndexedFaceTag_outerEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    (rlc_twoChannelIndexedOuterEdge gamma gamma' f).map
        (rlc_twoChannelIndexedFaceTag gamma gamma') = s(false, false) := by
  unfold rlc_twoChannelIndexedOuterEdge
  split
  · rename_i hret
    induction hret.choose.1 using Sym2.inductionOn with
    | _ x y =>
        simp [rlc_twoChannelIndexedOuterTarget,
          rlc_twoChannelIndexedFaceTag]
  · simp [rlc_twoChannelIndexedOuterPort,
      rlc_twoChannelIndexedFaceTag]

theorem rlc_twoChannelIndexedSpoke_faceTag_ne_false {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcTwoChannelIndexedOuterVertex gamma gamma'}
    (hxy : (rlc_twoChannelIndexedSpokeGraph gamma gamma').Adj x y) :
    s(x, y).map (rlc_twoChannelIndexedFaceTag gamma gamma') ≠
      s(false, false) := by
  intro htag
  rw [Sym2.map_mk, Sym2.eq_iff] at htag
  have hxfalse : rlc_twoChannelIndexedFaceTag gamma gamma' x = false := by
    rcases htag with htag | htag <;> exact htag.1
  have hyfalse : rlc_twoChannelIndexedFaceTag gamma gamma' y = false := by
    rcases htag with htag | htag <;> exact htag.2
  rcases hxy.2.2 with hx | hy
  · have hxtrue := (rlc_twoChannelIndexedFaceTag_eq_true_iff
      gamma gamma' x).2 hx
    simp [hxtrue] at hxfalse
  · have hytrue := (rlc_twoChannelIndexedFaceTag_eq_true_iff
      gamma gamma' y).2 hy
    simp [hytrue] at hyfalse

theorem rlc_twoChannelIndexedOuterEdge_not_mem_spoke {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    rlc_twoChannelIndexedOuterEdge gamma gamma' f ∉
      (rlc_twoChannelIndexedSpokeGraph gamma gamma').edgeSet := by
  induction hxy : rlc_twoChannelIndexedOuterEdge gamma gamma' f using
      Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet]
      intro hspoke
      apply rlc_twoChannelIndexedSpoke_faceTag_ne_false gamma gamma' hspoke
      rw [← hxy]
      exact rlc_twoChannelIndexedFaceTag_outerEdge gamma gamma' f



theorem rlc_twoChannelIndexedOuterConfig_spoke {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {e : Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma')}
    (he : e ∈ (rlc_twoChannelIndexedSpokeGraph gamma gamma').edgeSet) :
    rlc_twoChannelIndexedOuterConfig gamma gamma' omega e = true := by
  unfold rlc_twoChannelIndexedOuterConfig
  split
  · rename_i hrandom
    obtain ⟨f, rfl⟩ := hrandom
    exact (rlc_twoChannelIndexedOuterEdge_not_mem_spoke
      gamma gamma' f he).elim
  · simp [he]

theorem rlc_twoChannelIndexedOuterEdge_ne_diag {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'))
    (x : RlcTwoChannelIndexedOuterVertex gamma gamma') :
    rlc_twoChannelIndexedOuterEdge gamma gamma' f ≠ s(x, x) := by
  unfold rlc_twoChannelIndexedOuterEdge
  split
  · rename_i hf
    have hedge := hf.choose.2
    revert hedge
    induction hf.choose.1 using Sym2.inductionOn with
    | _ u v =>
        intro hedge heq
        rw [SimpleGraph.mem_edgeSet] at hedge
        rw [Sym2.map_mk, Sym2.eq_iff] at heq
        rcases heq with h | h
        · apply hedge.ne
          exact rlc_twoChannelIndexedOuterTarget_injective gamma gamma'
            (h.1.trans h.2.symm)
        · apply hedge.ne
          exact rlc_twoChannelIndexedOuterTarget_injective gamma gamma'
            (h.2.trans h.1.symm).symm
  · intro heq
    rw [Sym2.eq_iff] at heq
    rcases heq with h | h
    · have hbool : false = true := congrArg
          (fun z => match z with
            | Sum.inr (Sum.inl (_, side)) => side
            | _ => false) (h.1.trans h.2.symm)
      simp at hbool
    · have hbool : false = true := congrArg
          (fun z => match z with
            | Sum.inr (Sum.inl (_, side)) => side
            | _ => false) (h.1.trans h.2.symm)
      simp at hbool

theorem rlc_twoChannelIndexedOuterEdge_mem_random {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    rlc_twoChannelIndexedOuterEdge gamma gamma' f ∈
      (rlc_twoChannelIndexedRandomGraph gamma gamma').edgeSet := by
  induction hxy : rlc_twoChannelIndexedOuterEdge gamma gamma' f using
      Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet]
      refine ⟨?_, f, hxy⟩
      intro h
      subst y
      exact rlc_twoChannelIndexedOuterEdge_ne_diag gamma gamma' f x hxy


noncomputable def rlc_twoChannelIndexedOuterOpenGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    SimpleGraph (RlcTwoChannelIndexedOuterVertex gamma gamma') :=
  FK.openSub (rlc_twoChannelIndexedOuterGraph gamma gamma')
    (rlc_twoChannelIndexedOuterConfig gamma gamma' omega)

theorem rlc_twoChannelIndexedSpoke_le_open {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelIndexedSpokeGraph gamma gamma' ≤
      rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega := by
  intro x y hxy
  rw [rlc_twoChannelIndexedOuterOpenGraph, FK.openSub_adj]
  refine ⟨Or.inr hxy, ?_⟩
  exact rlc_twoChannelIndexedOuterConfig_spoke gamma gamma' omega
    ((SimpleGraph.mem_edgeSet _).mpr hxy)



theorem rlc_twoChannelIndexedOuterEdge_open_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    rlc_twoChannelIndexedOuterEdge gamma gamma' f ∈
        (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).edgeSet ↔
      f.1 ∉ (FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))).edgeSet := by
  rw [rlc_twoChannelIndexedOuterOpenGraph]
  induction hxy : rlc_twoChannelIndexedOuterEdge gamma gamma' f using
      Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet, FK.openSub_adj]
      have hrandom :
          (rlc_twoChannelIndexedRandomGraph gamma gamma').Adj x y := by
        rw [← SimpleGraph.mem_edgeSet, ← hxy]
        exact rlc_twoChannelIndexedOuterEdge_mem_random gamma gamma' f
      have hconfig :=
        rlc_twoChannelIndexedOuterConfig_randomEdge gamma gamma' omega f
      rw [hxy] at hconfig
      rw [hconfig]
      constructor
      · rintro ⟨_, hopen⟩ hprimal
        have htrue : rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) f.1 = true := by
          induction hfedge : f.1 using Sym2.inductionOn with
          | _ u v =>
              rw [hfedge] at hprimal
              rw [SimpleGraph.mem_edgeSet, FK.openSub_adj] at hprimal
              simpa [hfedge] using hprimal.2
        rw [htrue] at hopen
        simp at hopen
      · intro hclosed
        refine ⟨Or.inl hrandom, ?_⟩
        have hfalse : rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) f.1 = false := by
          apply Bool.eq_false_of_not_eq_true
          intro hopen
          apply hclosed
          induction hfedge : f.1 using Sym2.inductionOn with
          | _ u v =>
              have hfmem : f.1 ∈
                  (rlc_connectorTwoChannelAugmentedPlanarDomain
                    gamma gamma').G.edgeSet := f.2
              rw [hfedge] at hfmem
              rw [SimpleGraph.mem_edgeSet, FK.openSub_adj]
              exact ⟨(SimpleGraph.mem_edgeSet _).mp hfmem,
                by simpa [hfedge] using hopen⟩
        simp [hfalse]

theorem rlc_twoChannelIndexedOuterEdge_endpoints_not_face {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'))
    {x y : RlcTwoChannelIndexedOuterVertex gamma gamma'}
    (hxy : rlc_twoChannelIndexedOuterEdge gamma gamma' f = s(x, y)) :
    ¬RlcTwoChannelIndexedIsFace gamma gamma' x ∧
      ¬RlcTwoChannelIndexedIsFace gamma gamma' y := by
  have htag := rlc_twoChannelIndexedFaceTag_outerEdge gamma gamma' f
  rw [hxy, Sym2.map_mk, Sym2.eq_iff] at htag
  have hxfalse : rlc_twoChannelIndexedFaceTag gamma gamma' x = false := by
    rcases htag with htag | htag <;> exact htag.1
  have hyfalse : rlc_twoChannelIndexedFaceTag gamma gamma' y = false := by
    rcases htag with htag | htag <;> exact htag.2
  constructor
  · intro hx
    have hxtrue := (rlc_twoChannelIndexedFaceTag_eq_true_iff
      gamma gamma' x).2 hx
    simp [hxtrue] at hxfalse
  · intro hy
    have hytrue := (rlc_twoChannelIndexedFaceTag_eq_true_iff
      gamma gamma' y).2 hy
    simp [hytrue] at hyfalse



theorem rlc_twoChannelIndexedFaceProjection_reachable_of_adj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {x y : RlcTwoChannelIndexedOuterVertex gamma gamma'}
    (hxy : (rlc_twoChannelIndexedOuterOpenGraph
      gamma gamma' omega).Adj x y) :
    (BeffaraDC.pfdClosedDual
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))).Reachable
      (rlc_twoChannelIndexedFaceProjection gamma gamma' x)
      (rlc_twoChannelIndexedFaceProjection gamma gamma' y) := by
  rw [rlc_twoChannelIndexedOuterOpenGraph, FK.openSub_adj] at hxy
  rcases hxy.1 with hrandom | hspoke
  · obtain ⟨f, hf⟩ := hrandom.2
    have hopen : rlc_twoChannelIndexedOuterEdge gamma gamma' f ∈
        (rlc_twoChannelIndexedOuterOpenGraph
          gamma gamma' omega).edgeSet := by
      rw [hf]
      exact (SimpleGraph.mem_edgeSet _).mpr <| by
        rw [rlc_twoChannelIndexedOuterOpenGraph, FK.openSub_adj]
        exact ⟨Or.inl hrandom, hxy.2⟩
    have habsent := (rlc_twoChannelIndexedOuterEdge_open_iff
      gamma gamma' omega f).1 hopen
    have hends : Ising.kwg_dualEnds
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') f =
        s(rlc_twoChannelIndexedFaceProjection gamma gamma' x,
          rlc_twoChannelIndexedFaceProjection gamma gamma' y) := by
      rw [← rlc_twoChannelIndexedFaceProjection_outerEdge
        gamma gamma' f, hf, Sym2.map_mk]
    by_cases heq : rlc_twoChannelIndexedFaceProjection gamma gamma' x =
        rlc_twoChannelIndexedFaceProjection gamma gamma' y
    · rw [heq]
    · exact ((BeffaraDC.pfdClosedDual_adj
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
        (FK.openSub
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))) _ _).2
          ⟨heq, f, habsent, hends⟩).reachable
  · rw [hspoke.2.1]

theorem rlc_twoChannelIndexedFaceProjection_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {x y : RlcTwoChannelIndexedOuterVertex gamma gamma'}
    (hxy : (rlc_twoChannelIndexedOuterOpenGraph
      gamma gamma' omega).Reachable x y) :
    (BeffaraDC.pfdClosedDual
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))).Reachable
      (rlc_twoChannelIndexedFaceProjection gamma gamma' x)
      (rlc_twoChannelIndexedFaceProjection gamma gamma' y) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hxy
  induction hxy with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail hreach hadj ih =>
      exact ih.trans
        (rlc_twoChannelIndexedFaceProjection_reachable_of_adj
          gamma gamma' omega hadj)



theorem rlc_twoChannelIndexedFace_reachable_of_pfd_adj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {C D : Ising.kwg_Face
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')}
    (hCD : (BeffaraDC.pfdClosedDual
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))).Adj C D) :
    (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Reachable
      (rlc_twoChannelIndexedOuterFace gamma gamma' C)
      (rlc_twoChannelIndexedOuterFace gamma gamma' D) := by
  rw [BeffaraDC.pfdClosedDual_adj] at hCD
  obtain ⟨_, f, habsent, hends⟩ := hCD
  have hopen := (rlc_twoChannelIndexedOuterEdge_open_iff
    gamma gamma' omega f).2 habsent
  induction hedge : rlc_twoChannelIndexedOuterEdge gamma gamma' f using
      Sym2.inductionOn with
  | _ x y =>
      have hnonface := rlc_twoChannelIndexedOuterEdge_endpoints_not_face
        gamma gamma' f hedge
      have hxface := (rlc_twoChannelIndexedSpoke_le_open gamma gamma' omega
        (rlc_twoChannelIndexedSpoke_adj_face
          gamma gamma' x hnonface.1)).reachable
      have hyface := (rlc_twoChannelIndexedSpoke_le_open gamma gamma' omega
        (rlc_twoChannelIndexedSpoke_adj_face
          gamma gamma' y hnonface.2)).reachable
      have hxy : (rlc_twoChannelIndexedOuterOpenGraph
          gamma gamma' omega).Adj x y := by
        rw [← SimpleGraph.mem_edgeSet, ← hedge]
        exact hopen
      have hproj :
          s(rlc_twoChannelIndexedFaceProjection gamma gamma' x,
            rlc_twoChannelIndexedFaceProjection gamma gamma' y) = s(C, D) := by
        rw [← hends,
          ← rlc_twoChannelIndexedFaceProjection_outerEdge gamma gamma' f,
          hedge, Sym2.map_mk]
      rw [Sym2.eq_iff] at hproj
      rcases hproj with hproj | hproj
      · simpa [hproj.1, hproj.2] using
          hxface.symm.trans (hxy.reachable.trans hyface)
      · simpa [hproj.1, hproj.2] using
          hyface.symm.trans (hxy.symm.reachable.trans hxface)



theorem rlc_twoChannelIndexedFace_reachable_of_pfd {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {C D : Ising.kwg_Face
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')}
    (hCD : (BeffaraDC.pfdClosedDual
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))).Reachable
            C D) :
    (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Reachable
      (rlc_twoChannelIndexedOuterFace gamma gamma' C)
      (rlc_twoChannelIndexedOuterFace gamma gamma' D) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hCD
  induction hCD with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail hreach hadj ih =>
      exact ih.trans (rlc_twoChannelIndexedFace_reachable_of_pfd_adj
        gamma gamma' omega hadj)


theorem rlc_twoChannelIndexedOuter_reachable_face {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (x : RlcTwoChannelIndexedOuterVertex gamma gamma') :
    (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Reachable x
      (rlc_twoChannelIndexedOuterFace gamma gamma'
        (rlc_twoChannelIndexedFaceProjection gamma gamma' x)) := by
  by_cases hx : RlcTwoChannelIndexedIsFace gamma gamma' x
  · have heq : x = rlc_twoChannelIndexedOuterFace gamma gamma'
        (rlc_twoChannelIndexedFaceProjection gamma gamma' x) := by
      rcases x with x | (x | x)
      · simp [RlcTwoChannelIndexedIsFace] at hx
      · simp [RlcTwoChannelIndexedIsFace] at hx
      · rfl
    rw [heq]
    rw [rlc_twoChannelIndexedFaceProjection_face]
  · exact (rlc_twoChannelIndexedSpoke_le_open gamma gamma' omega
      (rlc_twoChannelIndexedSpoke_adj_face gamma gamma' x hx)).reachable



theorem rlc_twoChannelIndexedOuter_reachable_iff_pfd {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (x y : RlcTwoChannelIndexedOuterVertex gamma gamma') :
    (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Reachable x y ↔
      (BeffaraDC.pfdClosedDual
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
        (FK.openSub
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))).Reachable
        (rlc_twoChannelIndexedFaceProjection gamma gamma' x)
        (rlc_twoChannelIndexedFaceProjection gamma gamma' y) := by
  constructor
  · exact rlc_twoChannelIndexedFaceProjection_reachable
      gamma gamma' omega
  · intro hxy
    exact (rlc_twoChannelIndexedOuter_reachable_face
      gamma gamma' omega x).trans
      ((rlc_twoChannelIndexedFace_reachable_of_pfd
        gamma gamma' omega hxy).trans
        (rlc_twoChannelIndexedOuter_reachable_face
          gamma gamma' omega y).symm)



theorem rlc_twoChannelIndexedOuterTargets_reachable_of_pfd {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (x y : RlcConnectorVertex n)
    (hxy : (BeffaraDC.pfdClosedDual
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))).Reachable
      (BeffaraDC.pfdFace
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
        (rlc_dualReflect.symm x.1))
      (BeffaraDC.pfdFace
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
        (rlc_dualReflect.symm y.1))) :
    (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Reachable
      (rlc_twoChannelIndexedOuterTarget gamma gamma' x)
      (rlc_twoChannelIndexedOuterTarget gamma gamma' y) := by
  exact (rlc_twoChannelIndexedOuter_reachable_face gamma gamma' omega
      (rlc_twoChannelIndexedOuterTarget gamma gamma' x)).trans
    ((rlc_twoChannelIndexedFace_reachable_of_pfd gamma gamma' omega hxy).trans
      (rlc_twoChannelIndexedOuter_reachable_face gamma gamma' omega
        (rlc_twoChannelIndexedOuterTarget gamma gamma' y)).symm)

theorem rlc_twoChannelIndexedOuterConfig_closedSource_randomEdge_iff
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    rlc_twoChannelIndexedOuterConfig gamma gamma' (fun _ => false)
        (rlc_twoChannelIndexedOuterEdge gamma gamma' f) = true ↔
      f.1 ∉ (rlc_connectorTraceWiring gamma gamma').edgeSet := by
  rw [rlc_twoChannelIndexedOuterConfig_randomEdge]
  induction hedge : f.1 using Sym2.inductionOn with
  | _ x y =>
      have hfmem := f.2
      rw [hedge, SimpleGraph.mem_edgeSet] at hfmem
      change (rlc_connectorTwoChannelGraph gamma gamma' ⊔
        rlc_connectorTraceWiring gamma gamma').Adj x y at hfmem
      rcases hfmem with htwo | htrace
      · have hnotTrace : s(x, y) ∉
            (rlc_connectorTraceWiring gamma gamma').edgeFinset := by
          intro hmem
          exact htwo.2 ((SimpleGraph.mem_edgeSet _).mp
            (SimpleGraph.mem_edgeFinset.mp hmem))
        have hforce : rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' (fun _ => false))
            s(x, y) = false := by
          change (if s(x, y) ∈
              (rlc_connectorTraceWiring gamma gamma').edgeFinset then
            true else rlc_twoChannelEdgeConfigExtend gamma gamma'
              (fun _ => false) s(x, y)) = false
          calc
            _ = rlc_twoChannelEdgeConfigExtend gamma gamma'
                (fun _ => false) s(x, y) := if_neg hnotTrace
            _ = false := by
              change (if _ : s(x, y) ∈
                  (rlc_connectorTwoChannelGraph gamma gamma').edgeSet then
                false else false) = false
              split <;> rfl
        have hnotSet : s(x, y) ∉
            (rlc_connectorTraceWiring gamma gamma').edgeSet := by
          intro hmem
          exact htwo.2 ((SimpleGraph.mem_edgeSet _).mp hmem)
        constructor
        · intro _
          exact hnotSet
        · intro _
          calc
            (!(rlc_connectorForceTraceConfig gamma gamma'
                (rlc_twoChannelEdgeConfigExtend gamma gamma'
                  (fun _ => false)) s(x, y))) = (!false) :=
              congrArg Bool.not hforce
            _ = true := rfl
      · have htraceMem : s(x, y) ∈
            (rlc_connectorTraceWiring gamma gamma').edgeFinset :=
          SimpleGraph.mem_edgeFinset.mpr
            ((SimpleGraph.mem_edgeSet _).mpr htrace)
        have hforce : rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' (fun _ => false))
            s(x, y) = true := by
          unfold rlc_connectorForceTraceConfig
          exact if_pos htraceMem
        have hset : s(x, y) ∈
            (rlc_connectorTraceWiring gamma gamma').edgeSet :=
          (SimpleGraph.mem_edgeSet _).mpr htrace
        constructor
        · intro hopen
          have himpossible : (!true) = true :=
            (congrArg Bool.not hforce).symm.trans hopen
          exact Bool.noConfusion himpossible
        · intro hnot
          exact (hnot hset).elim



theorem rlc_twoChannelIndexedOuterConfig_variable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (target : RlcTwoChannelFullVariableTargetEdge gamma gamma') :
    rlc_twoChannelIndexedOuterConfig gamma gamma' omega
        (target.1.map (rlc_twoChannelIndexedOuterTarget gamma gamma')) =
      rlc_twoChannelFullDualConfig gamma gamma' omega target.1 := by
  rw [← rlc_twoChannelIndexedOuterEdge_variable target,
    rlc_twoChannelIndexedOuterConfig_randomEdge,
    ← rlc_twoChannelFullAmbientDual_reflectedEdge gamma gamma' omega
      (rlc_twoChannelIndexedAugmentedEdge target)]
  rw [rlc_twoChannelFullDualConfig]
  change rlc_dualReflectConfig
      (rlc_twoChannelFullAmbientConfig gamma gamma' omega)
        (rlc_twoChannelReflectedDualEdge gamma gamma'
          (rlc_twoChannelIndexedAugmentedEdge target)) =
    rlc_dualReflectConfig
      (rlc_twoChannelFullAmbientConfig gamma gamma' omega)
        (target.1.map Subtype.val)
  rw [rlc_twoChannelIndexedAugmentedEdge_reflected]

theorem rlc_twoChannelIndexedRandomGraph_adj_target {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x y : RlcConnectorVertex n) :
    (rlc_twoChannelIndexedRandomGraph gamma gamma').Adj
        (rlc_twoChannelIndexedOuterTarget gamma gamma' x)
        (rlc_twoChannelIndexedOuterTarget gamma gamma' y) ↔
      (rlc_twoChannelFullVariableGraph gamma gamma').Adj x y := by
  constructor
  · rintro ⟨_, f, hf⟩
    unfold rlc_twoChannelIndexedOuterEdge at hf
    split at hf
    · rename_i hret
      have hedge : hret.choose.1 = s(x, y) := by
        apply Sym2.map.injective
          (rlc_twoChannelIndexedOuterTarget_injective gamma gamma')
        simpa [Sym2.map_mk] using hf
      rw [← SimpleGraph.mem_edgeSet, ← hedge]
      exact hret.choose.2
    · rw [Sym2.eq_iff] at hf
      simp [rlc_twoChannelIndexedOuterTarget,
        rlc_twoChannelIndexedOuterPort] at hf
  · intro hxy
    let target : RlcTwoChannelFullVariableTargetEdge gamma gamma' :=
      ⟨s(x, y), (SimpleGraph.mem_edgeSet _).mpr hxy⟩
    let source := rlc_twoChannelFullSourceEdge target
    let f : Ising.kwg_Edge
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') :=
      ⟨source.1, SimpleGraph.edgeSet_mono le_sup_left source.2⟩
    have hreflected : rlc_twoChannelReflectedDualEdge gamma gamma' f =
        target.1.map Subtype.val := by
      apply rlc_pimsEdgeEquiv.injective
      rw [rlc_pimsEdgeEquiv_twoChannelReflectedDualEdge]
      change (rlc_twoChannelFullSourceEdge target).1.map Subtype.val =
        rlc_pimsEdgeEquiv (target.1.map Subtype.val)
      exact rlc_twoChannelFullSourceEdge_map target
    have hret : RlcTwoChannelIndexedRetainedEdge gamma gamma' f :=
      ⟨target, hreflected.symm⟩
    refine ⟨fun h => hxy.1.ne
      (rlc_twoChannelIndexedOuterTarget_injective gamma gamma' h), f, ?_⟩
    unfold rlc_twoChannelIndexedOuterEdge
    rw [dif_pos hret]
    have hedge : hret.choose.1 = target.1 := by
      apply Sym2.map.injective Subtype.val_injective
      exact hret.choose_spec.trans hreflected
    rw [hedge]
    rfl

theorem rlc_twoChannelIndexedSpokeGraph_not_adj_targets {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x y : RlcConnectorVertex n) :
    ¬(rlc_twoChannelIndexedSpokeGraph gamma gamma').Adj
      (rlc_twoChannelIndexedOuterTarget gamma gamma' x)
      (rlc_twoChannelIndexedOuterTarget gamma gamma' y) := by
  rintro ⟨_, _, hghost⟩
  simp [RlcTwoChannelIndexedIsFace,
    rlc_twoChannelIndexedOuterTarget] at hghost

theorem rlc_twoChannelIndexedOuter_adjMatch {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    FK.ocd_AdjMatch (rlc_twoChannelFullVariableGraph gamma gamma')
      (rlc_twoChannelIndexedOuterGraph gamma gamma')
      (rlc_twoChannelIndexedOuterTarget gamma gamma') := by
  intro x y
  rw [rlc_twoChannelIndexedOuterGraph, SimpleGraph.sup_adj]
  constructor
  · intro hxy
    exact Or.inl
      ((rlc_twoChannelIndexedRandomGraph_adj_target gamma gamma' x y).2 hxy)
  · rintro (hrandom | hspoke)
    · exact (rlc_twoChannelIndexedRandomGraph_adj_target gamma gamma' x y).1
        hrandom
    · exact (rlc_twoChannelIndexedSpokeGraph_not_adj_targets
        gamma gamma' x y hspoke).elim


theorem rlc_twoChannelIndexed_condProb_eq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (psi : ConfigSpace
      (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma')))
    (eta : ConfigSpace
      (Sym2 (RlcConnectorVertex n))) :
    FK.condBcProb (rlc_twoChannelIndexedOuterGraph gamma gamma')
        (Lattice.boundaryCliqueGraph (fun _ => False)) p q
        (FK.ocd_innerEdgeFinset
          (rlc_twoChannelIndexedOuterTarget gamma gamma')) psi
        (FK.ocd_psiExt
          (rlc_twoChannelIndexedOuterTarget gamma gamma') psi eta) =
      FK.bcProb (rlc_twoChannelFullVariableGraph gamma gamma')
        (FK.ocd_inducedWiring
          (rlc_twoChannelIndexedOuterGraph gamma gamma')
          (rlc_twoChannelIndexedOuterTarget gamma gamma')
          (fun _ => False) psi) p q eta := by
  simpa using
    (FK.ocd_condBcProb_psiExt_eq_bcProb
      (Gin := rlc_twoChannelFullVariableGraph gamma gamma')
      (Gout := rlc_twoChannelIndexedOuterGraph gamma gamma')
      (ιV := rlc_twoChannelIndexedOuterTarget gamma gamma')
      (bdryOut := fun _ => False)
      (rlc_twoChannelIndexedOuterTarget_injective gamma gamma')
      (rlc_twoChannelIndexedOuter_adjMatch gamma gamma')
      hp hp1 hq psi eta)

def RlcTwoChannelFullInnerCore {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x : RlcConnectorVertex n) : Prop :=
  x = rlc_connectorRightAnchor gamma ∨
    x = rlc_connectorLeftAnchor gamma' ∨
      x ∈ (rlc_twoChannelFullVariableGraph gamma gamma').support

noncomputable instance rlc_twoChannelFullInnerCoreDecidable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidablePred (RlcTwoChannelFullInnerCore gamma gamma') :=
  Classical.decPred _

abbrev RlcTwoChannelFullInnerVertex {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  {x : RlcConnectorVertex n // RlcTwoChannelFullInnerCore gamma gamma' x}

noncomputable instance rlc_twoChannelFullInnerVertexFintype {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Fintype (RlcTwoChannelFullInnerVertex gamma gamma') :=
  Fintype.ofFinite _

noncomputable instance rlc_twoChannelFullInnerVertexDecidableEq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableEq (RlcTwoChannelFullInnerVertex gamma gamma') :=
  Classical.decEq _

noncomputable def rlc_twoChannelFullInnerGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcTwoChannelFullInnerVertex gamma gamma') :=
  (rlc_twoChannelFullVariableGraph gamma gamma').comap Subtype.val

noncomputable instance rlc_twoChannelFullInnerGraphDecidableAdj {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_twoChannelFullInnerGraph gamma gamma').Adj :=
  Classical.decRel _

theorem rlc_twoChannelFullVariableTargetEdge_inner_exists {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelFullVariableTargetEdge gamma gamma') :
    ∃ e : (rlc_twoChannelFullInnerGraph gamma gamma').edgeSet,
      e.1.map Subtype.val = target.1 := by
  induction ht : target.1 using Sym2.inductionOn with
  | _ x y =>
      have hxy : (rlc_twoChannelFullVariableGraph gamma gamma').Adj x y :=
        (SimpleGraph.mem_edgeSet _).mp (ht ▸ target.2)
      let x' : RlcTwoChannelFullInnerVertex gamma gamma' :=
        ⟨x, Or.inr (Or.inr hxy.mem_support_left)⟩
      let y' : RlcTwoChannelFullInnerVertex gamma gamma' :=
        ⟨y, Or.inr (Or.inr hxy.mem_support_right)⟩
      let e : (rlc_twoChannelFullInnerGraph gamma gamma').edgeSet :=
        ⟨s(x', y'), (SimpleGraph.mem_edgeSet _).mpr hxy⟩
      exact ⟨e, by simp [e, x', y', ht]⟩



noncomputable def rlc_twoChannelFullVariableTargetEdge_inner {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelFullVariableTargetEdge gamma gamma') :
    (rlc_twoChannelFullInnerGraph gamma gamma').edgeSet :=
  Classical.choose (rlc_twoChannelFullVariableTargetEdge_inner_exists target)

@[simp] theorem rlc_twoChannelFullVariableTargetEdge_inner_map {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelFullVariableTargetEdge gamma gamma') :
    (rlc_twoChannelFullVariableTargetEdge_inner target).1.map Subtype.val =
      target.1 :=
  Classical.choose_spec
    (rlc_twoChannelFullVariableTargetEdge_inner_exists target)


noncomputable def rlc_twoChannelFullInnerToVariable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace
      (Sym2 (RlcTwoChannelFullInnerVertex gamma gamma'))) :
    ConfigSpace (rlc_twoChannelFullVariableGraph gamma gamma').edgeSet :=
  fun target => rho (rlc_twoChannelFullVariableTargetEdge_inner target).1

def rlc_twoChannelFullInnerOuterVertex {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcTwoChannelFullInnerVertex gamma gamma' →
      RlcTwoChannelIndexedOuterVertex gamma gamma' :=
  fun x => rlc_twoChannelIndexedOuterTarget gamma gamma' x.1

theorem rlc_twoChannelFullInnerOuterVertex_injective {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Function.Injective
      (rlc_twoChannelFullInnerOuterVertex gamma gamma') := by
  intro x y hxy
  apply Subtype.ext
  exact rlc_twoChannelIndexedOuterTarget_injective gamma gamma' hxy

theorem rlc_twoChannelFullInnerOuter_adjMatch {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    FK.ocd_AdjMatch (rlc_twoChannelFullInnerGraph gamma gamma')
      (rlc_twoChannelIndexedOuterGraph gamma gamma')
      (rlc_twoChannelFullInnerOuterVertex gamma gamma') := by
  intro x y
  exact rlc_twoChannelIndexedOuter_adjMatch gamma gamma' x.1 y.1


theorem rlc_twoChannelIndexedOuterEdge_mem_innerRange_of_retained {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'))
    (hret : RlcTwoChannelIndexedRetainedEdge gamma gamma' f) :
    rlc_twoChannelIndexedOuterEdge gamma gamma' f ∈
      Set.range (FK.ocd_innerEdge
        (rlc_twoChannelFullInnerOuterVertex gamma gamma')) := by
  let target := hret.choose
  induction ht : target.1 using Sym2.inductionOn with
  | _ x y =>
      have hxy : (rlc_twoChannelFullVariableGraph gamma gamma').Adj x y :=
        (SimpleGraph.mem_edgeSet _).mp (ht ▸ target.2)
      let x' : RlcTwoChannelFullInnerVertex gamma gamma' :=
        ⟨x, Or.inr (Or.inr hxy.mem_support_left)⟩
      let y' : RlcTwoChannelFullInnerVertex gamma gamma' :=
        ⟨y, Or.inr (Or.inr hxy.mem_support_right)⟩
      refine ⟨s(x', y'), ?_⟩
      rw [FK.ocd_innerEdge_mk]
      unfold rlc_twoChannelIndexedOuterEdge
      rw [dif_pos hret]
      simp [target, ht, x', y',
        rlc_twoChannelFullInnerOuterVertex,
        rlc_twoChannelIndexedOuterTarget]

theorem rlc_twoChannelIndexedOuterEdge_variable_mem_innerRange {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelFullVariableTargetEdge gamma gamma') :
    rlc_twoChannelIndexedOuterEdge gamma gamma'
        (rlc_twoChannelIndexedAugmentedEdge target) ∈
      Set.range (FK.ocd_innerEdge
        (rlc_twoChannelFullInnerOuterVertex gamma gamma')) := by
  apply rlc_twoChannelIndexedOuterEdge_mem_innerRange_of_retained
  exact ⟨target,
    (rlc_twoChannelIndexedAugmentedEdge_reflected target).symm⟩


noncomputable def rlc_twoChannelFullInnerActiveProjection {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    ConfigSpace (rlc_twoChannelFullInnerGraph gamma gamma').edgeSet :=
  fun e => rlc_twoChannelFullDualConfig gamma gamma' omega
    (e.1.map Subtype.val)



theorem rlc_twoChannelFullIndexed_innerActive_eq_projection {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    FK.restrictActive (rlc_twoChannelFullInnerGraph gamma gamma')
        (FK.ocd_innerRestrict
          (rlc_twoChannelFullInnerOuterVertex gamma gamma')
          (rlc_twoChannelIndexedOuterConfig gamma gamma' omega)) =
      rlc_twoChannelFullInnerActiveProjection gamma gamma' omega := by
  funext e
  unfold FK.restrictActive FK.ocd_innerRestrict
    rlc_twoChannelFullInnerActiveProjection
  rw [FK.ocd_innerEdge]
  have htarget : e.1.map Subtype.val ∈
      (rlc_twoChannelFullVariableGraph gamma gamma').edgeSet := by
    induction he : e.1 using Sym2.inductionOn with
    | _ x y =>
        have hinner : (rlc_twoChannelFullInnerGraph gamma gamma').Adj
            x y := (SimpleGraph.mem_edgeSet _).mp (by
          rw [← he]
          exact e.2)
        rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
        exact hinner
  let target : RlcTwoChannelFullVariableTargetEdge gamma gamma' :=
    ⟨e.1.map Subtype.val, htarget⟩
  have hmap : e.1.map
      (rlc_twoChannelFullInnerOuterVertex gamma gamma') =
      target.1.map (rlc_twoChannelIndexedOuterTarget gamma gamma') := by
    simp [target, rlc_twoChannelFullInnerOuterVertex,
      rlc_twoChannelIndexedOuterTarget, Sym2.map_map]
  rw [hmap]
  exact rlc_twoChannelIndexedOuterConfig_variable
    gamma gamma' omega target



theorem rlc_twoChannelFullInnerToVariable_innerRestrict_eq_projection
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelFullInnerToVariable gamma gamma'
        (FK.ocd_innerRestrict
          (rlc_twoChannelFullInnerOuterVertex gamma gamma')
          (rlc_twoChannelIndexedOuterConfig gamma gamma' omega)) =
      rlc_twoChannelFullVariableProjection gamma gamma' omega := by
  funext target
  have hactive := congrFun
    (rlc_twoChannelFullIndexed_innerActive_eq_projection
      gamma gamma' omega)
    (rlc_twoChannelFullVariableTargetEdge_inner target)
  unfold FK.restrictActive
    rlc_twoChannelFullInnerActiveProjection at hactive
  unfold rlc_twoChannelFullInnerToVariable
    rlc_twoChannelFullVariableProjection at ⊢
  rw [rlc_twoChannelFullVariableTargetEdge_inner_map] at hactive
  exact hactive



def rlc_twoChannelFullInnerExteriorEvent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (ConfigSpace
      (Sym2 (RlcTwoChannelFullInnerVertex gamma gamma'))) :=
  rlc_twoChannelFullInnerToVariable gamma gamma' ⁻¹'
    rlc_twoChannelFullVariableExteriorEvent gamma gamma'

theorem rlc_twoChannelFullVariableExteriorEvent_isIncreasing {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    IsIncreasing
      (rlc_twoChannelFullVariableExteriorEvent gamma gamma') := by
  intro eta eta' heta
  rintro ⟨x, y, hx, hy, hxy⟩
  refine ⟨x, y, hx, hy, hxy.mono ?_⟩
  intro u v huv
  rw [SimpleGraph.sup_adj, FK.openSub_adj] at huv ⊢
  rcases huv with ⟨hvar, hopen⟩ | hext
  · refine Or.inl ⟨hvar, ?_⟩
    have he : s(u, v) ∈
        (rlc_twoChannelFullVariableGraph gamma gamma').edgeSet :=
      (SimpleGraph.mem_edgeSet _).mpr hvar
    have hopen' : eta ⟨s(u, v), he⟩ = true := by
      simpa [FK.extendActive, he] using hopen
    have hopen'' : eta' ⟨s(u, v), he⟩ = true := by
      apply Bool.eq_true_of_not_eq_false
      intro hfalse
      have hle := heta ⟨s(u, v), he⟩
      rw [hopen', hfalse] at hle
      exact (show ¬((true : Bool) ≤ false) by decide) hle
    simpa [FK.extendActive, he] using hopen''
  · exact Or.inr hext

theorem rlc_twoChannelFullInnerExteriorEvent_isIncreasing {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    IsIncreasing (rlc_twoChannelFullInnerExteriorEvent gamma gamma') := by
  intro rho sigma hrs hrho
  exact rlc_twoChannelFullVariableExteriorEvent_isIncreasing gamma gamma'
    (fun target => hrs _)
    hrho



theorem rlc_twoChannelFullIndexed_innerExteriorEvent_iff_fullDual {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    FK.ocd_innerRestrict
          (rlc_twoChannelFullInnerOuterVertex gamma gamma')
          (rlc_twoChannelIndexedOuterConfig gamma gamma' omega) ∈
        rlc_twoChannelFullInnerExteriorEvent gamma gamma' ↔
      rlc_twoChannelFullDualConfig gamma gamma' omega ∈
        rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
  unfold rlc_twoChannelFullInnerExteriorEvent
  change rlc_twoChannelFullInnerToVariable gamma gamma'
        (FK.ocd_innerRestrict
          (rlc_twoChannelFullInnerOuterVertex gamma gamma')
          (rlc_twoChannelIndexedOuterConfig gamma gamma' omega)) ∈
      rlc_twoChannelFullVariableExteriorEvent gamma gamma' ↔ _
  rw [rlc_twoChannelFullInnerToVariable_innerRestrict_eq_projection]
  exact (rlc_twoChannelFullDual_mem_event_iff_variableExterior
    gamma gamma' omega).symm



theorem rlc_twoChannelIndexedOuterConfig_agreesOff_of_discarded {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega omega' : RlcTwoChannelEdgeConfig gamma gamma')
    (hdiscarded : ∀ e : RlcTwoChannelFullDiscardedSourceEdge gamma gamma',
      omega e.1 = omega' e.1) :
    FK.AgreesOff
      (FK.ocd_innerEdgeFinset
        (rlc_twoChannelFullInnerOuterVertex gamma gamma'))
      (rlc_twoChannelIndexedOuterConfig gamma gamma' omega)
      (rlc_twoChannelIndexedOuterConfig gamma gamma' omega') := by
  intro a ha
  have haRange : a ∉ Set.range (FK.ocd_innerEdge
      (rlc_twoChannelFullInnerOuterVertex gamma gamma')) := by
    rwa [FK.ocd_mem_innerEdgeFinset] at ha
  unfold rlc_twoChannelIndexedOuterConfig
  split
  · rename_i hrandom
    let f := hrandom.choose
    induction hedge : f.1 using Sym2.inductionOn with
    | _ x y =>
        have hfmem := f.2
        rw [hedge, SimpleGraph.mem_edgeSet] at hfmem
        change (rlc_connectorTwoChannelGraph gamma gamma' ⊔
          rlc_connectorTraceWiring gamma gamma').Adj x y at hfmem
        rcases hfmem with htwo | htrace
        · let source :
              (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
            ⟨s(x, y), (SimpleGraph.mem_edgeSet _).mpr htwo⟩
          have hnotRange : source ∉ Set.range
              (rlc_twoChannelFullSourceEdge
                (gamma := gamma) (gamma' := gamma')) := by
            rintro ⟨target, htarget⟩
            apply haRange
            have hf : f = rlc_twoChannelIndexedAugmentedEdge target := by
              apply Subtype.ext
              change f.1 = (rlc_twoChannelFullSourceEdge target).1
              exact hedge.trans (congrArg Subtype.val htarget).symm
            rw [← hrandom.choose_spec]
            change rlc_twoChannelIndexedOuterEdge gamma gamma' f ∈
              Set.range (FK.ocd_innerEdge
                (rlc_twoChannelFullInnerOuterVertex gamma gamma'))
            rw [hf]
            exact rlc_twoChannelIndexedOuterEdge_variable_mem_innerRange
              target
          have hnotTrace : s(x, y) ∉
              (rlc_connectorTraceWiring gamma gamma').edgeFinset := by
            intro hmem
            exact htwo.2 ((SimpleGraph.mem_edgeSet _).mp
              (SimpleGraph.mem_edgeFinset.mp hmem))
          have hforce (rho : RlcTwoChannelEdgeConfig gamma gamma') :
              rlc_connectorForceTraceConfig gamma gamma'
                  (rlc_twoChannelEdgeConfigExtend gamma gamma' rho) f.1 =
                rho source := by
            unfold rlc_connectorForceTraceConfig
            rw [if_neg (hedge ▸ hnotTrace)]
            rw [hedge]
            change (if h : s(x, y) ∈
                (rlc_connectorTwoChannelGraph gamma gamma').edgeSet then
              rho ⟨s(x, y), h⟩ else false) = rho source
            have hs : s(x, y) ∈
                (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
              (SimpleGraph.mem_edgeSet _).mpr htwo
            rw [dif_pos hs]
          have hforce' (rho : RlcTwoChannelEdgeConfig gamma gamma') :
              rlc_connectorForceTraceConfig gamma gamma'
                  (rlc_twoChannelEdgeConfigExtend gamma gamma' rho)
                  s(x, y) = rho source := by
            simpa [hedge] using hforce rho
          apply congrArg Bool.not
          exact (hforce' omega').trans <|
            (hdiscarded ⟨source, hnotRange⟩).symm.trans
              (hforce' omega).symm
        · have htraceMem : s(x, y) ∈
              (rlc_connectorTraceWiring gamma gamma').edgeFinset :=
            SimpleGraph.mem_edgeFinset.mpr
              ((SimpleGraph.mem_edgeSet _).mpr htrace)
          have hforce (rho : RlcTwoChannelEdgeConfig gamma gamma') :
              rlc_connectorForceTraceConfig gamma gamma'
                (rlc_twoChannelEdgeConfigExtend gamma gamma' rho)
                s(x, y) = true := by
            unfold rlc_connectorForceTraceConfig
            exact if_pos htraceMem
          apply congrArg Bool.not
          exact (hforce omega').trans (hforce omega).symm
  · rfl




noncomputable def rlc_twoChannelFullIndexedOuterState {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    ConfigSpace (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma')) :=
  FK.ocd_outProj (rlc_twoChannelFullInnerOuterVertex gamma gamma')
    (rlc_twoChannelIndexedOuterConfig gamma gamma' omega)



def RlcTwoChannelFullIndexedFibreSupported {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace
      (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma'))) : Prop :=
  ∃ omega : RlcTwoChannelEdgeConfig gamma gamma',
    psi = rlc_twoChannelFullIndexedOuterState gamma gamma' omega

theorem rlc_twoChannelFullIndexedOuterState_supported {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    RlcTwoChannelFullIndexedFibreSupported gamma gamma'
      (rlc_twoChannelFullIndexedOuterState gamma gamma' omega) :=
  ⟨omega, rfl⟩

theorem rlc_twoChannelFullIndexedOuterState_fixed {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    FK.ocd_outProj (rlc_twoChannelFullInnerOuterVertex gamma gamma')
        (rlc_twoChannelFullIndexedOuterState gamma gamma' omega) =
      rlc_twoChannelFullIndexedOuterState gamma gamma' omega := by
  exact FK.ocd_outProj_idem
    (rlc_twoChannelFullInnerOuterVertex_injective gamma gamma') _


theorem rlc_twoChannelFullIndexedOuterState_eq_of_discarded {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega omega' : RlcTwoChannelEdgeConfig gamma gamma')
    (hdiscarded : ∀ e : RlcTwoChannelFullDiscardedSourceEdge gamma gamma',
      omega e.1 = omega' e.1) :
    rlc_twoChannelFullIndexedOuterState gamma gamma' omega =
      rlc_twoChannelFullIndexedOuterState gamma gamma' omega' := by
  have hagree := rlc_twoChannelIndexedOuterConfig_agreesOff_of_discarded
    gamma gamma' omega omega' hdiscarded
  funext a
  by_cases ha : a ∈ Set.range (FK.ocd_innerEdge
      (rlc_twoChannelFullInnerOuterVertex gamma gamma'))
  · rw [rlc_twoChannelFullIndexedOuterState,
      rlc_twoChannelFullIndexedOuterState,
      FK.ocd_outProj_eq_false_of_range
        (rlc_twoChannelFullInnerOuterVertex_injective gamma gamma') _ ha,
      FK.ocd_outProj_eq_false_of_range
        (rlc_twoChannelFullInnerOuterVertex_injective gamma gamma') _ ha]
  · rw [rlc_twoChannelFullIndexedOuterState,
      rlc_twoChannelFullIndexedOuterState,
      FK.ocd_outProj_eq_of_not_range _ ha,
      FK.ocd_outProj_eq_of_not_range _ ha]
    exact (hagree a (by
      rw [FK.ocd_mem_innerEdgeFinset]
      exact ha)).symm



noncomputable def rlc_twoChannelFullIndexedOuterMaxState {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    ConfigSpace (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma')) :=
  rlc_twoChannelFullIndexedOuterState gamma gamma' (fun _ => false)

theorem rlc_twoChannelIndexedOuterConfig_le_closedSource {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelIndexedOuterConfig gamma gamma' omega ≤
      rlc_twoChannelIndexedOuterConfig gamma gamma' (fun _ => false) := by
  intro a
  unfold rlc_twoChannelIndexedOuterConfig
  split
  · rename_i hrandom
    let f := hrandom.choose
    induction hedge : f.1 using Sym2.inductionOn with
    | _ x y =>
        have hfmem := f.2
        rw [hedge, SimpleGraph.mem_edgeSet] at hfmem
        change (rlc_connectorTwoChannelGraph gamma gamma' ⊔
          rlc_connectorTraceWiring gamma gamma').Adj x y at hfmem
        rcases hfmem with htwo | htrace
        · let source :
              (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
            ⟨s(x, y), (SimpleGraph.mem_edgeSet _).mpr htwo⟩
          have hnotTrace : s(x, y) ∉
              (rlc_connectorTraceWiring gamma gamma').edgeFinset := by
            intro hmem
            exact htwo.2 ((SimpleGraph.mem_edgeSet _).mp
              (SimpleGraph.mem_edgeFinset.mp hmem))
          have hforce (rho : RlcTwoChannelEdgeConfig gamma gamma') :
              rlc_connectorForceTraceConfig gamma gamma'
                  (rlc_twoChannelEdgeConfigExtend gamma gamma' rho)
                  s(x, y) = rho source := by
            change (if s(x, y) ∈
                (rlc_connectorTraceWiring gamma gamma').edgeFinset then
              true else rlc_twoChannelEdgeConfigExtend gamma gamma' rho
                s(x, y)) = rho source
            calc
              _ = rlc_twoChannelEdgeConfigExtend gamma gamma' rho
                    s(x, y) := if_neg hnotTrace
              _ = rho source := by
                change (if h : s(x, y) ∈
                    (rlc_connectorTwoChannelGraph gamma gamma').edgeSet then
                  rho ⟨s(x, y), h⟩ else false) = rho source
                have hs : s(x, y) ∈
                    (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
                  (SimpleGraph.mem_edgeSet _).mpr htwo
                rw [dif_pos hs]
          calc
            (!(rlc_connectorForceTraceConfig gamma gamma'
                (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)
                s(x, y))) = (!(omega source)) :=
              congrArg Bool.not (hforce omega)
            _ ≤ (!false) := Bool.le_true _
            _ ≤ (!(rlc_connectorForceTraceConfig gamma gamma'
                (rlc_twoChannelEdgeConfigExtend gamma gamma' (fun _ => false))
                s(x, y))) := (congrArg Bool.not
              (hforce (fun _ => false)).symm).le
        · have htraceMem : s(x, y) ∈
              (rlc_connectorTraceWiring gamma gamma').edgeFinset :=
            SimpleGraph.mem_edgeFinset.mpr
              ((SimpleGraph.mem_edgeSet _).mpr htrace)
          have hforce (rho : RlcTwoChannelEdgeConfig gamma gamma') :
              rlc_connectorForceTraceConfig gamma gamma'
                  (rlc_twoChannelEdgeConfigExtend gamma gamma' rho)
                  s(x, y) =
                true := by
            unfold rlc_connectorForceTraceConfig
            exact if_pos htraceMem
          calc
            (!(rlc_connectorForceTraceConfig gamma gamma'
                (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)
                s(x, y))) = (!true) := congrArg Bool.not (hforce omega)
            _ ≤ (!(rlc_connectorForceTraceConfig gamma gamma'
                (rlc_twoChannelEdgeConfigExtend gamma gamma' (fun _ => false))
                s(x, y))) := (congrArg Bool.not
              (hforce (fun _ => false)).symm).le
  · exact le_rfl

theorem rlc_twoChannelFullIndexedOuterState_le_max {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelFullIndexedOuterState gamma gamma' omega ≤
      rlc_twoChannelFullIndexedOuterMaxState gamma gamma' := by
  intro a
  by_cases ha : a ∈ Set.range (FK.ocd_innerEdge
      (rlc_twoChannelFullInnerOuterVertex gamma gamma'))
  · rw [rlc_twoChannelFullIndexedOuterState,
      rlc_twoChannelFullIndexedOuterMaxState,
      rlc_twoChannelFullIndexedOuterState,
      FK.ocd_outProj_eq_false_of_range
        (rlc_twoChannelFullInnerOuterVertex_injective gamma gamma') _ ha,
      FK.ocd_outProj_eq_false_of_range
        (rlc_twoChannelFullInnerOuterVertex_injective gamma gamma') _ ha]
  · rw [rlc_twoChannelFullIndexedOuterState,
      rlc_twoChannelFullIndexedOuterMaxState,
      rlc_twoChannelFullIndexedOuterState,
      FK.ocd_outProj_eq_of_not_range _ ha,
      FK.ocd_outProj_eq_of_not_range _ ha]
    exact rlc_twoChannelIndexedOuterConfig_le_closedSource
      gamma gamma' omega a



theorem rlc_twoChannelFullIndexedOuterState_reconstruct {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    FK.ocd_psiExt (rlc_twoChannelFullInnerOuterVertex gamma gamma')
        (rlc_twoChannelFullIndexedOuterState gamma gamma' omega)
        (FK.ocd_innerRestrict
          (rlc_twoChannelFullInnerOuterVertex gamma gamma')
          (rlc_twoChannelIndexedOuterConfig gamma gamma' omega)) =
      rlc_twoChannelIndexedOuterConfig gamma gamma' omega := by
  apply FK.ocd_psiExt_innerRestrict_of_agreesOff
    (rlc_twoChannelFullInnerOuterVertex_injective gamma gamma')
  intro a ha
  rw [FK.ocd_mem_innerEdgeFinset] at ha
  exact (FK.ocd_outProj_eq_of_not_range
    (rlc_twoChannelIndexedOuterConfig gamma gamma' omega) ha).symm

noncomputable def rlc_twoChannelFullInnerMergedWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcTwoChannelFullInnerVertex gamma gamma') :=
  (rlc_connectorMergedWiring gamma gamma').comap Subtype.val

noncomputable instance rlc_twoChannelFullInnerMergedWiringDecidableAdj
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_twoChannelFullInnerMergedWiring gamma gamma').Adj :=
  Classical.decRel _

noncomputable def rlc_twoChannelFullInnerInducedWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace
      (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma'))) :
    SimpleGraph (RlcTwoChannelFullInnerVertex gamma gamma') :=
  FK.ocd_inducedWiring (rlc_twoChannelIndexedOuterGraph gamma gamma')
    (rlc_twoChannelFullInnerOuterVertex gamma gamma')
    (fun _ => False) psi

noncomputable instance rlc_twoChannelFullInnerInducedWiringDecidableAdj
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace
      (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma'))) :
    DecidableRel
      (rlc_twoChannelFullInnerInducedWiring gamma gamma' psi).Adj :=
  Classical.decRel _


noncomputable def rlc_twoChannelFullInnerMaxSupportedWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcTwoChannelFullInnerVertex gamma gamma') :=
  rlc_twoChannelFullInnerInducedWiring gamma gamma'
    (rlc_twoChannelFullIndexedOuterMaxState gamma gamma')

noncomputable instance rlc_twoChannelFullInnerMaxSupportedWiringDecidableAdj
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel
      (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma').Adj :=
  Classical.decRel _

theorem rlc_twoChannelFullInnerInducedWiring_mono {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {psi phi : ConfigSpace
      (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma'))}
    (hpsi : psi ≤ phi) :
    rlc_twoChannelFullInnerInducedWiring gamma gamma' psi ≤
      rlc_twoChannelFullInnerInducedWiring gamma gamma' phi := by
  intro x y hxy
  refine ⟨hxy.1, hxy.2.mono ?_⟩
  intro u v huv
  rw [FK.ocd_outsideGraph_adj] at huv ⊢
  rcases huv with hopen | hboundary
  · exact Or.inl ⟨hopen.1, hpsi _ hopen.2.1, hopen.2.2⟩
  · exact Or.inr hboundary



theorem rlc_twoChannelFullInnerInducedWiring_le_maxSupported {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelFullInnerInducedWiring gamma gamma'
        (rlc_twoChannelFullIndexedOuterState gamma gamma' omega) ≤
      rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma' := by
  exact rlc_twoChannelFullInnerInducedWiring_mono gamma gamma'
    (rlc_twoChannelFullIndexedOuterState_le_max gamma gamma' omega)



noncomputable def rlc_twoChannelFullMaxOutsideGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcTwoChannelIndexedOuterVertex gamma gamma') :=
  FK.ocd_outsideGraph (rlc_twoChannelIndexedOuterGraph gamma gamma')
    (rlc_twoChannelFullInnerOuterVertex gamma gamma')
    (fun _ => False) (rlc_twoChannelFullIndexedOuterMaxState gamma gamma')

abbrev RlcTwoChannelFullMaxOutsideComponent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  (rlc_twoChannelFullMaxOutsideGraph gamma gamma').ConnectedComponent


noncomputable def rlc_twoChannelFullMaxOuterContraction {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcTwoChannelIndexedOuterVertex gamma gamma' →
      RlcTwoChannelFullMaxOutsideComponent gamma gamma' :=
  (rlc_twoChannelFullMaxOutsideGraph gamma gamma').connectedComponentMk

noncomputable def rlc_twoChannelFullMaxInnerContraction {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcTwoChannelFullInnerVertex gamma gamma' →
      RlcTwoChannelFullMaxOutsideComponent gamma gamma' :=
  fun x => rlc_twoChannelFullMaxOuterContraction gamma gamma'
    (rlc_twoChannelFullInnerOuterVertex gamma gamma' x)

theorem rlc_twoChannelFullMaxOuterContraction_eq_of_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcTwoChannelIndexedOuterVertex gamma gamma'}
    (hxy : (rlc_twoChannelFullMaxOutsideGraph gamma gamma').Reachable x y) :
    rlc_twoChannelFullMaxOuterContraction gamma gamma' x =
      rlc_twoChannelFullMaxOuterContraction gamma gamma' y :=
  ConnectedComponent.sound hxy

theorem rlc_twoChannelFullMaxInnerContraction_eq_of_maxWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcTwoChannelFullInnerVertex gamma gamma'}
    (hxy : (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma').Adj x y) :
    rlc_twoChannelFullMaxInnerContraction gamma gamma' x =
      rlc_twoChannelFullMaxInnerContraction gamma gamma' y := by
  exact rlc_twoChannelFullMaxOuterContraction_eq_of_reachable
    gamma gamma' hxy.2

def rlc_twoChannelFullRightInnerAnchor {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcTwoChannelFullInnerVertex gamma gamma' :=
  ⟨rlc_connectorRightAnchor gamma, Or.inl rfl⟩




noncomputable def rlc_twoChannelFullMaxComponentTraceRep {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcTwoChannelFullMaxOutsideComponent gamma gamma' →
      RlcConnectorVertex n := by
  classical
  exact fun C => if C = rlc_twoChannelFullMaxInnerContraction gamma gamma'
        (rlc_twoChannelFullRightInnerAnchor gamma gamma') then
      rlc_connectorRightAnchor gamma
    else rlc_connectorLeftAnchor gamma'

theorem rlc_twoChannelFullMaxComponentTraceRep_onEither {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (C : RlcTwoChannelFullMaxOutsideComponent gamma gamma') :
    rlc_connectorOnEither gamma gamma'
      (rlc_twoChannelFullMaxComponentTraceRep gamma gamma' C) := by
  classical
  unfold rlc_twoChannelFullMaxComponentTraceRep
  split
  · exact Or.inl (rlc_connectorRightAnchor_onRight gamma)
  · exact Or.inr (rlc_connectorLeftAnchor_onLeft gamma')

theorem rlc_twoChannelFullMaxComponentTraceRep_eq_or_mergedClique_adj
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (C D : RlcTwoChannelFullMaxOutsideComponent gamma gamma') :
    rlc_twoChannelFullMaxComponentTraceRep gamma gamma' C =
        rlc_twoChannelFullMaxComponentTraceRep gamma gamma' D ∨
      (rlc_connectorMergedClique gamma gamma').Adj
        (rlc_twoChannelFullMaxComponentTraceRep gamma gamma' C)
        (rlc_twoChannelFullMaxComponentTraceRep gamma gamma' D) := by
  by_cases hCD : rlc_twoChannelFullMaxComponentTraceRep gamma gamma' C =
      rlc_twoChannelFullMaxComponentTraceRep gamma gamma' D
  · exact Or.inl hCD
  · right
    rw [rlc_connectorMergedClique,
      Lattice.boundaryCliqueGraph_adj]
    exact ⟨hCD,
      rlc_twoChannelFullMaxComponentTraceRep_onEither gamma gamma' C,
      rlc_twoChannelFullMaxComponentTraceRep_onEither gamma gamma' D⟩



theorem rlc_twoChannelFullMaxWiring_traceRep_eq_or_mergedClique_adj
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcTwoChannelFullInnerVertex gamma gamma'}
    (hxy : (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma').Adj x y) :
    rlc_twoChannelFullMaxComponentTraceRep gamma gamma'
          (rlc_twoChannelFullMaxInnerContraction gamma gamma' x) =
        rlc_twoChannelFullMaxComponentTraceRep gamma gamma'
          (rlc_twoChannelFullMaxInnerContraction gamma gamma' y) ∨
      (rlc_connectorMergedClique gamma gamma').Adj
        (rlc_twoChannelFullMaxComponentTraceRep gamma gamma'
          (rlc_twoChannelFullMaxInnerContraction gamma gamma' x))
        (rlc_twoChannelFullMaxComponentTraceRep gamma gamma'
          (rlc_twoChannelFullMaxInnerContraction gamma gamma' y)) := by
  exact Or.inl (congrArg
    (rlc_twoChannelFullMaxComponentTraceRep gamma gamma')
    (rlc_twoChannelFullMaxInnerContraction_eq_of_maxWiring
      gamma gamma' hxy))

noncomputable def rlc_twoChannelFullMaxInnerTraceRep {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcTwoChannelFullInnerVertex gamma gamma' → RlcConnectorVertex n :=
  fun x => rlc_twoChannelFullMaxComponentTraceRep gamma gamma'
    (rlc_twoChannelFullMaxInnerContraction gamma gamma' x)

theorem rlc_twoChannelFullMaxInnerTraceRep_onEither {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x : RlcTwoChannelFullInnerVertex gamma gamma') :
    rlc_connectorOnEither gamma gamma'
      (rlc_twoChannelFullMaxInnerTraceRep gamma gamma' x) :=
  rlc_twoChannelFullMaxComponentTraceRep_onEither gamma gamma' _

theorem rlc_twoChannelFullMaxInnerContraction_eq_of_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcTwoChannelFullInnerVertex gamma gamma'}
    (hxy : (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma').Reachable
      x y) :
    rlc_twoChannelFullMaxInnerContraction gamma gamma' x =
      rlc_twoChannelFullMaxInnerContraction gamma gamma' y := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => rfl
  | cons huv p ih =>
      exact (rlc_twoChannelFullMaxInnerContraction_eq_of_maxWiring
        gamma gamma' huv).trans ih

theorem rlc_twoChannelFullMaxInnerTraceRep_eq_of_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcTwoChannelFullInnerVertex gamma gamma'}
    (hxy : (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma').Reachable
      x y) :
    rlc_twoChannelFullMaxInnerTraceRep gamma gamma' x =
      rlc_twoChannelFullMaxInnerTraceRep gamma gamma' y :=
  congrArg (rlc_twoChannelFullMaxComponentTraceRep gamma gamma')
    (rlc_twoChannelFullMaxInnerContraction_eq_of_reachable
      gamma gamma' hxy)



noncomputable def rlc_twoChannelFullMaxTraceKernelWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcTwoChannelFullInnerVertex gamma gamma') where
  Adj x y := x ≠ y ∧
    rlc_twoChannelFullMaxInnerTraceRep gamma gamma' x =
      rlc_twoChannelFullMaxInnerTraceRep gamma gamma' y
  symm := by
    rintro x y ⟨hne, hrep⟩
    exact ⟨hne.symm, hrep.symm⟩
  loopless := ⟨fun x h => h.1 rfl⟩

noncomputable instance rlc_twoChannelFullMaxTraceKernelWiringDecidableAdj
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel
      (rlc_twoChannelFullMaxTraceKernelWiring gamma gamma').Adj :=
  Classical.decRel _

theorem rlc_twoChannelFullInnerMaxSupportedWiring_le_traceKernel {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma' ≤
      rlc_twoChannelFullMaxTraceKernelWiring gamma gamma' := by
  intro x y hxy
  exact ⟨hxy.1, congrArg
    (rlc_twoChannelFullMaxComponentTraceRep gamma gamma')
    (rlc_twoChannelFullMaxInnerContraction_eq_of_maxWiring
      gamma gamma' hxy)⟩


theorem rlc_twoChannelFullIndexed_innerEvent_eq_induced {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (psi : ConfigSpace
      (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma')))
    (A : Set (ConfigSpace
      (Sym2 (RlcTwoChannelFullInnerVertex gamma gamma')))) :
    (∑ rho,
        (FK.ocd_innerRestrict
          (rlc_twoChannelFullInnerOuterVertex gamma gamma') ⁻¹' A).indicator
            (fun _ => (1 : Real)) rho *
          FK.condBcProb (rlc_twoChannelIndexedOuterGraph gamma gamma')
            (Lattice.boundaryCliqueGraph (fun _ => False)) p q
            (FK.ocd_innerEdgeFinset
              (rlc_twoChannelFullInnerOuterVertex gamma gamma')) psi rho) =
      ∑ eta,
        A.indicator (fun _ => (1 : Real)) eta *
          FK.bcProb (rlc_twoChannelFullInnerGraph gamma gamma')
            (rlc_twoChannelFullInnerInducedWiring gamma gamma' psi)
            p q eta := by
  rw [FK.ocd_condBcProb_psiExt_sum_eq_inducedBox
    (rlc_twoChannelFullInnerOuterVertex_injective gamma gamma')
    (rlc_twoChannelFullInnerOuter_adjMatch gamma gamma')
    hp hp1 hq psi
    (FK.ocd_innerRestrict
      (rlc_twoChannelFullInnerOuterVertex gamma gamma') ⁻¹' A)]
  have hpre : FK.ocd_psiExt
      (rlc_twoChannelFullInnerOuterVertex gamma gamma') psi ⁻¹'
      (FK.ocd_innerRestrict
        (rlc_twoChannelFullInnerOuterVertex gamma gamma') ⁻¹' A) = A := by
    ext eta
    simp only [Set.mem_preimage,
      FK.ocd_innerRestrict_psiExt
        (rlc_twoChannelFullInnerOuterVertex_injective gamma gamma')]
  rw [hpre]
  rfl



theorem rlc_twoChannelFullIndexed_actualInnerEvent_le_maxSupported
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (A : Set (ConfigSpace
      (Sym2 (RlcTwoChannelFullInnerVertex gamma gamma'))))
    (hA : IsIncreasing A) :
    (∑ rho,
        (FK.ocd_innerRestrict
          (rlc_twoChannelFullInnerOuterVertex gamma gamma') ⁻¹' A).indicator
            (fun _ => (1 : Real)) rho *
          FK.condBcProb (rlc_twoChannelIndexedOuterGraph gamma gamma')
            (Lattice.boundaryCliqueGraph (fun _ => False)) p q
            (FK.ocd_innerEdgeFinset
              (rlc_twoChannelFullInnerOuterVertex gamma gamma'))
            (rlc_twoChannelFullIndexedOuterState gamma gamma' omega) rho) ≤
      FK.bcEventMass (rlc_twoChannelFullInnerGraph gamma gamma')
        (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma') p q A := by
  rw [rlc_twoChannelFullIndexed_innerEvent_eq_induced
    gamma gamma' hp hp1 (zero_lt_one.trans_le hq)
      (rlc_twoChannelFullIndexedOuterState gamma gamma' omega) A]
  exact FK.bcProb_mono_bc (rlc_twoChannelFullInnerGraph gamma gamma')
    (rlc_twoChannelFullInnerInducedWiring gamma gamma'
      (rlc_twoChannelFullIndexedOuterState gamma gamma' omega))
    (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma')
    (rlc_twoChannelFullInnerInducedWiring_le_maxSupported
      gamma gamma' omega) hp hp1 hq hA



noncomputable def rlc_twoChannelFullIndexed_actualConnectorFibreMass
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) (p q : Real)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') : Real :=
  ∑ rho,
    (FK.ocd_innerRestrict
      (rlc_twoChannelFullInnerOuterVertex gamma gamma') ⁻¹'
        rlc_twoChannelFullInnerExteriorEvent gamma gamma').indicator
          (fun _ => (1 : Real)) rho *
      FK.condBcProb (rlc_twoChannelIndexedOuterGraph gamma gamma')
        (Lattice.boundaryCliqueGraph (fun _ => False)) p q
        (FK.ocd_innerEdgeFinset
          (rlc_twoChannelFullInnerOuterVertex gamma gamma'))
        (rlc_twoChannelFullIndexedOuterState gamma gamma' omega) rho

theorem rlc_twoChannelFullIndexed_actualConnectorFibreMass_le_maxSupported
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelFullIndexed_actualConnectorFibreMass
        gamma gamma' p q omega ≤
      FK.bcEventMass (rlc_twoChannelFullInnerGraph gamma gamma')
        (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma') p q
        (rlc_twoChannelFullInnerExteriorEvent gamma gamma') := by
  unfold rlc_twoChannelFullIndexed_actualConnectorFibreMass
  exact rlc_twoChannelFullIndexed_actualInnerEvent_le_maxSupported
    gamma gamma' hp hp1 hq omega
    (rlc_twoChannelFullInnerExteriorEvent gamma gamma')
    (rlc_twoChannelFullInnerExteriorEvent_isIncreasing gamma gamma')



theorem rlc_twoChannelFullIndexed_actualConnectorMixture_le_maxSupported
    {n : Int} {I : Type*} [Fintype I] [DecidableEq I]
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (weight : I → Real) (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
    (omega : I → RlcTwoChannelEdgeConfig gamma gamma') :
    (∑ i, weight i *
      rlc_twoChannelFullIndexed_actualConnectorFibreMass
        gamma gamma' p q (omega i)) ≤
      FK.bcEventMass (rlc_twoChannelFullInnerGraph gamma gamma')
        (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma') p q
        (rlc_twoChannelFullInnerExteriorEvent gamma gamma') := by
  let target := FK.bcEventMass
    (rlc_twoChannelFullInnerGraph gamma gamma')
    (rlc_twoChannelFullInnerMaxSupportedWiring gamma gamma') p q
    (rlc_twoChannelFullInnerExteriorEvent gamma gamma')
  calc
    (∑ i, weight i *
      rlc_twoChannelFullIndexed_actualConnectorFibreMass
        gamma gamma' p q (omega i)) ≤
        ∑ i, weight i * target := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (rlc_twoChannelFullIndexed_actualConnectorFibreMass_le_maxSupported
          gamma gamma' hp hp1 hq (omega i)) (hweight i)
    _ = target := by rw [← Finset.sum_mul, hweightSum, one_mul]




theorem rlc_twoChannelFullIndexed_innerEvent_le_merged {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (psi : ConfigSpace
      (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma')))
    (hwire : rlc_twoChannelFullInnerInducedWiring gamma gamma' psi ≤
      rlc_twoChannelFullInnerMergedWiring gamma gamma')
    (A : Set (ConfigSpace
      (Sym2 (RlcTwoChannelFullInnerVertex gamma gamma'))))
    (hA : IsIncreasing A) :
    (∑ rho,
        (FK.ocd_innerRestrict
          (rlc_twoChannelFullInnerOuterVertex gamma gamma') ⁻¹' A).indicator
            (fun _ => (1 : Real)) rho *
          FK.condBcProb (rlc_twoChannelIndexedOuterGraph gamma gamma')
            (Lattice.boundaryCliqueGraph (fun _ => False)) p q
            (FK.ocd_innerEdgeFinset
              (rlc_twoChannelFullInnerOuterVertex gamma gamma')) psi rho) ≤
      FK.bcEventMass (rlc_twoChannelFullInnerGraph gamma gamma')
        (rlc_twoChannelFullInnerMergedWiring gamma gamma') p q A := by
  rw [rlc_twoChannelFullIndexed_innerEvent_eq_induced
    gamma gamma' hp hp1 (zero_lt_one.trans_le hq) psi A]
  exact FK.bcProb_mono_bc (rlc_twoChannelFullInnerGraph gamma gamma')
    (rlc_twoChannelFullInnerInducedWiring gamma gamma' psi)
    (rlc_twoChannelFullInnerMergedWiring gamma gamma')
    hwire hp hp1 hq hA



theorem rlc_twoChannelFullIndexed_innerEvent_half_q_one_eq_merged {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (psi : ConfigSpace
      (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma')))
    (A : Set (ConfigSpace
      (Sym2 (RlcTwoChannelFullInnerVertex gamma gamma')))) :
    (∑ rho,
        (FK.ocd_innerRestrict
          (rlc_twoChannelFullInnerOuterVertex gamma gamma') ⁻¹' A).indicator
            (fun _ => (1 : Real)) rho *
          FK.condBcProb (rlc_twoChannelIndexedOuterGraph gamma gamma')
            (Lattice.boundaryCliqueGraph (fun _ => False)) (1 / 2) 1
            (FK.ocd_innerEdgeFinset
              (rlc_twoChannelFullInnerOuterVertex gamma gamma')) psi rho) =
      FK.bcEventMass (rlc_twoChannelFullInnerGraph gamma gamma')
        (rlc_twoChannelFullInnerMergedWiring gamma gamma')
        (1 / 2) 1 A := by
  rw [rlc_twoChannelFullIndexed_innerEvent_eq_induced
    gamma gamma' (by norm_num) (by norm_num) (by norm_num) psi A]
  unfold FK.bcEventMass
  apply Finset.sum_congr rfl
  intro eta _
  congr 1
  exact rlc_bcProb_half_q_one_uniform
    (rlc_twoChannelFullInnerGraph gamma gamma')
    (rlc_twoChannelFullInnerInducedWiring gamma gamma' psi)
    (rlc_twoChannelFullInnerMergedWiring gamma gamma') eta eta



theorem rlc_twoChannelFullIndexed_fibreMixture_half_q_one_eq_merged
    {n : Int} {I : Type*} [Fintype I] [DecidableEq I]
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (weight : I → Real)
    (psi : I → ConfigSpace
      (Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma')))
    (hweight : ∑ i, weight i = 1)
    (A : Set (ConfigSpace
      (Sym2 (RlcTwoChannelFullInnerVertex gamma gamma')))) :
    (∑ i, weight i *
      (∑ rho,
        (FK.ocd_innerRestrict
          (rlc_twoChannelFullInnerOuterVertex gamma gamma') ⁻¹' A).indicator
            (fun _ => (1 : Real)) rho *
          FK.condBcProb (rlc_twoChannelIndexedOuterGraph gamma gamma')
            (Lattice.boundaryCliqueGraph (fun _ => False)) (1 / 2) 1
            (FK.ocd_innerEdgeFinset
              (rlc_twoChannelFullInnerOuterVertex gamma gamma'))
            (psi i) rho)) =
      FK.bcEventMass (rlc_twoChannelFullInnerGraph gamma gamma')
        (rlc_twoChannelFullInnerMergedWiring gamma gamma')
        (1 / 2) 1 A := by
  simp_rw [rlc_twoChannelFullIndexed_innerEvent_half_q_one_eq_merged
    gamma gamma' _ A]
  rw [← Finset.sum_mul, hweight, one_mul]



abbrev RlcTwoChannelFaithfulFace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  Ising.kwg_Face
    (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')

abbrev RlcTwoChannelFaithfulSourceEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  (rlc_connectorTwoChannelGraph gamma gamma').edgeSet

noncomputable instance rlc_twoChannelFaithfulFaceFintype {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Fintype (RlcTwoChannelFaithfulFace gamma gamma') :=
  Fintype.ofFinite _

noncomputable instance rlc_twoChannelFaithfulFaceDecidableEq {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidableEq (RlcTwoChannelFaithfulFace gamma gamma') :=
  Classical.decEq _

def rlc_twoChannelFaithfulAugmentedEdge {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (e : RlcTwoChannelFaithfulSourceEdge gamma gamma') :
    Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') :=
  ⟨e.1, SimpleGraph.edgeSet_mono le_sup_left e.2⟩



noncomputable def rlc_twoChannelFaithfulEnds {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcTwoChannelFaithfulSourceEdge gamma gamma' →
      Sym2 (RlcTwoChannelFaithfulFace gamma gamma') :=
  fun e => Ising.kwg_dualEnds
    (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
    (rlc_twoChannelFaithfulAugmentedEdge e)

def rlc_twoChannelFaithfulDualConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    ConfigSpace (RlcTwoChannelFaithfulSourceEdge gamma gamma') :=
  fun e => !(omega e)

theorem rlc_twoChannelForceTrace_sourceEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (e : RlcTwoChannelFaithfulSourceEdge gamma gamma') :
    rlc_connectorForceTraceConfig gamma gamma'
        (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)
        (rlc_twoChannelFaithfulAugmentedEdge e).1 = omega e := by
  induction he : e.1 using Sym2.inductionOn with
  | _ x y =>
      have htwo : (rlc_connectorTwoChannelGraph gamma gamma').Adj x y :=
        (SimpleGraph.mem_edgeSet _).mp (he ▸ e.2)
      have hnotTrace : s(x, y) ∉
          (rlc_connectorTraceWiring gamma gamma').edgeFinset := by
        intro hmem
        exact htwo.2 ((SimpleGraph.mem_edgeSet _).mp
          (SimpleGraph.mem_edgeFinset.mp hmem))
      change rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) e.1 = omega e
      rw [he]
      change (if s(x, y) ∈
          (rlc_connectorTraceWiring gamma gamma').edgeFinset then true
        else rlc_twoChannelEdgeConfigExtend gamma gamma' omega s(x, y)) =
          omega e
      calc
        _ = rlc_twoChannelEdgeConfigExtend gamma gamma' omega s(x, y) :=
          if_neg hnotTrace
        _ = omega e := by
          change (if h : s(x, y) ∈
              (rlc_connectorTwoChannelGraph gamma gamma').edgeSet then
            omega ⟨s(x, y), h⟩ else false) = omega e
          have hs : s(x, y) ∈
              (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
            (SimpleGraph.mem_edgeSet _).mpr htwo
          rw [dif_pos hs]
          congr 1
          exact Subtype.ext he.symm

theorem rlc_twoChannelFaithfulDualConfig_open_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (e : RlcTwoChannelFaithfulSourceEdge gamma gamma') :
    rlc_twoChannelFaithfulDualConfig gamma gamma' omega e = true ↔
      (rlc_twoChannelFaithfulAugmentedEdge e).1 ∉
        (FK.openSub
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))).edgeSet := by
  have h := rlc_twoChannelFullAmbientDual_reflectedEdge_open_iff
    gamma gamma' omega (rlc_twoChannelFaithfulAugmentedEdge e)
  rw [rlc_twoChannelFullAmbientDual_reflectedEdge,
    rlc_twoChannelForceTrace_sourceEdge] at h
  exact h



theorem rlc_twoChannelFaithful_indexedOpenGraph_eq_pfdClosedDual {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    FK.indexedOpenGraph (rlc_twoChannelFaithfulEnds gamma gamma')
        (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) =
      BeffaraDC.pfdClosedDual
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
        (FK.openSub
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))) := by
  ext C D
  simp only [FK.indexedOpenGraph, SimpleGraph.fromEdgeSet_adj,
    Set.mem_setOf_eq, BeffaraDC.pfdClosedDual_adj]
  constructor
  · rintro ⟨⟨e, hends, hopen⟩, hne⟩
    exact ⟨hne, rlc_twoChannelFaithfulAugmentedEdge e,
      (rlc_twoChannelFaithfulDualConfig_open_iff
        gamma gamma' omega e).mp hopen, hends⟩
  · rintro ⟨hne, f, hfclosed, hends⟩
    induction hedge : f.1 using Sym2.inductionOn with
    | _ x y =>
        have hfmem := f.2
        rw [hedge, SimpleGraph.mem_edgeSet] at hfmem
        change (rlc_connectorTwoChannelGraph gamma gamma' ⊔
          rlc_connectorTraceWiring gamma gamma').Adj x y at hfmem
        rcases hfmem with htwo | htrace
        · let e : RlcTwoChannelFaithfulSourceEdge gamma gamma' :=
            ⟨s(x, y), (SimpleGraph.mem_edgeSet _).mpr htwo⟩
          have hf : rlc_twoChannelFaithfulAugmentedEdge e = f := by
            apply Subtype.ext
            exact hedge.symm
          refine ⟨⟨e, ?_, ?_⟩, hne⟩
          · change Ising.kwg_dualEnds
                (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
                (rlc_twoChannelFaithfulAugmentedEdge e) = s(C, D)
            rw [hf]
            exact hends
          · apply (rlc_twoChannelFaithfulDualConfig_open_iff
              gamma gamma' omega e).mpr
            simpa [hf] using hfclosed
        · exfalso
          apply hfclosed
          rw [hedge, SimpleGraph.mem_edgeSet, FK.openSub_adj]
          refine ⟨Or.inr htrace, ?_⟩
          have hmem : s(x, y) ∈
              (rlc_connectorTraceWiring gamma gamma').edgeFinset :=
            SimpleGraph.mem_edgeFinset.mpr
              ((SimpleGraph.mem_edgeSet _).mpr htrace)
          change rlc_connectorForceTraceConfig gamma gamma'
              (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)
              s(x, y) = true
          exact if_pos hmem



theorem rlc_twoChannelFullFaceDual_le_pfdRegion {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    openSubgraph 2 (fci_faceDualConfig
        (rlc_twoChannelFullAmbientConfig gamma gamma' omega)) ≤
      whb_faceRegion (jei_pushGraph
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
        (FK.openSub
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))) := by
  classical
  intro f g hfg
  have hface : (fci_faceOpenDual
      (rlc_twoChannelFullAmbientConfig gamma gamma' omega)).Adj f g := by
    rw [fci_faceOpenDual_eq_openSubgraph]
    exact hfg
  rw [fci_faceOpenDual_adj] at hface
  rw [whb_faceRegion_adj]
  refine ⟨hface.1, ?_⟩
  intro hmem
  induction hshared : sharedPrimalEdge f g using Sym2.inductionOn with
  | _ a b =>
      rw [hshared, SimpleGraph.mem_edgeSet, jei_pushGraph_adj] at hmem
      obtain ⟨x, y, hxy, hx, hy⟩ := hmem
      rw [FK.openSub_adj] at hxy
      let e : Ising.kwg_Edge
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') :=
        ⟨s(x, y), (SimpleGraph.mem_edgeSet _).mpr hxy.1⟩
      have hemb : Ising.kwg_embeddedEdge
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') e =
          sharedPrimalEdge f g := by
        rw [hshared, Ising.kwg_embeddedEdge, Sym2.map_mk]
        rw [hx, hy]
      have hopen := rlc_twoChannelFullAmbientConfig_embeddedEdge
        gamma gamma' omega e
      rw [hemb] at hopen
      have hamb : rlc_twoChannelFullAmbientConfig gamma gamma' omega
          (sharedPrimalEdge f g) = true := hopen.trans hxy.2
      rw [hamb] at hface
      exact Bool.noConfusion hface.2



theorem rlc_twoChannelFullFaceDual_eq_pfdRegion {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    openSubgraph 2 (fci_faceDualConfig
        (rlc_twoChannelFullAmbientConfig gamma gamma' omega)) =
      whb_faceRegion (jei_pushGraph
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
        (FK.openSub
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))) := by
  apply le_antisymm
  · exact rlc_twoChannelFullFaceDual_le_pfdRegion gamma gamma' omega
  · classical
    intro f g hfg
    rw [whb_faceRegion_adj] at hfg
    rw [← fci_faceOpenDual_eq_openSubgraph, fci_faceOpenDual_adj]
    refine ⟨hfg.1, Bool.eq_false_of_not_eq_true ?_⟩
    intro hopen
    have hplanar := rlc_twoChannelFullAmbientConfig_open_mem_planarEdges
      gamma gamma' omega hopen
    induction hshared : sharedPrimalEdge f g using Sym2.inductionOn with
    | _ a b =>
        have haBox := rlc_connectorCentralFacePlanarEdge_endpoints_mem_box
          gamma gamma' hplanar (hshared ▸ Sym2.mem_mk_left a b)
        have hbBox := rlc_connectorCentralFacePlanarEdge_endpoints_mem_box
          gamma gamma' hplanar (hshared ▸ Sym2.mem_mk_right a b)
        let x : RlcConnectorVertex n := ⟨a, by
          simpa [RlcConnectorVertex, rlc_connectorBox] using haBox⟩
        let y : RlcConnectorVertex n := ⟨b, by
          simpa [RlcConnectorVertex, rlc_connectorBox] using hbBox⟩
        obtain ⟨p, q, hpq, hpqAdj⟩ :=
          sharedPrimalEdge_isLatticeEdge hfg.1
        have habPair : s(a, b) = s(p, q) := hshared.symm.trans hpq
        rw [Sym2.eq_iff] at habPair
        have hab : (hypercubicLattice 2).Adj a b := by
          rcases habPair with habPair | habPair
          · simpa [habPair.1, habPair.2] using hpqAdj
          · simpa [habPair.1, habPair.2] using hpqAdj.symm
        have hcarrier :
            (rlc_connectorTwoChannelAugmentedPlanarDomain
              gamma gamma').G.Adj x y := by
          rw [rlc_connectorTwoChannelAugmentedGraph_eq_closure]
          exact ⟨hab, by simpa [x, y, hshared] using hplanar⟩
        let e : Ising.kwg_Edge
            (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') :=
          ⟨s(x, y), (SimpleGraph.mem_edgeSet _).mpr hcarrier⟩
        have hemb : Ising.kwg_embeddedEdge
            (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') e =
              sharedPrimalEdge f g := by
          rw [hshared, Ising.kwg_embeddedEdge, Sym2.map_mk]
          rfl
        have hedge := rlc_twoChannelFullAmbientConfig_embeddedEdge
          gamma gamma' omega e
        rw [hemb, hopen] at hedge
        have hK : (FK.openSub
            (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
            (rlc_connectorForceTraceConfig gamma gamma'
              (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))).Adj x y :=
          ⟨hcarrier, by simpa [e] using hedge.symm⟩
        apply hfg.2
        rw [hshared, SimpleGraph.mem_edgeSet, jei_pushGraph_adj]
        exact ⟨x, y, hK, rfl, rfl⟩



theorem rlc_twoChannelFaithful_indexedNumClusters_eq_pfd {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    FK.indexedNumClustersBC (rlc_twoChannelFaithfulEnds gamma gamma') ⊥
        (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) =
      Nat.card (BeffaraDC.pfdClosedDual
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
        (FK.openSub
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))).ConnectedComponent := by
  unfold FK.indexedNumClustersBC
  rw [sup_bot_eq,
    rlc_twoChannelFaithful_indexedOpenGraph_eq_pfdClosedDual]




theorem rlc_twoChannelFaithful_indexedEdgeProduct_eq_source {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p : Real) (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    FK.edgeProduct (rlc_connectorTwoChannelGraph gamma gamma') (1 - p)
        (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) =
      FK.indexedEdgeProduct p
        (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) := by
  classical
  unfold FK.edgeProduct FK.indexedEdgeProduct
  rw [← Finset.prod_attach
    (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset,
    Finset.attach_eq_univ]
  let edgeEquiv :
      (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset ≃
        RlcTwoChannelFaithfulSourceEdge gamma gamma' :=
    { toFun := fun e => ⟨e.1, by
          simpa only [SimpleGraph.mem_edgeFinset] using e.2⟩
      invFun := fun e => ⟨e.1, by
          simpa only [SimpleGraph.mem_edgeFinset] using e.2⟩
      left_inv := by intro e; rfl
      right_inv := by intro e; rfl }
  apply Fintype.prod_equiv edgeEquiv
  intro e
  have hext : rlc_twoChannelEdgeConfigExtend gamma gamma' omega e.1 =
      omega (edgeEquiv e) := by
    change rlc_twoChannelEdgeConfigCombine gamma gamma' omega
        (fun _ => false) e.1 = omega (edgeEquiv e)
    exact rlc_twoChannelEdgeConfigCombine_edge gamma gamma' omega
      (fun _ => false) (edgeEquiv e)
  rw [hext]
  cases h : omega (edgeEquiv e) <;>
    simp [h, rlc_twoChannelFaithfulDualConfig]



theorem rlc_twoChannelFaithful_pfdDualEdgeFactor_eq_indexed {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p : Real) (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'
    let forced := rlc_connectorForceTraceConfig gamma gamma'
      (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)
    BeffaraDC.edgeProductCount p P.G.edgeFinset.card
        (P.G.edgeFinset.card -
          (FK.openSub P.G forced).edgeSet.ncard) =
      (1 - p) ^
          (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        FK.indexedEdgeProduct p
          (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) := by
  dsimp only
  let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'
  let forced := rlc_connectorForceTraceConfig gamma gamma'
    (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)
  calc
    BeffaraDC.edgeProductCount p P.G.edgeFinset.card
        (P.G.edgeFinset.card -
          (FK.openSub P.G forced).edgeSet.ncard) =
      BeffaraDC.edgeProductCount p P.G.edgeFinset.card
        (FK.openCount P.G (fun e => !(forced e))) := by
          rw [rlc_openCount_complement,
            BeffaraDC.pfd_openSub_edge_ncard]
    _ = FK.edgeProduct P.G p (fun e => !(forced e)) :=
      (BeffaraDC.dlt_edgeProduct_eq_count P.G p
        (fun e => !(forced e))).symm
    _ = FK.edgeProduct P.G (1 - p) forced := by
      unfold FK.edgeProduct
      apply Finset.prod_congr rfl
      intro e _
      cases h : forced e <;> simp [h]
    _ = (1 - p) ^
          (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        FK.edgeProduct (rlc_connectorTwoChannelGraph gamma gamma') (1 - p)
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) := by
      exact rlc_twoChannel_edgeProduct_augmented_forceTrace
        gamma gamma' (1 - p)
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)
    _ = (1 - p) ^
          (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        FK.indexedEdgeProduct p
          (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) := by
      rw [rlc_twoChannelFaithful_indexedEdgeProduct_eq_source]



theorem rlc_twoChannelFaithful_pfdDualWeight_eq_indexed {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    BeffaraDC.pfdDualWeight
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') p q
        (FK.openSub
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))) =
      (1 - p) ^
          (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        FK.indexedBcWeight (rlc_twoChannelFaithfulEnds gamma gamma') ⊥ p q
          (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) := by
  unfold BeffaraDC.pfdDualWeight FK.indexedBcWeight
  rw [rlc_twoChannelFaithful_pfdDualEdgeFactor_eq_indexed,
    rlc_twoChannelFaithful_indexedNumClusters_eq_pfd]
  ring



def rlc_twoChannelFaithfulDualEquiv {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    RlcTwoChannelEdgeConfig gamma gamma' ≃
      RlcTwoChannelEdgeConfig gamma gamma' where
  toFun := rlc_twoChannelFaithfulDualConfig gamma gamma'
  invFun := rlc_twoChannelFaithfulDualConfig gamma gamma'
  left_inv omega := by
    funext e
    simp [rlc_twoChannelFaithfulDualConfig]
  right_inv omega := by
    funext e
    simp [rlc_twoChannelFaithfulDualConfig]

@[simp] theorem rlc_twoChannelFaithfulDualEquiv_apply {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelFaithfulDualEquiv gamma gamma' omega =
      rlc_twoChannelFaithfulDualConfig gamma gamma' omega := rfl



noncomputable def rlc_twoChannelFaithfulForcedDualEdgeZ {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) : Real :=
  ∑ omega : RlcTwoChannelEdgeConfig gamma gamma',
    BeffaraDC.pfdDualWeight
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') p q
      (FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))


theorem rlc_twoChannelFaithfulForcedDualEdgeZ_eq_indexed {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) :
    rlc_twoChannelFaithfulForcedDualEdgeZ gamma gamma' p q =
      (1 - p) ^
          (rlc_connectorTraceWiring gamma gamma').edgeFinset.card *
        FK.indexedBcZ (rlc_twoChannelFaithfulEnds gamma gamma') ⊥ p q := by
  unfold rlc_twoChannelFaithfulForcedDualEdgeZ FK.indexedBcZ
  simp_rw [rlc_twoChannelFaithful_pfdDualWeight_eq_indexed]
  rw [← Finset.mul_sum]
  congr 1
  exact Equiv.sum_comp (rlc_twoChannelFaithfulDualEquiv gamma gamma')
    (fun eta => FK.indexedBcWeight
      (rlc_twoChannelFaithfulEnds gamma gamma') ⊥ p q eta)


noncomputable def rlc_twoChannelFaithfulForcedDualEdgeProb {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (omega : RlcTwoChannelEdgeConfig gamma gamma') : Real :=
  BeffaraDC.pfdDualWeight
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') p q
      (FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))) /
    rlc_twoChannelFaithfulForcedDualEdgeZ gamma gamma' p q


theorem rlc_twoChannelFaithfulForcedDualEdgeProb_eq_indexed {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p : Real} (hp1 : p < 1) (q : Real)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelFaithfulForcedDualEdgeProb gamma gamma' p q omega =
      FK.indexedBcProb (rlc_twoChannelFaithfulEnds gamma gamma') ⊥ p q
        (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) := by
  unfold rlc_twoChannelFaithfulForcedDualEdgeProb FK.indexedBcProb
  rw [rlc_twoChannelFaithful_pfdDualWeight_eq_indexed,
    rlc_twoChannelFaithfulForcedDualEdgeZ_eq_indexed]
  apply mul_div_mul_left
  exact pow_ne_zero _ (by linarith)



noncomputable def rlc_twoChannelFaithfulForcedDualEdgeEventMass {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real)
    (A : Set (ConfigSpace
      (RlcTwoChannelFaithfulSourceEdge gamma gamma'))) : Real :=
  ∑ omega : RlcTwoChannelEdgeConfig gamma gamma',
    A.indicator (fun _ => (1 : Real))
        (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) *
      rlc_twoChannelFaithfulForcedDualEdgeProb gamma gamma' p q omega


theorem rlc_twoChannelFaithfulForcedDualEdgeEventMass_eq_indexed {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p : Real} (hp1 : p < 1) (q : Real)
    (A : Set (ConfigSpace
      (RlcTwoChannelFaithfulSourceEdge gamma gamma'))) :
    rlc_twoChannelFaithfulForcedDualEdgeEventMass gamma gamma' p q A =
      FK.indexedBcEventMass (rlc_twoChannelFaithfulEnds gamma gamma') ⊥
        p q A := by
  unfold rlc_twoChannelFaithfulForcedDualEdgeEventMass
    FK.indexedBcEventMass
  simp_rw [rlc_twoChannelFaithfulForcedDualEdgeProb_eq_indexed
    gamma gamma' hp1 q]
  exact Equiv.sum_comp (rlc_twoChannelFaithfulDualEquiv gamma gamma')
    (fun eta => A.indicator (fun _ => (1 : Real)) eta *
      FK.indexedBcProb (rlc_twoChannelFaithfulEnds gamma gamma') ⊥ p q eta)


theorem rlc_twoChannelFaithful_pfdDualWeight_edgeConfigCombine {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (outside : RlcTwoChannelOffGraphConfig gamma gamma') :
    BeffaraDC.pfdDualWeight
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') p q
        (FK.openSub
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside))) =
      BeffaraDC.pfdDualWeight
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma') p q
        (FK.openSub
          (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
          (rlc_connectorForceTraceConfig gamma gamma'
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))) := by
  congr 1
  rw [rlc_openSub_twoChannelAugmented_forceTrace,
    rlc_openSub_twoChannelAugmented_forceTrace,
    rlc_openSub_twoChannel_edgeConfigCombine]



theorem rlc_twoChannelForcedDualZ_eq_offGraph_mul_edgeZ {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) :
    rlc_twoChannelForcedDualZ gamma gamma' p q =
      Fintype.card (RlcTwoChannelOffGraphConfig gamma gamma') *
        rlc_twoChannelFaithfulForcedDualEdgeZ gamma gamma' p q := by
  let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'
  let split := rlc_twoChannelConfigSplitEquiv gamma gamma'
  let w : ConfigSpace (Sym2 (RlcConnectorVertex n)) → Real := fun rho =>
    BeffaraDC.pfdDualWeight P p q
      (FK.openSub P.G (rlc_connectorForceTraceConfig gamma gamma' rho))
  have hreindex := Equiv.sum_comp split
    (fun pair : RlcTwoChannelEdgeConfig gamma gamma' ×
        RlcTwoChannelOffGraphConfig gamma gamma' => w (split.symm pair))
  unfold rlc_twoChannelForcedDualZ
  dsimp only
  change (∑ rho, w rho) = _
  calc
    (∑ rho, w rho) = ∑ pair, w (split.symm pair) := by
      simpa only [Equiv.symm_apply_apply] using hreindex
    _ = ∑ omega : RlcTwoChannelEdgeConfig gamma gamma',
        ∑ outside : RlcTwoChannelOffGraphConfig gamma gamma',
          w (rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside) := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = ∑ omega : RlcTwoChannelEdgeConfig gamma gamma',
        ∑ _outside : RlcTwoChannelOffGraphConfig gamma gamma',
          BeffaraDC.pfdDualWeight P p q
            (FK.openSub P.G (rlc_connectorForceTraceConfig gamma gamma'
              (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))) := by
      apply Finset.sum_congr rfl
      intro omega _
      apply Finset.sum_congr rfl
      intro outside _
      exact rlc_twoChannelFaithful_pfdDualWeight_edgeConfigCombine
        gamma gamma' p q omega outside
    _ = Fintype.card (RlcTwoChannelOffGraphConfig gamma gamma') *
        rlc_twoChannelFaithfulForcedDualEdgeZ gamma gamma' p q := by
      unfold rlc_twoChannelFaithfulForcedDualEdgeZ
      simp [P, nsmul_eq_mul, Finset.mul_sum]

theorem rlc_twoChannelFaithfulForcedDualEdgeZ_pos {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < rlc_twoChannelFaithfulForcedDualEdgeZ gamma gamma' p q := by
  rw [rlc_twoChannelFaithfulForcedDualEdgeZ_eq_indexed]
  exact mul_pos (pow_pos (by linarith) _)
    (FK.indexedBcZ_pos (rlc_twoChannelFaithfulEnds gamma gamma') ⊥
      hp hp1 hq)



theorem rlc_twoChannelForcedDualProb_extend_mul_offGraph_eq_edgeProb {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    Fintype.card (RlcTwoChannelOffGraphConfig gamma gamma') *
        rlc_twoChannelForcedDualProb gamma gamma' p q
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) =
      rlc_twoChannelFaithfulForcedDualEdgeProb gamma gamma' p q omega := by
  have hcard : (Fintype.card
      (RlcTwoChannelOffGraphConfig gamma gamma') : Real) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hZ : rlc_twoChannelFaithfulForcedDualEdgeZ gamma gamma' p q ≠ 0 :=
    (rlc_twoChannelFaithfulForcedDualEdgeZ_pos
      gamma gamma' hp hp1 hq).ne'
  unfold rlc_twoChannelForcedDualProb
    rlc_twoChannelFaithfulForcedDualEdgeProb
  dsimp only
  rw [rlc_twoChannelForcedDualZ_eq_offGraph_mul_edgeZ]
  field_simp



def rlc_twoChannelFaithfulFullPullbackEvent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (A : Set (ConfigSpace
      (RlcTwoChannelFaithfulSourceEdge gamma gamma'))) :
    Set (ConfigSpace (Sym2 (RlcConnectorVertex n))) :=
  {rho | rlc_twoChannelFaithfulDualConfig gamma gamma'
      (rlc_twoChannelConfigSplitEquiv gamma gamma' rho).1 ∈ A}



theorem rlc_twoChannelForcedDualEventMass_faithfulPullback_eq_edge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace
      (RlcTwoChannelFaithfulSourceEdge gamma gamma'))) :
    rlc_twoChannelForcedDualEventMass gamma gamma' p q
        (rlc_twoChannelFaithfulFullPullbackEvent gamma gamma' A) =
      rlc_twoChannelFaithfulForcedDualEdgeEventMass gamma gamma' p q A := by
  classical
  let split := rlc_twoChannelConfigSplitEquiv gamma gamma'
  let summand : ConfigSpace (Sym2 (RlcConnectorVertex n)) → Real :=
    fun rho =>
      (rlc_twoChannelFaithfulFullPullbackEvent gamma gamma' A).indicator
          (fun _ => (1 : Real)) rho *
        rlc_twoChannelForcedDualProb gamma gamma' p q rho
  have hreindex := Equiv.sum_comp split
    (fun pair : RlcTwoChannelEdgeConfig gamma gamma' ×
        RlcTwoChannelOffGraphConfig gamma gamma' =>
      summand (split.symm pair))
  unfold rlc_twoChannelForcedDualEventMass
    rlc_twoChannelFaithfulForcedDualEdgeEventMass
  change (∑ rho, summand rho) = _
  calc
    (∑ rho, summand rho) = ∑ pair, summand (split.symm pair) := by
      simpa only [Equiv.symm_apply_apply] using hreindex
    _ = ∑ omega : RlcTwoChannelEdgeConfig gamma gamma',
        ∑ outside : RlcTwoChannelOffGraphConfig gamma gamma',
          A.indicator (fun _ => (1 : Real))
              (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) *
            rlc_twoChannelForcedDualProb gamma gamma' p q
              (rlc_twoChannelEdgeConfigCombine gamma gamma' omega outside) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro omega _
      apply Finset.sum_congr rfl
      intro outside _
      change (if rlc_twoChannelFaithfulDualConfig gamma gamma'
          (split (split.symm (omega, outside))).1 ∈ A then 1 else 0) *
          rlc_twoChannelForcedDualProb gamma gamma' p q
            (split.symm (omega, outside)) =
        (if rlc_twoChannelFaithfulDualConfig gamma gamma' omega ∈ A
          then 1 else 0) *
          rlc_twoChannelForcedDualProb gamma gamma' p q
            (split.symm (omega, outside))
      rw [split.apply_symm_apply]
    _ = ∑ omega : RlcTwoChannelEdgeConfig gamma gamma',
        ∑ _outside : RlcTwoChannelOffGraphConfig gamma gamma',
          A.indicator (fun _ => (1 : Real))
              (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) *
            rlc_twoChannelForcedDualProb gamma gamma' p q
              (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) := by
      apply Finset.sum_congr rfl
      intro omega _
      apply Finset.sum_congr rfl
      intro outside _
      rw [rlc_twoChannelForcedDualProb_edgeConfigCombine]
    _ = ∑ omega : RlcTwoChannelEdgeConfig gamma gamma',
        A.indicator (fun _ => (1 : Real))
            (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) *
          (Fintype.card (RlcTwoChannelOffGraphConfig gamma gamma') *
            rlc_twoChannelForcedDualProb gamma gamma' p q
              (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)) := by
      apply Finset.sum_congr rfl
      intro omega _
      simp [nsmul_eq_mul]
      ring
    _ = ∑ omega : RlcTwoChannelEdgeConfig gamma gamma',
        A.indicator (fun _ => (1 : Real))
            (rlc_twoChannelFaithfulDualConfig gamma gamma' omega) *
          rlc_twoChannelFaithfulForcedDualEdgeProb
            gamma gamma' p q omega := by
      apply Finset.sum_congr rfl
      intro omega _
      rw [rlc_twoChannelForcedDualProb_extend_mul_offGraph_eq_edgeProb
        gamma gamma' hp hp1 hq]

def rlc_twoChannelFaithfulFaceOnRight {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (C : RlcTwoChannelFaithfulFace gamma gamma') : Prop :=
  ∃ x : RlcConnectorVertex n, rlc_connectorOnRight gamma x ∧
    C = BeffaraDC.pfdFace
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (rlc_dualReflect.symm x.1)

def rlc_twoChannelFaithfulFaceOnLeft {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (C : RlcTwoChannelFaithfulFace gamma gamma') : Prop :=
  ∃ x : RlcConnectorVertex n, rlc_connectorOnLeft gamma' x ∧
    C = BeffaraDC.pfdFace
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (rlc_dualReflect.symm x.1)

noncomputable instance rlc_twoChannelFaithfulFaceOnRightDecidable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidablePred (rlc_twoChannelFaithfulFaceOnRight gamma gamma') :=
  Classical.decPred _

noncomputable instance rlc_twoChannelFaithfulFaceOnLeftDecidable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    DecidablePred (rlc_twoChannelFaithfulFaceOnLeft gamma gamma') :=
  Classical.decPred _

noncomputable def rlc_twoChannelFaithfulFaceSeparateWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcTwoChannelFaithfulFace gamma gamma') :=
  Lattice.boundaryCliqueGraph
      (rlc_twoChannelFaithfulFaceOnRight gamma gamma') ⊔
    Lattice.boundaryCliqueGraph
      (rlc_twoChannelFaithfulFaceOnLeft gamma gamma')

noncomputable def rlc_twoChannelFaithfulFaceMergedWiring {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcTwoChannelFaithfulFace gamma gamma') :=
  Lattice.boundaryCliqueGraph (fun C =>
    rlc_twoChannelFaithfulFaceOnRight gamma gamma' C ∨
      rlc_twoChannelFaithfulFaceOnLeft gamma gamma' C)

noncomputable instance rlc_twoChannelFaithfulFaceSeparateWiringDecidableAdj
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel
      (rlc_twoChannelFaithfulFaceSeparateWiring gamma gamma').Adj :=
  Classical.decRel _

noncomputable instance rlc_twoChannelFaithfulFaceMergedWiringDecidableAdj
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel
      (rlc_twoChannelFaithfulFaceMergedWiring gamma gamma').Adj :=
  Classical.decRel _

theorem rlc_twoChannelFaithfulFaceSeparateWiring_le_merged {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_twoChannelFaithfulFaceSeparateWiring gamma gamma' ≤
      rlc_twoChannelFaithfulFaceMergedWiring gamma gamma' := by
  intro C D hCD
  rw [rlc_twoChannelFaithfulFaceSeparateWiring,
    SimpleGraph.sup_adj, Lattice.boundaryCliqueGraph_adj,
    Lattice.boundaryCliqueGraph_adj] at hCD
  rw [rlc_twoChannelFaithfulFaceMergedWiring,
    Lattice.boundaryCliqueGraph_adj]
  rcases hCD with hright | hleft
  · exact ⟨hright.1, Or.inl hright.2.1, Or.inl hright.2.2⟩
  · exact ⟨hleft.1, Or.inr hleft.2.1, Or.inr hleft.2.2⟩


def rlc_twoChannelFaithfulFaceConnectorEvent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (ConfigSpace (RlcTwoChannelFaithfulSourceEdge gamma gamma')) :=
  {eta | ∃ C D : RlcTwoChannelFaithfulFace gamma gamma',
    rlc_twoChannelFaithfulFaceOnRight gamma gamma' C ∧
    rlc_twoChannelFaithfulFaceOnLeft gamma gamma' D ∧
    (FK.indexedOpenGraph
      (rlc_twoChannelFaithfulEnds gamma gamma') eta).Reachable C D}




theorem rlc_twoChannelFaithfulFaceConnectorEvent_of_failure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    rlc_twoChannelFaithfulDualConfig gamma gamma' omega ∈
      rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma' := by
  let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'
  let K := FK.openSub P.G
    (rlc_connectorForceTraceConfig gamma gamma'
      (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))
  obtain ⟨x, y, hx, hy, hxPath, hyPath⟩ :=
    rlc_twoChannelFullFilledBoundaryContacts_of_faithful_failure
      gamma gamma' hfaith omega hno
  obtain ⟨a⟩ := rlc_twoChannelFullFilledFaceBoundary_reachable
    gamma gamma' omega hx hy
  let hle := rlc_twoChannelFullFilledBoundary_le_openFaceDual
    gamma gamma' omega
  have hface : (openSubgraph 2 (fci_faceDualConfig
      (rlc_twoChannelFullAmbientConfig gamma gamma' omega))).Reachable x y :=
    ⟨a.mapLe hle⟩
  have hregion : (whb_faceRegion (jei_pushGraph P K)).Reachable x y :=
    hface.mono (rlc_twoChannelFullFaceDual_le_pfdRegion
      gamma gamma' omega)
  have hdual : (BeffaraDC.pfdClosedDual P K).Reachable
      (BeffaraDC.pfdFace P x) (BeffaraDC.pfdFace P y) :=
    BeffaraDC.pfd_regionReachable_to_dual P K hregion
  have hindexed : (FK.indexedOpenGraph
      (rlc_twoChannelFaithfulEnds gamma gamma')
      (rlc_twoChannelFaithfulDualConfig gamma gamma' omega)).Reachable
        (BeffaraDC.pfdFace P x) (BeffaraDC.pfdFace P y) := by
    rw [rlc_twoChannelFaithful_indexedOpenGraph_eq_pfdClosedDual]
    exact hdual
  let xr : RlcConnectorVertex n :=
    ⟨rlc_dualReflect x,
      rlc_rightPathVertex_mem_connectorBox gamma hxPath⟩
  let yl : RlcConnectorVertex n :=
    ⟨rlc_dualReflect y,
      rlc_leftPathVertex_mem_connectorBox gamma' hyPath⟩
  refine ⟨BeffaraDC.pfdFace P x, BeffaraDC.pfdFace P y, ?_, ?_, hindexed⟩
  · refine ⟨xr, ?_, ?_⟩
    · exact hxPath
    · simp [xr, P]
  · refine ⟨yl, ?_, ?_⟩
    · exact hyPath
    · simp [yl, P]




theorem rlc_twoChannelFaithfulFaceConnectorEvent_to_ambientReachable
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hconn : rlc_twoChannelFaithfulDualConfig gamma gamma' omega ∈
      rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') :
    ∃ x y : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
      (openSubgraph 2 (rlc_dualReflectConfig
        (rlc_twoChannelFullAmbientConfig gamma gamma' omega))).Reachable
          x.1 y.1 := by
  let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'
  let K := FK.openSub P.G
    (rlc_connectorForceTraceConfig gamma gamma'
      (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))
  obtain ⟨C, D, ⟨x, hx, hC⟩, ⟨y, hy, hD⟩, hdual⟩ := hconn
  have hdual' : (BeffaraDC.pfdClosedDual P K).Reachable
      (BeffaraDC.pfdFace P (rlc_dualReflect.symm x.1))
      (BeffaraDC.pfdFace P (rlc_dualReflect.symm y.1)) := by
    rw [← hC, ← hD]
    rw [← rlc_twoChannelFaithful_indexedOpenGraph_eq_pfdClosedDual]
    exact hdual
  have hregion := (BeffaraDC.pfd_regionReachable_iff_dual P K
    (FK.openSub_le P.G
      (rlc_connectorForceTraceConfig gamma gamma'
        (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)))).mpr hdual'
  have hface : (openSubgraph 2 (fci_faceDualConfig
      (rlc_twoChannelFullAmbientConfig gamma gamma' omega))).Reachable
        (rlc_dualReflect.symm x.1) (rlc_dualReflect.symm y.1) := by
    rw [rlc_twoChannelFullFaceDual_eq_pfdRegion]
    exact hregion
  obtain ⟨w⟩ := hface
  have hreflected := (w.map (rlc_dualReflectOpenHom
    (rlc_twoChannelFullAmbientConfig gamma gamma' omega))).reachable
  refine ⟨x, y, hx, hy, ?_⟩
  simpa [rlc_dualReflectOpenHom] using hreflected





theorem rlc_twoChannelFaithfulFaceConnectorEvent_to_indexedOuterReachable
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hconn : rlc_twoChannelFaithfulDualConfig gamma gamma' omega ∈
      rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') :
    ∃ x y : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
      (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Reachable
        (rlc_twoChannelIndexedOuterTarget gamma gamma' x)
        (rlc_twoChannelIndexedOuterTarget gamma gamma' y) := by
  let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'
  let K := FK.openSub P.G
    (rlc_connectorForceTraceConfig gamma gamma'
      (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))
  obtain ⟨C, D, ⟨x, hx, hC⟩, ⟨y, hy, hD⟩, hdual⟩ := hconn
  have hdual' : (BeffaraDC.pfdClosedDual P K).Reachable
      (BeffaraDC.pfdFace P (rlc_dualReflect.symm x.1))
      (BeffaraDC.pfdFace P (rlc_dualReflect.symm y.1)) := by
    rw [← hC, ← hD]
    rw [← rlc_twoChannelFaithful_indexedOpenGraph_eq_pfdClosedDual]
    exact hdual
  refine ⟨x, y, hx, hy, ?_⟩
  exact rlc_twoChannelIndexedOuterTargets_reachable_of_pfd
    gamma gamma' omega x y hdual'



theorem rlc_twoChannelFaithfulFaceConnectorEvent_iff_indexedOuterReachable
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelFaithfulDualConfig gamma gamma' omega ∈
        rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma' ↔
      ∃ x y : RlcConnectorVertex n,
        rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
        (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Reachable
          (rlc_twoChannelIndexedOuterTarget gamma gamma' x)
          (rlc_twoChannelIndexedOuterTarget gamma gamma' y) := by
  constructor
  · exact rlc_twoChannelFaithfulFaceConnectorEvent_to_indexedOuterReachable
      gamma gamma' omega
  · rintro ⟨x, y, hx, hy, hxy⟩
    let C := BeffaraDC.pfdFace
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (rlc_dualReflect.symm x.1)
    let D := BeffaraDC.pfdFace
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')
      (rlc_dualReflect.symm y.1)
    refine ⟨C, D, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, ?_⟩
    have hpfd := (rlc_twoChannelIndexedOuter_reachable_iff_pfd
      gamma gamma' omega
      (rlc_twoChannelIndexedOuterTarget gamma gamma' x)
      (rlc_twoChannelIndexedOuterTarget gamma gamma' y)).mp hxy
    rw [rlc_twoChannelFaithful_indexedOpenGraph_eq_pfdClosedDual]
    simpa [C, D, rlc_twoChannelIndexedFaceProjection,
      rlc_twoChannelIndexedOuterTarget] using hpfd



theorem rlc_twoChannelFailure_to_indexedOuterReachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    ∃ x y : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
      (rlc_twoChannelIndexedOuterOpenGraph gamma gamma' omega).Reachable
        (rlc_twoChannelIndexedOuterTarget gamma gamma' x)
        (rlc_twoChannelIndexedOuterTarget gamma gamma' y) := by
  apply rlc_twoChannelFaithfulFaceConnectorEvent_to_indexedOuterReachable
    gamma gamma' omega
  exact rlc_twoChannelFaithfulFaceConnectorEvent_of_failure
    gamma gamma' hfaith omega hno

theorem rlc_twoChannelFaithfulFaceConnectorEvent_isIncreasing {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    IsIncreasing
      (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') := by
  intro eta eta' heta
  rintro ⟨C, D, hC, hD, hreach⟩
  refine ⟨C, D, hC, hD, hreach.mono ?_⟩
  intro x y hxy
  simp only [FK.indexedOpenGraph, SimpleGraph.fromEdgeSet_adj,
    Set.mem_setOf_eq] at hxy ⊢
  obtain ⟨⟨e, he, hopen⟩, hne⟩ := hxy
  refine ⟨⟨e, he, ?_⟩, hne⟩
  apply Bool.eq_true_of_not_eq_false
  intro hfalse
  have hle := heta e
  rw [hopen, hfalse] at hle
  exact (show ¬((true : Bool) ≤ false) by decide) hle



theorem rlc_twoChannelFaithfulFaceFree_le_merged {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    (⊥ : SimpleGraph (RlcTwoChannelFaithfulFace gamma gamma')) ≤
      rlc_twoChannelFaithfulFaceMergedWiring gamma gamma' :=
  bot_le



theorem rlc_twoChannelFaithfulFaceIndexedMass_free_le_merged {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    FK.indexedBcEventMass (rlc_twoChannelFaithfulEnds gamma gamma') ⊥ p q
        (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') ≤
      FK.indexedBcEventMass (rlc_twoChannelFaithfulEnds gamma gamma')
        (rlc_twoChannelFaithfulFaceMergedWiring gamma gamma') p q
        (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') := by
  exact FK.indexedBcEventMass_mono_bc
    (rlc_twoChannelFaithfulEnds gamma gamma') ⊥
    (rlc_twoChannelFaithfulFaceMergedWiring gamma gamma')
    (rlc_twoChannelFaithfulFaceFree_le_merged gamma gamma')
    hp hp1 hq
    (rlc_twoChannelFaithfulFaceConnectorEvent_isIncreasing gamma gamma')



theorem rlc_twoChannelFaithfulForcedDualEdgeConnectorMass_le_merged {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    rlc_twoChannelFaithfulForcedDualEdgeEventMass gamma gamma' p q
        (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') ≤
      FK.indexedBcEventMass (rlc_twoChannelFaithfulEnds gamma gamma')
        (rlc_twoChannelFaithfulFaceMergedWiring gamma gamma') p q
        (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') := by
  rw [rlc_twoChannelFaithfulForcedDualEdgeEventMass_eq_indexed
    gamma gamma' hp1 q]
  exact rlc_twoChannelFaithfulFaceIndexedMass_free_le_merged
    gamma gamma' hp hp1 hq



theorem rlc_twoChannelFailure_subset_faithfulFacePullback {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ ⊆
      rlc_twoChannelFaithfulFullPullbackEvent gamma gamma'
        (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') := by
  intro rho hno
  have hnoEdge : rlc_twoChannelEdgeConfigExtend gamma gamma'
      (rlc_twoChannelConfigSplitEquiv gamma gamma' rho).1 ∉
        rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
    intro hedge
    exact hno ((rlc_twoChannel_split_fst_mem_event_iff
      gamma gamma' rho).mp hedge)
  exact rlc_twoChannelFaithfulFaceConnectorEvent_of_failure
    gamma gamma' hfaith
      (rlc_twoChannelConfigSplitEquiv gamma gamma' rho).1 hnoEdge



theorem rlc_twoChannelForcedDualFailureMass_le_faithfulMerged {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    rlc_twoChannelForcedDualEventMass gamma gamma' p q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ ≤
      FK.indexedBcEventMass (rlc_twoChannelFaithfulEnds gamma gamma')
        (rlc_twoChannelFaithfulFaceMergedWiring gamma gamma') p q
        (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') := by
  calc
    rlc_twoChannelForcedDualEventMass gamma gamma' p q
        (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ ≤
      rlc_twoChannelForcedDualEventMass gamma gamma' p q
        (rlc_twoChannelFaithfulFullPullbackEvent gamma gamma'
          (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma')) :=
      by
        unfold rlc_twoChannelForcedDualEventMass
        apply Finset.sum_le_sum
        intro rho _
        by_cases hfail : rho ∈
            (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ
        · have hpull := rlc_twoChannelFailure_subset_faithfulFacePullback
            gamma gamma' hfaith hfail
          simp [hfail, hpull]
        · by_cases hpull : rho ∈
              rlc_twoChannelFaithfulFullPullbackEvent gamma gamma'
                (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma')
          · simp [hfail, hpull,
              rlc_twoChannelForcedDualProb_nonneg gamma gamma' hp hp1
                (lt_of_lt_of_le zero_lt_one hq) rho]
          · simp [hfail, hpull]
    _ = rlc_twoChannelFaithfulForcedDualEdgeEventMass gamma gamma' p q
        (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') :=
      rlc_twoChannelForcedDualEventMass_faithfulPullback_eq_edge
        gamma gamma' hp hp1 (lt_of_lt_of_le zero_lt_one hq)
          (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma')
    _ ≤ FK.indexedBcEventMass (rlc_twoChannelFaithfulEnds gamma gamma')
        (rlc_twoChannelFaithfulFaceMergedWiring gamma gamma') p q
        (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') :=
      rlc_twoChannelFaithfulForcedDualEdgeConnectorMass_le_merged
        gamma gamma' hp hp1 hq


theorem rlc_twoChannelFaithfulFaceIndexedMass_mono_merged {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    FK.indexedBcEventMass (rlc_twoChannelFaithfulEnds gamma gamma')
        (rlc_twoChannelFaithfulFaceSeparateWiring gamma gamma') p q
        (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') ≤
      FK.indexedBcEventMass (rlc_twoChannelFaithfulEnds gamma gamma')
        (rlc_twoChannelFaithfulFaceMergedWiring gamma gamma') p q
        (rlc_twoChannelFaithfulFaceConnectorEvent gamma gamma') := by
  exact FK.indexedBcEventMass_mono_bc
    (rlc_twoChannelFaithfulEnds gamma gamma')
    (rlc_twoChannelFaithfulFaceSeparateWiring gamma gamma')
    (rlc_twoChannelFaithfulFaceMergedWiring gamma gamma')
    (rlc_twoChannelFaithfulFaceSeparateWiring_le_merged gamma gamma')
    hp hp1 hq
    (rlc_twoChannelFaithfulFaceConnectorEvent_isIncreasing gamma gamma')

end

end StatMech.Universality
