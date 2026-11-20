/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardPrincipalAngleMultiaffine
import Code.FrontierA.KacWardReversibleCycleCoefficient
import Code.FrontierA.SurfaceKacWardQuadraticAssembly












open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager

universe u





structure SurfaceFlatSpinorEmbedding (g : Nat)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  phase : G.Dart -> G.Dart -> Complex
  edgeClass : Sym2 V -> SurfaceHomology g
  localIntersection : Sym2 V -> Sym2 V -> Fin 2
  degree_le_three : forall vertex, G.degree vertex <= 3
  phase_reverse : forall dart next,
    G.DartAdj dart next -> dart.edge ≠ next.edge ->
      phase next.symm dart.symm = (phase dart next)⁻¹
  path_phase_sq : forall {N : Nat} (path : Fin (N + 1) -> G.Dart),
    path (Fin.last N) = (path 0).symm ->
      (forall j : Fin N,
        G.DartAdj (path j.castSucc) (path j.succ) /\
          (path j.castSucc).edge ≠ (path j.succ).edge) ->
      (∏ j : Fin N,
        phase (path j.castSucc) (path j.succ)) ^ 2 = -1
  closed_phase_sq : forall {n : Nat} [NeZero n]
      (loop : Fin n -> G.Dart),
    (forall k : Fin n,
      G.DartAdj (loop k) (loop (k + 1)) /\
        (loop k).edge ≠ (loop (k + 1)).edge) ->
      (∏ k, phase (loop k) (loop (k + 1))) ^ 2 = 1
  simple_cycle_spin_holonomy : forall {root : V}
      (p : G.Walk root root) (hp : p.IsCycle),
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwLoopPhaseProduct phase (kwGraphCycleDartLoop p) =
      -(surfaceBaseCycleCoefficient edgeClass p.edges.toFinset)
  intersection_formula : forall (F K : Finset (Sym2 V)),
    surfaceIntersection
        (surfaceSubgraphHomology edgeClass F)
        (surfaceSubgraphHomology edgeClass K) =
      ∑ edge ∈ F, ∑ other ∈ K,
        localIntersection edge other
  localIntersection_zero : forall (edge other : Sym2 V),
    Disjoint edge.toFinset other.toFinset ->
      localIntersection edge other = 0

theorem surfaceParitySign_ne_zero (z : Fin 2) :
    surfaceParitySign z ≠ 0 := by
  fin_cases z <;> norm_num [surfaceParitySign]

theorem kwGraphFormalLogCoeff_squarefree_of_mem_reversalInvariant'
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart -> G.Dart -> Complex)
    (hrev : KWGraphLoopReversalInvariant G phase)
    (hdeg : forall vertex, G.degree vertex <= 3)
    (S : Finset (Sym2 V)) {n : Nat} [NeZero n]
    (loop : Fin n -> G.Dart)
    (hloop : loop ∈ kwGraphSquarefreeLoopFinset G phase S) :
    kwGraphFormalLogCoeff G phase (ons_finsetExponent S) =
      -kwGraphLoopScalar G phase loop := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact kwGraphFormalLogCoeff_squarefree_of_mem_reversalInvariant
    G phase hrev hdeg S r loop hloop

theorem edge_toFinset_subset_walk_verts
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) {edge : Sym2 V}
    (hedge : edge ∈ p.edges.toFinset) :
    (edge.toFinset : Set V) ⊆ p.toSubgraph.verts := by
  intro x hx
  apply p.toSubgraph.mem_verts_of_mem_edge
  · rw [p.mem_edges_toSubgraph]
    exact List.mem_toFinset.mp hedge
  · exact Sym2.mem_toFinset.mp hx



theorem SurfaceFlatSpinorEmbedding.disjointCycleIsotropic
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : SurfaceFlatSpinorEmbedding g G) :
    SurfaceDisjointCycleIsotropic G embedding.edgeClass := by
  intro u v p q hp hq hverts
  rw [embedding.intersection_formula]
  apply Finset.sum_eq_zero
  intro edge hedge
  apply Finset.sum_eq_zero
  intro other hother
  apply embedding.localIntersection_zero
  rw [Finset.disjoint_left]
  intro x hxedge hxother
  have hxp : x ∈ p.toSubgraph.verts :=
    edge_toFinset_subset_walk_verts p hedge hxedge
  have hxq : x ∈ q.toSubgraph.verts :=
    edge_toFinset_subset_walk_verts q hother hxother
  exact (Set.disjoint_left.1 hverts hxp hxq)



theorem SurfaceFlatSpinorEmbedding.loopReversalInvariant
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : SurfaceFlatSpinorEmbedding g G) :
    KWGraphLoopReversalInvariant G embedding.phase := by
  intro n hn loop hvalid
  have hweight := kwSpinorGraphLoopWeight_loopRev
    G embedding.phase embedding.phase_reverse embedding.closed_phase_sq
    (fun _ => (1 : Complex)) loop
  rw [kwGraphLoopWeight_factor, kwGraphLoopWeight_factor] at hweight
  simpa [kwGraphLoopRev] using hweight



theorem SurfaceFlatSpinorEmbedding.simpleCycleLogCoeff
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : SurfaceFlatSpinorEmbedding g G)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    kwGraphFormalLogCoeff G embedding.phase
        (ons_finsetExponent p.edges.toFinset) =
      surfaceBaseCycleCoefficient embedding.edgeClass p.edges.toFinset := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  have hscalar : kwGraphLoopScalar G embedding.phase
      (kwGraphCycleDartLoop p) =
        -surfaceBaseCycleCoefficient embedding.edgeClass p.edges.toFinset := by
    rw [kwGraphCycleDartLoop_scalar_eq_phaseProduct G embedding.phase p hp]
    exact embedding.simple_cycle_spin_holonomy p hp
  have hscalarNe : kwGraphLoopScalar G embedding.phase
      (kwGraphCycleDartLoop p) ≠ 0 := by
    rw [hscalar]
    unfold surfaceBaseCycleCoefficient
    exact neg_ne_zero.mpr <| Complex.ofReal_ne_zero.mpr <|
      surfaceParitySign_ne_zero _
  have hd : kwGraphCycleDartLoop p ∈
      kwGraphSquarefreeLoopFinset G embedding.phase p.edges.toFinset := by
    rw [kwGraph_mem_squarefreeLoopFinset]
    exact ⟨kwGraphCycleDartLoop_exponent G p hp, hscalarNe⟩
  rw [kwGraphFormalLogCoeff_squarefree_of_mem_reversalInvariant'
    G embedding.phase embedding.loopReversalInvariant
      embedding.degree_le_three p.edges.toFinset
      (kwGraphCycleDartLoop p) hd, hscalar]
  ring



theorem SurfaceFlatSpinorEmbedding.weightedCycleLog
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : SurfaceFlatSpinorEmbedding g G) :
    KWGraphWeightedCycleLog G embedding.phase
      (surfaceBaseCycleCoefficient embedding.edgeClass) := by
  constructor
  · intro root p hp
    exact embedding.simpleCycleLogCoeff p hp
  · exact kwGraphFormalLogCoeff_squarefree_cycle_of_ne_zero
      G embedding.phase embedding.degree_le_three


theorem SurfaceFlatSpinorEmbedding.formalRoot_nonsquarefree
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : SurfaceFlatSpinorEmbedding g G)
    (m : Sym2 V →₀ Nat) (hm : ¬ ons_IsSquarefreeExponent m) :
    MvPowerSeries.coeff m
      (kwGraphFormalRoot G embedding.phase) = 0 := by
  simp only [ons_IsSquarefreeExponent] at hm
  push Not at hm
  obtain ⟨edge, hedge⟩ := hm
  have hrepeated : 2 <= m edge := by omega
  by_cases hedgeG : edge ∈ G.edgeFinset
  · rw [SimpleGraph.mem_edgeFinset] at hedgeG
    obtain ⟨v, w⟩ := edge
    let selected : G.Dart := ⟨(v, w), hedgeG⟩
    exact kw_spinorGraph_formalRoot_coeff_eq_zero_of_repeated
      G embedding.phase embedding.path_phase_sq embedding.phase_reverse
        embedding.closed_phase_sq selected m hrepeated
  · exact kwGraphFormalRoot_coeff_eq_zero_of_offGraph
      G embedding.phase m edge hedgeG (by omega)



theorem surface_flatSpinor_kacWard_det_square
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : SurfaceFlatSpinorEmbedding g G)
    (lambda : SurfaceSpinStructure g) (weight : Sym2 V -> Complex) :
    (1 - surfaceTwistedKacWardMatrix G embedding.phase
        embedding.edgeClass lambda weight).det =
      surfaceQuadraticEvenPolynomial G embedding.edgeClass lambda weight ^ 2 := by
  exact surface_twisted_kacWard_det_square_of_cycle_phase
    G embedding.phase embedding.edgeClass embedding.weightedCycleLog
      embedding.disjointCycleIsotropic embedding.degree_le_three
      embedding.formalRoot_nonsquarefree lambda weight


theorem surface_flatSpinor_kacWard_arf_formula
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : SurfaceFlatSpinorEmbedding g G)
    (weight : Sym2 V -> Real) :
    (forall lambda : SurfaceSpinStructure g,
      (1 - surfaceTwistedKacWardMatrix G embedding.phase
          embedding.edgeClass lambda
          (fun edge => (weight edge : Complex))).det =
        (surfaceTwistedSectorSquare
          (surfaceGraphSectorWeight G embedding.edgeClass weight)
          lambda : Complex)) /\
    surfaceUnsignedSectorSum
        (surfaceGraphSectorWeight G embedding.edgeClass weight) =
      ((2 : Real) ^ g)⁻¹ *
        ∑ lambda : SurfaceSpinStructure g,
          surfaceParitySign (surfaceArfParity lambda) *
            surfaceTwistedSectorRoot
              (surfaceGraphSectorWeight G embedding.edgeClass weight)
              lambda := by
  constructor
  · intro lambda
    exact surface_twisted_kacWard_det_eq_sectorSquare_of_cycle_phase
      G embedding.phase embedding.edgeClass embedding.weightedCycleLog
        embedding.disjointCycleIsotropic embedding.degree_le_three
        embedding.formalRoot_nonsquarefree lambda weight
  · exact surface_arf_reconstruction g
      (surfaceGraphSectorWeight G embedding.edgeClass weight)

end StatMech.FrontierA
