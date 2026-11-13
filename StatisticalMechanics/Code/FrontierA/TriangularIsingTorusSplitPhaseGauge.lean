/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusSplitPhase
import Code.FrontierA.TriangularIsingTorusSplitHomology
import Code.FrontierA.SurfaceKacWardShiftedCycleAssembly





namespace StatMech.FrontierA

open SimpleGraph

theorem triangularTorusSplitDartDirection_nonbacktracking
    (L : Nat) [Fact (2 < L)]
    (d e : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Dart)
    (hconnect : d.snd = e.fst) (hne : d.edge ≠ e.edge) :
    triangularTorusSplitDartDirection L e ≠
      triangularTorusDirectionReverse (triangularTorusSplitDartDirection L d) := by
  intro hreverse
  have hdart : (triangularTorusSplitEmbedHom L).mapDart e =
      ((triangularTorusSplitEmbedHom L).mapDart d).symm := by
    apply triangularTorusGraphDartDirection_fst_injective (3 * L)
    · change triangularTorusSplitEmbedVertex L e.fst =
        triangularTorusSplitEmbedVertex L d.snd
      rw [hconnect]
    · rw [triangularTorusGraphDartDirection_symm,
        triangularTorusSplitEmbedHom_mapDart_direction,
        triangularTorusSplitEmbedHom_mapDart_direction]
      exact hreverse
  apply hne
  have hedge := congrArg SimpleGraph.Dart.edge hdart
  have hmapped :=
    (hedge.trans ((triangularTorusSplitEmbedHom L).mapDart d).edge_symm).symm
  change Sym2.map (triangularTorusSplitEmbedHom L) d.edge =
    Sym2.map (triangularTorusSplitEmbedHom L) e.edge at hmapped
  exact Sym2.map.injective (triangularTorusSplitEmbedVertex_injective L) hmapped

theorem triangularTorusPortDirection_of_matching
    (L : Nat) [Fact (2 < L)]
    {p q : KWDartPort (triangularTorusGraph L)}
    (hmatching : kwDartOfPort (triangularTorusGraph L) q =
      (kwDartOfPort (triangularTorusGraph L) p).symm) :
    triangularTorusGraphDartDirection L
        (kwDartOfPort (triangularTorusGraph L) q) =
      triangularTorusDirectionReverse
        (triangularTorusGraphDartDirection L
          (kwDartOfPort (triangularTorusGraph L) p)) := by
  rw [hmatching, triangularTorusGraphDartDirection_symm]



theorem triangularTorusSplit_refinedPhase_eq_gauge
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    (d e : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Dart)
    (hconnect : d.snd = e.fst) (hne : d.edge ≠ e.edge) :
    triangularTorusGraphPhase (3 * L) rho 1 1
        ((triangularTorusSplitEmbedHom L).mapDart d)
        ((triangularTorusSplitEmbedHom L).mapDart e) =
      kwPhaseGauge (triangularTorusSplitPhaseGauge L rho)
        (kwLocalAngularSplitPhase
          (triangularTorusLocalAngularData L rho hrho)) d e := by
  classical
  rw [triangularTorusGraphPhase_one_one_apply,
    triangularTorusSplitEmbedHom_mapDart_direction,
    triangularTorusSplitEmbedHom_mapDart_direction]
  have hdirne := triangularTorusSplitDartDirection_nonbacktracking
    L d e hconnect hne
  generalize hda : triangularTorusGraphDartDirection L
    (kwDartOfPort (triangularTorusGraph L) d.fst) = a
  generalize hdb : triangularTorusGraphDartDirection L
    (kwDartOfPort (triangularTorusGraph L) d.snd) = b
  generalize hec : triangularTorusGraphDartDirection L
    (kwDartOfPort (triangularTorusGraph L) e.snd) = c
  have heb : triangularTorusGraphDartDirection L
      (kwDartOfPort (triangularTorusGraph L) e.fst) = b := by
    rw [← hconnect]
    exact hdb
  by_cases hd : kwDartOfPort (triangularTorusGraph L) d.snd =
      (kwDartOfPort (triangularTorusGraph L) d.fst).symm
  · have hba : b = triangularTorusDirectionReverse a := by
      simpa [hda, hdb] using triangularTorusPortDirection_of_matching L hd
    by_cases he : kwDartOfPort (triangularTorusGraph L) e.snd =
        (kwDartOfPort (triangularTorusGraph L) e.fst).symm
    · exfalso
      apply hdirne
      simpa [triangularTorusSplitDartDirection, hd, he, hda, hdb, heb]
        using hba
    · have herank := (kwOrderedDartPortSplitGraph_adj
          (triangularTorusGraph L) (triangularTorusLocalPortOrder L)
          e.fst e.snd).mp e.adj |>.resolve_left he |>.2
      have hrank : (triangularTorusDirectionRank b).val + 1 =
            (triangularTorusDirectionRank c).val ∨
          (triangularTorusDirectionRank c).val + 1 =
            (triangularTorusDirectionRank b).val := by
        simpa [triangularTorusLocalPortOrder_rank, heb, hec] using herank
      have ha : a = triangularTorusDirectionReverse b := by
        rw [hba, triangularOppositeDirection_reverse]
      simpa [kwPhaseGauge, triangularTorusSplitPhaseGauge,
        triangularTorusSplitDartDirection, hd, he, hda, hdb, heb, hec,
        ha, kwLocalAngularSplitPhase, triangularTorusLocalAngularData,
        triangularTorusLocalPortRoot, triangularTorusLocalPortOrder_rank] using
          triangularSplit_entry_phase rho hrho b c hrank
  · have hdrank := (kwOrderedDartPortSplitGraph_adj
        (triangularTorusGraph L) (triangularTorusLocalPortOrder L)
        d.fst d.snd).mp d.adj |>.resolve_left hd |>.2
    have hrankD : (triangularTorusDirectionRank a).val + 1 =
          (triangularTorusDirectionRank b).val ∨
        (triangularTorusDirectionRank b).val + 1 =
          (triangularTorusDirectionRank a).val := by
      simpa [triangularTorusLocalPortOrder_rank, hda, hdb] using hdrank
    by_cases he : kwDartOfPort (triangularTorusGraph L) e.snd =
        (kwDartOfPort (triangularTorusGraph L) e.fst).symm
    · simpa [kwPhaseGauge, triangularTorusSplitPhaseGauge,
        triangularTorusSplitDartDirection, hd, he, hda, hdb, heb, hec,
        kwLocalAngularSplitPhase, triangularTorusLocalAngularData,
        triangularTorusLocalPortRoot, triangularTorusLocalPortOrder_rank] using
          triangularSplit_exit_phase rho hrho a b hrankD
    · have herank := (kwOrderedDartPortSplitGraph_adj
          (triangularTorusGraph L) (triangularTorusLocalPortOrder L)
          e.fst e.snd).mp e.adj |>.resolve_left he |>.2
      have hrankE : (triangularTorusDirectionRank b).val + 1 =
            (triangularTorusDirectionRank c).val ∨
          (triangularTorusDirectionRank c).val + 1 =
            (triangularTorusDirectionRank b).val := by
        simpa [triangularTorusLocalPortOrder_rank, heb, hec] using herank
      have hmono :
          ((triangularTorusDirectionRank a).val <
              (triangularTorusDirectionRank b).val ∧
            (triangularTorusDirectionRank b).val <
              (triangularTorusDirectionRank c).val) ∨
          ((triangularTorusDirectionRank b).val <
              (triangularTorusDirectionRank a).val ∧
            (triangularTorusDirectionRank c).val <
              (triangularTorusDirectionRank b).val) := by
        fin_cases a <;> fin_cases b <;> fin_cases c <;>
          simp [triangularTorusDirectionRank,
            triangularTorusSplitDartDirection,
            triangularTorusSplitInternalDirection, hd, he, hda, hdb,
            heb, hec, triangularTorusSplitIncreasingDirection,
            triangularTorusDirectionReverse] at hrankD hrankE hdirne ⊢ <;>
          tauto
      simpa [kwPhaseGauge, triangularTorusSplitPhaseGauge,
        triangularTorusSplitDartDirection, hd, he, hda, hdb, heb, hec,
        kwLocalAngularSplitPhase, triangularTorusLocalAngularData,
        triangularTorusLocalPortRoot, triangularTorusLocalPortOrder_rank] using
          triangularSplit_internal_phase rho hrho a b c hrankD hrankE hmono

theorem triangularTorusSplitEmbedCycleDartLoop
    (L : Nat) [Fact (2 < L)]
    {root : KWDartPort (triangularTorusGraph L)}
    (p : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Walk root root)
    (k : Fin p.darts.length) :
    let hlen : (triangularTorusSplitEmbedWalk L p).darts.length =
        p.darts.length := by
      simpa only [SimpleGraph.Walk.length_darts] using
        (SimpleGraph.Walk.length_map
          (triangularTorusSplitEmbedHom L) p)
    kwGraphCycleDartLoop (triangularTorusSplitEmbedWalk L p)
        (Fin.cast hlen.symm k) =
      (triangularTorusSplitEmbedHom L).mapDart
        (kwGraphCycleDartLoop p k) := by
  dsimp only
  unfold kwGraphCycleDartLoop triangularTorusSplitEmbedWalk
  rw [List.get_eq_getElem, List.get_eq_getElem]
  calc
    (SimpleGraph.Walk.map (triangularTorusSplitEmbedHom L) p).darts[(Fin.cast _ k).val] =
        (p.darts.map (triangularTorusSplitEmbedHom L).mapDart)[k.val] := by
      apply getElem_congr
        (SimpleGraph.Walk.darts_map (triangularTorusSplitEmbedHom L) p)
        rfl
    _ = (triangularTorusSplitEmbedHom L).mapDart p.darts[k.val] := by
      rw [List.getElem_map]



theorem triangularTorusSplit_cyclePhaseProduct_eq_refined
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    (hrho : rho ^ 4 = Complex.I)
    {root : KWDartPort (triangularTorusGraph L)}
    (p : (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
      (triangularTorusLocalPortOrder L)).Walk root root)
    (hp : p.IsCycle) :
    let q := triangularTorusSplitEmbedWalk L p
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    letI : NeZero q.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr
          (triangularTorusSplitEmbedWalk_isCycle L p hp).not_nil))⟩
    kwLoopPhaseProduct
        (kwLocalAngularSplitPhase
          (triangularTorusLocalAngularData L rho hrho))
        (kwGraphCycleDartLoop p) =
      kwLoopPhaseProduct (triangularTorusGraphPhase (3 * L) rho 1 1)
        (kwGraphCycleDartLoop q) := by
  let q := triangularTorusSplitEmbedWalk L p
  have hqcycle := triangularTorusSplitEmbedWalk_isCycle L p hp
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  letI : NeZero q.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hqcycle.not_nil))⟩
  let localPhase := kwLocalAngularSplitPhase
    (triangularTorusLocalAngularData L rho hrho)
  let gaugedPhase := kwPhaseGauge
    (triangularTorusSplitPhaseGauge L rho) localPhase
  let refinedPhase := triangularTorusGraphPhase (3 * L) rho 1 1
  have hgauge : kwLoopPhaseProduct gaugedPhase (kwGraphCycleDartLoop p) =
      kwLoopPhaseProduct localPhase (kwGraphCycleDartLoop p) := by
    calc
      kwLoopPhaseProduct gaugedPhase (kwGraphCycleDartLoop p) =
          kwGraphLoopScalar _ gaugedPhase (kwGraphCycleDartLoop p) :=
        (kwGraphCycleDartLoop_scalar_eq_phaseProduct _ gaugedPhase p hp).symm
      _ = kwGraphLoopScalar _ localPhase (kwGraphCycleDartLoop p) :=
        kwGraphLoopScalar_phaseGauge _ localPhase
          (triangularTorusSplitPhaseGauge L rho)
          (triangularTorusSplitPhaseGauge_ne_zero L rho hrho)
          (kwGraphCycleDartLoop p)
      _ = kwLoopPhaseProduct localPhase (kwGraphCycleDartLoop p) :=
        kwGraphCycleDartLoop_scalar_eq_phaseProduct _ localPhase p hp
  have hlen : q.darts.length = p.darts.length := by
    simpa only [q, triangularTorusSplitEmbedWalk,
      SimpleGraph.Walk.length_darts] using
      (SimpleGraph.Walk.length_map (triangularTorusSplitEmbedHom L) p)
  let E : Fin p.darts.length ≃ Fin q.darts.length :=
    (Fin.castOrderIso hlen.symm).toEquiv
  let targetFactor : Fin q.darts.length → Complex := fun k =>
    refinedPhase (kwGraphCycleDartLoop q k)
      (kwGraphCycleDartLoop q (k + 1))
  have hreindex : (∏ k : Fin p.darts.length, targetFactor (E k)) =
      ∏ k : Fin q.darts.length, targetFactor k :=
    Equiv.prod_comp E targetFactor
  have hfactor (k : Fin p.darts.length) :
      targetFactor (E k) = gaugedPhase
        (kwGraphCycleDartLoop p k) (kwGraphCycleDartLoop p (k + 1)) := by
    have hsucc : E k + 1 = E (k + 1) := by
      apply Fin.ext
      simp [E, Fin.val_add, hlen]
    have hloopk := triangularTorusSplitEmbedCycleDartLoop L p k
    change kwGraphCycleDartLoop q (E k) =
      (triangularTorusSplitEmbedHom L).mapDart
        (kwGraphCycleDartLoop p k) at hloopk
    have hloopSucc := triangularTorusSplitEmbedCycleDartLoop L p (k + 1)
    change kwGraphCycleDartLoop q (E (k + 1)) =
      (triangularTorusSplitEmbedHom L).mapDart
        (kwGraphCycleDartLoop p (k + 1)) at hloopSucc
    unfold targetFactor refinedPhase gaugedPhase localPhase E
    rw [hloopk, hsucc, hloopSucc]
    have hnb := kwGraphCycleDartLoop_nonbacktracking
      (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
        (triangularTorusLocalPortOrder L)) p hp k
    exact triangularTorusSplit_embedPhase_eq_phaseGauge
      L rho hrho _ _ hnb.1 hnb.2
  calc
    kwLoopPhaseProduct localPhase (kwGraphCycleDartLoop p) =
        kwLoopPhaseProduct gaugedPhase (kwGraphCycleDartLoop p) := hgauge.symm
    _ = ∏ k : Fin p.darts.length, targetFactor (E k) := by
      unfold kwLoopPhaseProduct
      exact (Finset.prod_congr rfl fun k _ => (hfactor k).symm)
    _ = ∏ k : Fin q.darts.length, targetFactor k := hreindex
    _ = kwLoopPhaseProduct refinedPhase (kwGraphCycleDartLoop q) := rfl



theorem triangularTorus_localAngularSplitShiftedCyclePhase
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    (hrho : rho ^ 4 = Complex.I) :
    KWLocalAngularSplitShiftedCyclePhase
      (triangularTorusLocalAngularData L rho hrho)
      (kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L))
      (triangularTorusSurfaceSpin 0 0) := by
  intro root p hp
  let q := triangularTorusSplitEmbedWalk L p
  have hq := triangularTorusSplitEmbedWalk_isCycle L p hp
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  letI : NeZero q.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hq.not_nil))⟩
  have htransfer := triangularTorusSplit_cyclePhaseProduct_eq_refined
    L rho hrho p hp
  dsimp only at htransfer
  have hnative := triangularTorus_cyclePhaseProduct_eq_neg_baseSpinSign_closed
    (3 * L) rho hrho q hq
  have hhom := triangularTorusSplitEmbedWalk_surfaceHomology L p
  calc
    kwLoopPhaseProduct
        (kwLocalAngularSplitPhase
          (triangularTorusLocalAngularData L rho hrho))
        (kwGraphCycleDartLoop p) =
        kwLoopPhaseProduct (triangularTorusGraphPhase (3 * L) rho 1 1)
          (kwGraphCycleDartLoop (triangularTorusSplitEmbedWalk L p)) :=
      htransfer
    _ = -(surfaceParitySign
          (surfaceQuadraticParity (triangularTorusSurfaceSpin 0 0)
            (surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass (3 * L))
              (triangularTorusSplitEmbedWalk L p).edges.toFinset)) : Complex) := by
      simpa only [q] using hnative
    _ = -surfaceSpinCycleCoefficient
        (kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L))
        (triangularTorusSurfaceSpin 0 0) p.edges.toFinset := by
      rw [hhom]
      rfl

end StatMech.FrontierA
