/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusSplitPhaseGauge
import Code.FrontierA.SurfaceKacWardShiftedCycleAssembly









open scoped BigOperators

namespace StatMech.FrontierA

theorem triangularTorusSplitEmbed_phaseProduct
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
        (triangularTorusGraphPhase (3 * L) rho 1 1)
        (kwGraphCycleDartLoop q) =
      kwLoopPhaseProduct
        (kwPhaseGauge (triangularTorusSplitPhaseGauge L rho)
          (kwLocalAngularSplitPhase
            (triangularTorusLocalAngularData L rho hrho)))
        (kwGraphCycleDartLoop p) := by
  classical
  dsimp only
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let q := triangularTorusSplitEmbedWalk L p
  have hq : q.IsCycle := triangularTorusSplitEmbedWalk_isCycle L p hp
  letI : NeZero q.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hq.not_nil))⟩
  have hlen : q.darts.length = p.darts.length := by
    simpa only [SimpleGraph.Walk.length_darts] using
      (SimpleGraph.Walk.length_map (triangularTorusSplitEmbedHom L) p)
  unfold kwLoopPhaseProduct
  calc
    (∏ j : Fin q.darts.length,
        triangularTorusGraphPhase (3 * L) rho 1 1
          (kwGraphCycleDartLoop q j)
          (kwGraphCycleDartLoop q (j + 1))) =
        ∏ k : Fin p.darts.length,
          triangularTorusGraphPhase (3 * L) rho 1 1
            (kwGraphCycleDartLoop q
              ((Fin.castOrderIso hlen.symm) k))
            (kwGraphCycleDartLoop q
              ((Fin.castOrderIso hlen.symm) k + 1)) := by
      simpa only using
        (Equiv.prod_comp (Fin.castOrderIso hlen.symm).toEquiv
          (fun j : Fin q.darts.length ↦
            triangularTorusGraphPhase (3 * L) rho 1 1
              (kwGraphCycleDartLoop q j)
              (kwGraphCycleDartLoop q (j + 1)))).symm
    _ = ∏ k : Fin p.darts.length,
          kwPhaseGauge (triangularTorusSplitPhaseGauge L rho)
            (kwLocalAngularSplitPhase
              (triangularTorusLocalAngularData L rho hrho))
            (kwGraphCycleDartLoop p k)
            (kwGraphCycleDartLoop p (k + 1)) := by
      apply Finset.prod_congr rfl
      intro k _
      have hcast_add :
          (Fin.castOrderIso hlen.symm) k + 1 =
            (Fin.castOrderIso hlen.symm) (k + 1) := by
        apply Fin.ext
        have hwalkLen : q.length = p.length := by
          simpa only [SimpleGraph.Walk.length_darts] using hlen
        simp [Fin.val_add, hwalkLen]
      rw [hcast_add]
      have hmap (j : Fin p.darts.length) :
          kwGraphCycleDartLoop q ((Fin.castOrderIso hlen.symm) j) =
            (triangularTorusSplitEmbedHom L).mapDart
              (kwGraphCycleDartLoop p j) := by
        dsimp only [q]
        exact triangularTorusSplitEmbedCycleDartLoop L p j
      rw [hmap k, hmap (k + 1)]
      exact triangularTorusSplit_refinedPhase_eq_gauge L rho hrho
        (kwGraphCycleDartLoop p k) (kwGraphCycleDartLoop p (k + 1))
        (kwGraphCycleDartLoop_nonbacktracking
          (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
            (triangularTorusLocalPortOrder L)) p hp k).1
        (kwGraphCycleDartLoop_nonbacktracking
          (kwOrderedDartPortSplitGraph (triangularTorusGraph L)
            (triangularTorusLocalPortOrder L)) p hp k).2



theorem triangularTorus_localAngularSplit_shiftedCyclePhase
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    (hrho : rho ^ 4 = Complex.I) :
    KWLocalAngularSplitShiftedCyclePhase
      (triangularTorusLocalAngularData L rho hrho)
      (kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L))
      (triangularTorusSurfaceSpin 0 0) := by
  classical
  intro root p hp
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let split := kwOrderedDartPortSplitGraph (triangularTorusGraph L)
    (triangularTorusLocalAngularData L rho hrho).order
  let localPhase := kwLocalAngularSplitPhase
    (triangularTorusLocalAngularData L rho hrho)
  let gauge := triangularTorusSplitPhaseGauge L rho
  let q := triangularTorusSplitEmbedWalk L p
  have hq : q.IsCycle := triangularTorusSplitEmbedWalk_isCycle L p hp
  letI : NeZero q.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hq.not_nil))⟩
  have hgauge := kwGraphLoopScalar_phaseGauge split localPhase gauge
    (triangularTorusSplitPhaseGauge_ne_zero L rho hrho)
    (kwGraphCycleDartLoop p)
  rw [kwGraphCycleDartLoop_scalar_eq_phaseProduct split
      (kwPhaseGauge gauge localPhase) p hp,
    kwGraphCycleDartLoop_scalar_eq_phaseProduct split localPhase p hp]
      at hgauge
  have htransport := triangularTorusSplitEmbed_phaseProduct L rho hrho p hp
  have hnative :=
    triangularTorus_cyclePhaseProduct_eq_neg_baseSpinSign_closed
      (3 * L) rho hrho q hq
  have hhomology := triangularTorusSplitEmbedWalk_surfaceHomology L p
  calc
    kwLoopPhaseProduct localPhase (kwGraphCycleDartLoop p) =
        kwLoopPhaseProduct (kwPhaseGauge gauge localPhase)
          (kwGraphCycleDartLoop p) := hgauge.symm
    _ = kwLoopPhaseProduct
          (triangularTorusGraphPhase (3 * L) rho 1 1)
          (kwGraphCycleDartLoop q) := htransport.symm
    _ = -(surfaceParitySign
          (surfaceQuadraticParity (triangularTorusSurfaceSpin 0 0)
            (surfaceSubgraphHomology
              (triangularTorusSurfaceEdgeClass (3 * L))
              q.edges.toFinset)) : Complex) := hnative
    _ = -surfaceSpinCycleCoefficient
          (kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L))
          (triangularTorusSurfaceSpin 0 0) p.edges.toFinset := by
      unfold surfaceSpinCycleCoefficient
      dsimp only [q]
      rw [hhomology]
      rfl

end StatMech.FrontierA
