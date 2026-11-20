/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusPeriodicPhase









namespace StatMech.FrontierA



def TriangularTorusZeroHomologyWinding (L : Nat) [Fact (2 < L)] : Prop :=
  ∀ {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle),
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass L)
        p.edges.toFinset = 0 →
      ∑ k, triangularIntStep
        (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k)) = 0



theorem triangularTorus_cyclePhaseProduct_eq_neg_baseSpinSign
    (L : Nat) [Fact (2 < L)]
    (rho : Complex) (hrho : rho ^ 4 = Complex.I)
    (hprimitive : TriangularTorusZeroHomologyWinding L)
    {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwLoopPhaseProduct (triangularTorusGraphPhase L rho 1 1)
        (kwGraphCycleDartLoop p) =
      -(surfaceParitySign
        (surfaceQuadraticParity (triangularTorusSurfaceSpin 0 0)
          (surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass L)
            p.edges.toFinset)) : Complex) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let h := surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass L)
    p.edges.toFinset
  rw [triangularTorus_baseSpinSign_eq_if_homology_zero h]
  by_cases hzero : h = 0
  · rw [if_pos hzero]
    exact triangularTorus_cyclePhaseProduct_eq_neg_one_of_closed
      L rho hrho p hp (hprimitive p hp hzero)
  · rw [if_neg hzero]
    simpa using triangularTorus_cyclePhaseProduct_eq_one_of_nonzeroHomology
      L rho hrho p hp hzero

end StatMech.FrontierA
