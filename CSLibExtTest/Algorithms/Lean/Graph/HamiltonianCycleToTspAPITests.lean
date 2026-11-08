/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Graph.HamiltonianCycleToTsp

open Cslib.Algorithms.Lean.Graph

namespace HamiltonianCycleToTspAPITests

#check @hamiltonianCycleToTsp
#check @hamiltonianCycleToTsp_size
#check @hamiltonianCycleToTsp_getElem?
#check @hamiltonianCycleToTsp_costs
#check @hamiltonianCycleToTsp_time
#check @hamiltonianCycleToTsp_forward
#check @hamiltonianCycleToTsp_reverse
#check @hamiltonianCycleToTsp_iff

example (x : Array Bool) :
  (hamiltonianCycleToTsp x).ret.size = x.size := by
  exact hamiltonianCycleToTsp_size x

example (x : Array Bool) (n : Nat) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
  (∀ k : Nat, (hamiltonianCycleToTsp x).ret[k]? = x[k]?.map Bool.not) ∧
  (x.size = n * n →
    (∀ i j : Fin n, x[i.val * n + j.val]? = some (decide (G.Adj i j))) →
    (∀ i j : Fin n,
      ((hamiltonianCycleToTsp x).ret[i.val * n + j.val]?).map Bool.toNat =
        some (if G.Adj i j then 0 else 1)) ∧
    (∀ i : Fin n, ((hamiltonianCycleToTsp x).ret[i.val * n + i.val]?).map Bool.toNat = some 1) ∧
    (∀ i j : Fin n,
      (hamiltonianCycleToTsp x).ret[i.val * n + j.val]? =
        (hamiltonianCycleToTsp x).ret[j.val * n + i.val]?)) := by
  refine ⟨fun k => hamiltonianCycleToTsp_getElem? x k, ?_⟩
  intro hsize henc
  exact hamiltonianCycleToTsp_costs x n G hsize henc

example (x : Array Bool) :
  (hamiltonianCycleToTsp x).time = 2 * x.size := by
  exact hamiltonianCycleToTsp_time x

example (x : Array Bool) (n : Nat) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
  x.size = n * n →
  (∀ i j : Fin n, x[i.val * n + j.val]? = some (decide (G.Adj i j))) →
  ∀ (a : Fin n) (p : G.Walk a a), p.IsHamiltonianCycle →
    (p.mapLe (show G ≤ SimpleGraph.completeGraph (Fin n) from le_top)).IsHamiltonianCycle ∧
    (p.mapLe (show G ≤ SimpleGraph.completeGraph (Fin n) from le_top)).support = p.support ∧
    ∃ costs : List Nat,
      (p.mapLe (show G ≤ SimpleGraph.completeGraph (Fin n) from le_top)).darts.mapM
        (fun d => ((hamiltonianCycleToTsp x).ret[d.fst.val * n + d.snd.val]?).map Bool.toNat) =
          some costs ∧ costs.sum = 0 := by
  intro hsize henc a p hp
  exact hamiltonianCycleToTsp_forward x n G hsize henc a p hp

example (x : Array Bool) (n : Nat) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
  x.size = n * n →
  (∀ i j : Fin n, x[i.val * n + j.val]? = some (decide (G.Adj i j))) →
  ∀ (a : Fin n) (p : (SimpleGraph.completeGraph (Fin n)).Walk a a),
    p.IsHamiltonianCycle →
    (∃ costs : List Nat,
      p.darts.mapM (fun d =>
        ((hamiltonianCycleToTsp x).ret[d.fst.val * n + d.snd.val]?).map Bool.toNat) =
        some costs ∧ costs.sum ≤ 0) →
    ∃ q : G.Walk a a, q.IsHamiltonianCycle ∧ q.support = p.support := by
  intro hsize henc a p hp hcost
  exact hamiltonianCycleToTsp_reverse x n G hsize henc a p hp hcost

example (x : Array Bool) (n : Nat) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
  x.size = n * n →
  (∀ i j : Fin n, x[i.val * n + j.val]? = some (decide (G.Adj i j))) →
  ((∃ (a : Fin n) (p : G.Walk a a), p.IsHamiltonianCycle) ↔
    ∃ (a : Fin n) (p : (SimpleGraph.completeGraph (Fin n)).Walk a a),
      p.IsHamiltonianCycle ∧ ∃ costs : List Nat,
        p.darts.mapM (fun d =>
          ((hamiltonianCycleToTsp x).ret[d.fst.val * n + d.snd.val]?).map Bool.toNat) =
          some costs ∧ costs.sum ≤ 0) := by
  intro hsize henc
  exact hamiltonianCycleToTsp_iff x n G hsize henc

end HamiltonianCycleToTspAPITests
