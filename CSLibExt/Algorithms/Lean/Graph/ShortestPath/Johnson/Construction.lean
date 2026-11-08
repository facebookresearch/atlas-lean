/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.Johnson.Basic
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.Johnson.Basic

/-!
# Private construction facts for integer Johnson shortest paths

Return-value and event-count facts for the fresh-source construction and row builder.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Johnson

open BellmanFord

private lemma sourceEdges_ret {n : Nat} (vertices : List (Fin n)) :
    (sourceEdges vertices).ret =
      vertices.map (fun vertex => (⟨Fin.last n, vertex.castSucc, 0⟩ : Edge (n + 1))) := by
  induction vertices with
  | nil => rfl
  | cons vertex rest induction => simp [sourceEdges, induction]

private lemma liftEdges_ret {n : Nat} (tail : List (Edge (n + 1))) (edges : List (Edge n)) :
    (liftEdges tail edges).ret = edges.map liftEdge ++ tail := by
  induction edges with
  | nil => rfl
  | cons edge rest induction => simp [liftEdges, induction]

private lemma augment_ret {n : Nat} (edges : List (Edge n)) :
    (augment edges).ret = edges.map liftEdge ++
      (List.finRange n).map (fun vertex => (⟨Fin.last n, vertex.castSucc, 0⟩ : Edge (n + 1))) := by
  simp [augment, sourceEdges_ret, liftEdges_ret]

private lemma buildVector_get {α : Type} (n : Nat) (action : Fin n → TimeM Nat α)
    (vertex : Fin n) : (buildVector n action).ret.get vertex = (action vertex).ret := by
  induction n with
  | zero => exact Fin.elim0 vertex
  | succ n induction =>
      refine Fin.lastCases ?_ (fun previous => ?_) vertex
      · simp only [buildVector, TimeM.ret_bind, TimeM.ret_pure]
        exact Vector.getElem_push_eq
      · simp only [buildVector, TimeM.ret_bind, TimeM.ret_pure]
        change ((buildVector n (fun vertex => action vertex.castSucc)).ret.push
          (action (Fin.last n)).ret)[previous.val] = (action previous.castSucc).ret
        rw [Vector.getElem_push_lt previous.isLt]
        exact induction (fun vertex => action vertex.castSucc) previous

private lemma buildVector_time_const {α : Type} (n : Nat) (action : Fin n → TimeM Nat α)
    (cost : Nat) (cost_eq : ∀ vertex, (action vertex).time = cost) :
    (buildVector n action).time = n * cost := by
  induction n with
  | zero => simp [buildVector]
  | succ n induction =>
      have previous := induction (fun vertex => action vertex.castSucc)
        (fun vertex => cost_eq vertex.castSucc)
      simp [buildVector, previous, cost_eq, Nat.add_mul]

end Cslib.Algorithms.Lean.Johnson
