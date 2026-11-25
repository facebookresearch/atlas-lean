/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.TwoSquaresGraphMin
public meta import CSLibExt.Planning.MotionPlanning.TwoSquaresGraphMin
public import Mathlib.Tactic.NormNum.RealSqrt

namespace Cslib.Planning.MotionPlanning.TwoSquaresGraph

example : VisAdj (coord .s) (coord .D) := adj_s_D
example : VisAdj (coord .s) (coord .A) := adj_s_A
example : VisAdj (coord .D) (coord .P) := adj_D_P
example : VisAdj (coord .P) (coord .t) := adj_P_t
example : ¬ VisAdj (coord .s) (coord .t) := not_adj_s_t
example : ¬ VisAdj (coord .s) (coord .C) := not_adj_s_C

example : PathShortening.polyLen ([.s, .D, .P, .t].map coord) = 3 + Real.sqrt 5 := by
  simp only [List.map_cons, List.map_nil, PathShortening.polyLen_cons_cons,
    PathShortening.polyLen_singleton, dist_sD, dist_DP, dist_Pt]
  ring

private def vg {a b : Vtx} (h : VisAdj (coord a) (coord b)) (hne : a ≠ b) :
    visGraph.Adj a b := ⟨hne, h⟩

def backtrack_walk : visGraph.Walk .s .t :=
  .cons (vg adj_s_A (by decide))
    (.cons (vg (VisAdj.symm adj_s_A) (by decide))
      (.cons (vg adj_s_D (by decide))
        (.cons (vg adj_D_P (by decide))
          (.cons (vg adj_P_t (by decide)) .nil))))

example : walkWeight backtrack_walk =
    PathShortening.polyLen ([.s, .A, .s, .D, .P, .t].map coord) := rfl

example : 3 + Real.sqrt 5 ≤ PathShortening.polyLen ([.s, .A, .s, .D, .P, .t].map coord) :=
  min_eq_walk.2 ⟨backtrack_walk, rfl⟩

example : ¬ visGraph.Adj .s .C := fun h => not_adj_s_C h.2

example : ¬ visGraph.Adj .s .s := visGraph.loopless.irrefl _

example : ∃ p : visGraph.Walk .s .t, walkWeight p = 3 + Real.sqrt 5 := by
  refine ⟨.cons (vg adj_s_D (by decide))
    (.cons (vg adj_D_P (by decide))
      (.cons (vg adj_P_t (by decide)) .nil)), ?_⟩
  show PathShortening.polyLen ([.s, .D, .P, .t].map coord) = _
  simp only [List.map_cons, List.map_nil, PathShortening.polyLen_cons_cons,
    PathShortening.polyLen_singleton, dist_sD, dist_DP, dist_Pt]
  ring

#print axioms adj_s_D
#print axioms adj_D_P
#print axioms min_eq_walk

end Cslib.Planning.MotionPlanning.TwoSquaresGraph
