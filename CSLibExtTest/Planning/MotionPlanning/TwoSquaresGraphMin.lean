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

example : polyLen [.s, .D, .P, .t] = 3 + Real.sqrt 5 := by
  simp only [polyLen, dist_sD, dist_DP, dist_Pt]
  ring

theorem backtrack_walk : IsWalk [.s, .A, .s, .D, .P, .t] :=
  ⟨rfl, rfl, ⟨by decide, adj_s_A⟩, ⟨by decide, VisAdj.symm adj_s_A⟩,
    ⟨by decide, adj_s_D⟩, ⟨by decide, adj_D_P⟩, ⟨by decide, adj_P_t⟩, trivial⟩

example : 3 + Real.sqrt 5 ≤ polyLen [.s, .A, .s, .D, .P, .t] :=
  min_eq.2 ⟨_, backtrack_walk, rfl⟩

example : ¬ IsWalk [.s, .C, .t] := fun h => not_adj_s_C h.2.2.1.2

example : ¬ visGraph.Adj .s .s := visGraph.loopless.irrefl _

example : ¬ IsWalk [.s, .s, .D, .P, .t] :=
  fun h => visGraph.loopless.irrefl _ h.2.2.1

example : ∃ p : visGraph.Walk .s .t, walkWeight p = 3 + Real.sqrt 5 := by
  have hwalk : IsWalk [.s, .D, .P, .t] :=
    ⟨rfl, rfl, ⟨by decide, adj_s_D⟩, ⟨by decide, adj_D_P⟩, ⟨by decide, adj_P_t⟩,
      trivial⟩
  obtain ⟨p, hp⟩ := exists_walk_of_isWalk hwalk
  refine ⟨p, ?_⟩
  show polyLen p.support = _
  rw [hp]
  simp only [polyLen, dist_sD, dist_DP, dist_Pt]
  ring

#print axioms min_eq
#print axioms adj_s_D
#print axioms adj_D_P
#print axioms min_eq_walk

end Cslib.Planning.MotionPlanning.TwoSquaresGraph

