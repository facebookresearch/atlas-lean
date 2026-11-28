/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.StrongConnectivityAugmentationDefs

namespace MetaMathlibExt.Complexity.NPComplete.StrongConnectivityAugmentation

open MetaMathlibExt.BitstringEncoding

/-- The path `0 → 1 → 2`, every ordered pair of weight `w`, and bound `1`. -/
private abbrev path (w : ℕ) : StrongConnectivityAugmentationInstance :=
  (3, [(0, 1), (1, 2)], [[w, w, w], [w, w, w], [w, w, w]], 1)

private theorem path_one_wellFormed : WellFormed (path 1) := by
  unfold WellFormed weight; decide

/-- `path 2` is well formed too. -/
example : WellFormed (path 2) := by unfold WellFormed weight; decide

/-- Adding the pair `(2, 0)` closes the cycle `0 → 1 → 2 → 0`. -/
private theorem cycle_adj :
    ∀ u : Fin 3, (arcDigraph 3 ([(0, 1), (1, 2)] ++ [(2, 0)])).Adj u (u + 1) := by
  have h : ∀ u : Fin 3, ((u : ℕ), ((u + 1 : Fin 3) : ℕ)) ∈ [(0, 1), (1, 2)] ++ [(2, 0)] := by
    decide
  exact h

/-- With weights `1` the single added pair `(2, 0)` of weight `1` makes the path strongly
connected. -/
private theorem path_one_feasible : StrongConnectivityAugmentationFeasible (path 1) := by
  refine ⟨[(2, 0)], by decide, by decide, fun u v => ?_⟩
  have hv : v = u ∨ v = u + 1 ∨ v = u + 1 + 1 := by revert u v; decide
  rcases hv with rfl | rfl | rfl
  · exact .refl
  · exact .single (cycle_adj u)
  · exact .tail (.single (cycle_adj u)) (cycle_adj (u + 1))

/-- Nothing but `2` is reachable from `2` along the path's own arcs. -/
private theorem from_two {x y : Fin 3}
    (h : Relation.ReflTransGen (arcDigraph 3 ([(0, 1), (1, 2)] ++ [])).Adj x y) :
    x = 2 → y = 2 := by
  induction h with
  | refl => exact id
  | tail _ hab ih =>
    intro hx
    obtain rfl := ih hx
    revert hab
    simp [arcDigraph]

/-- Every pair costs `2` in `path 2`. -/
private theorem path_two_weight :
    ∀ a < 3, ∀ b < 3, weight [[2, 2, 2], [2, 2, 2], [2, 2, 2]] a b = 2 := by decide

/-- With weights `2` and bound `1`, no pair can be added, and the path itself is not strongly
connected (`0` is unreachable from `2`). Only the weights differ from `path 1`. -/
private theorem path_two_infeasible : ¬ StrongConnectivityAugmentationFeasible (path 2) := by
  rintro ⟨A, hA, hw, hconn⟩
  cases A with
  | nil => exact absurd (from_two (hconn 2 0) rfl) (by decide)
  | cons a A =>
    have h := path_two_weight a.1 (hA a (by simp)).1 a.2 (hA a (by simp)).2
    simp only [List.map_cons, List.sum_cons] at hw
    change _ + _ ≤ 1 at hw
    omega

/-- A weight `0` is malformed. -/
example : ¬ WellFormed ((2, [], [[1, 0], [1, 1]], 1) : StrongConnectivityAugmentationInstance) := by
  unfold WellFormed weight; decide

/-- An arc that is a loop is malformed. -/
example : ¬ WellFormed ((2, [(1, 1)], [[1, 1], [1, 1]], 1) :
    StrongConnectivityAugmentationInstance) := by
  unfold WellFormed weight; decide

/-- The decision problem accepts the encoding of `path 1`. -/
example : strongConnectivityAugmentationDec (bitEncode (path 1)) = true := by
  simp [strongConnectivityAugmentationDec, path_one_wellFormed, path_one_feasible]

/-- It rejects the encoding of the well-formed but infeasible `path 2`. -/
example : strongConnectivityAugmentationDec (bitEncode (path 2)) = false := by
  simp [strongConnectivityAugmentationDec, path_two_infeasible]

/-- It rejects a lone continuation bit, which decodes to no instance. -/
example : strongConnectivityAugmentationDec [true] = false := by
  have h : bitDecode (α := StrongConnectivityAugmentationInstance) [true] = none := rfl
  simp [strongConnectivityAugmentationDec, h]

end MetaMathlibExt.Complexity.NPComplete.StrongConnectivityAugmentation
