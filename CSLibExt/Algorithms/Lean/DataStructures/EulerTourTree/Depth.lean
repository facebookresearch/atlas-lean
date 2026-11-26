/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.EulerTourTree

/-!
# Depth-annotated Euler tours

`Tree.depthTour d t` is the Euler tour `Tree.tour t` of
`CSLibExt.Algorithms.Lean.DataStructures.EulerTourTree` with every entry paired
with the depth of its vertex, where the root of `t` has depth `d` and the
children of a vertex of depth `k` have depth `k + 1`. A vertex is recorded on
entry and again after each child subtree, both times at its own depth.

`Tree.depthTourAux` builds the tour with an accumulator, as `Tree.tourAux`
does, so each output entry is constructed once. `Tree.depthTour_node` is the
characteristic node equation, `Tree.map_fst_depthTour` recovers `Tree.tour`
by forgetting the depths, and `Tree.depthTour_length_add_one` shows that a
tree with `n` vertices has a depth-annotated tour with `2 * n - 1` entries.

The reduction of lowest common ancestors to range-minimum queries over this
sequence is not formalized here.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

namespace EulerTourTree

namespace Tree

variable {V : Type u}

/-- Accumulator depth-annotated Euler tour, with the root of the tree at depth
`d`: `depthTourAux t d acc = depthTour d t ++ acc` (see `depthTourAux_eq`). -/
def depthTourAux : Tree V → Nat → List (V × Nat) → List (V × Nat)
  | .node r cs, d, acc =>
      (r, d) :: cs.foldr (fun c acc => depthTourAux c (d + 1) ((r, d) :: acc)) acc

/-- The Euler tour of `t` with every vertex paired with its depth, the root of
`t` having depth `d`. -/
def depthTour (d : Nat) (t : Tree V) : List (V × Nat) :=
  depthTourAux t d []

/-- The accumulator tour is the depth-annotated tour followed by the
accumulator. -/
theorem depthTourAux_eq (t : Tree V) (d : Nat) (acc : List (V × Nat)) :
    depthTourAux t d acc = depthTour d t ++ acc := by
  induction t using Tree.children_ind generalizing d acc with
  | node r cs ih =>
      have hfold : ∀ (cs : List (Tree V)) (acc : List (V × Nat)),
          (∀ c ∈ cs, ∀ d acc, depthTourAux c d acc = depthTour d c ++ acc) →
          cs.foldr (fun c acc => depthTourAux c (d + 1) ((r, d) :: acc)) acc =
            cs.flatMap (fun c => depthTour (d + 1) c ++ [(r, d)]) ++ acc := by
        intro cs
        induction cs with
        | nil => intro acc _; rfl
        | cons c cs ihl =>
            intro acc h
            have hrest := ihl acc (fun x hx => h x (List.mem_cons_of_mem c hx))
            simp only [List.foldr_cons, List.flatMap_cons]
            rw [h c (by simp) (d + 1)
              ((r, d) :: cs.foldr (fun c acc => depthTourAux c (d + 1) ((r, d) :: acc)) acc),
              hrest]
            simp [List.append_assoc]
      have hnode : depthTour d (.node r cs) =
          (r, d) :: cs.flatMap (fun c => depthTour (d + 1) c ++ [(r, d)]) := by
        rw [depthTour, depthTourAux, hfold cs [] ih]
        simp
      rw [depthTourAux, hfold cs acc ih, hnode]
      simp

/-- Characteristic node equation for `depthTour`: the root at depth `d`, then
each child subtree at depth `d + 1` followed by the root again. -/
theorem depthTour_node (d : Nat) (r : V) (cs : List (Tree V)) :
    depthTour d (.node r cs) =
      (r, d) :: cs.flatMap (fun c => depthTour (d + 1) c ++ [(r, d)]) := by
  rw [depthTour, depthTourAux]
  congr 1
  induction cs with
  | nil => rfl
  | cons c cs ihl =>
      simp only [List.foldr_cons, List.flatMap_cons]
      rw [depthTourAux_eq, ihl]
      simp [List.append_assoc]

/-- Forgetting the depths of the depth-annotated tour gives the Euler tour. -/
theorem map_fst_depthTour (d : Nat) (t : Tree V) :
    (depthTour d t).map Prod.fst = tour t := by
  induction t using Tree.children_ind generalizing d with
  | node r cs ih =>
      rw [depthTour_node, tour_node, List.map_cons, List.map_flatMap]
      congr 1
      apply List.flatMap_congr
      intro c hc
      rw [List.map_append, ih c hc]
      rfl

/-- A tree with `n` vertices has a depth-annotated tour with `2 * n - 1`
entries, stated without truncated subtraction. -/
theorem depthTour_length_add_one (d : Nat) (t : Tree V) :
    (depthTour d t).length + 1 = 2 * size t := by
  have h := tour_length t
  have hp := size_pos t
  rw [← map_fst_depthTour d t, List.length_map] at h
  omega

end Tree

end EulerTourTree

end Cslib.Algorithms.Lean
