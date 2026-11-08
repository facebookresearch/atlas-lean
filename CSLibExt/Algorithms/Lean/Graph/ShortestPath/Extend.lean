/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.FloydWarshall.Basic
public import CSLibExt.Algorithms.Lean.Matrix.Multiply
public import Mathlib.Algebra.Tropical.Basic

import Batteries.Data.Vector.Lemmas
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.FloydWarshall.Internal.Paths
import Mathlib.Algebra.Tropical.BigOperators
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Min-plus extension of shortest paths

The existing increasing `i-j-k` matrix accumulator implements CLRS, fourth
edition, Section 23.1, EXTEND-SHORTEST-PATHS on min-plus tropical scalars.
An arbitrary incoming accumulator is retained; the source caller initializes
it to tropical zero, whose underlying value is infinity.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.FloydWarshall

/-- `distance` is a lower bound for every weighted path with at most `r`
edges, and is either infinity or the weight of an attaining such path.
Paths may repeat vertices; no absence-of-negative-cycles hypothesis is needed. -/
@[expose] public def IsEdgeBoundedShortestPathWeight {n : Nat}
    (weight : Matrix (Fin n) (Fin n) (WithTop Int))
    (r : Nat) (i j : Fin n) (distance : WithTop Int) : Prop :=
  (∀ path, IsWeightedPath weight i j path → path.length - 1 ≤ r →
    distance ≤ pathWeight weight path) ∧
  (distance = ⊤ ∨ ∃ path, IsWeightedPath weight i j path ∧
    path.length - 1 ≤ r ∧ pathWeight weight path = distance)

/-- Characterize an edge-bounded shortest weight by universal lower bounds
and finite attainment, without unfolding the path specification. -/
public theorem isEdgeBoundedShortestPathWeight_iff {n : Nat}
    (weight : Matrix (Fin n) (Fin n) (WithTop Int))
    (r : Nat) (i j : Fin n) (distance : WithTop Int) :
    IsEdgeBoundedShortestPathWeight weight r i j distance ↔
      (∀ path, IsWeightedPath weight i j path → path.length - 1 ≤ r →
        distance ≤ pathWeight weight path) ∧
      (distance = ⊤ ∨ ∃ path, IsWeightedPath weight i j path ∧
        path.length - 1 ≤ r ∧ pathWeight weight path = distance) := by
  rfl

private lemma weightedPath_cons_cons_unsnoc {n : Nat}
    (weight : Matrix (Fin n) (Fin n) (WithTop Int))
    {source target first second : Fin n} (rest : List (Fin n))
    (hpath : IsWeightedPath weight source target (first :: second :: rest)) :
    ∃ pivot initial,
      IsWeightedPath weight source pivot initial ∧
      weight pivot target ≠ ⊤ ∧
      first :: second :: rest = initial ++ [target] := by
  induction rest generalizing source first second with
  | nil =>
      have hsource : first = source := by simpa using hpath.head_eq
      have htarget : second = target := by simpa using hpath.getLast_eq
      subst first
      subst second
      have hedge : weight source target ≠ ⊤ :=
        (List.isChain_cons_cons.mp hpath.isChain).1
      exact ⟨source, [source],
        Internal.weightedPath_singleton weight source, hedge, rfl⟩
  | cons third rest induction =>
      have hsource : first = source := by simpa using hpath.head_eq
      subst first
      have hedge : weight source second ≠ ⊤ :=
        (List.isChain_cons_cons.mp hpath.isChain).1
      have htail :
          IsWeightedPath weight second target (second :: third :: rest) :=
        hpath.of_cons_cons
      obtain ⟨pivot, initial, hinitial, hlast, hdecomp⟩ := induction htail
      refine ⟨pivot, source :: initial, hinitial.cons hedge, hlast, ?_⟩
      simpa using congrArg (List.cons source) hdecomp

private lemma edgeBounded_inf_add {n r : Nat}
    (weight previous : Matrix (Fin n) (Fin n) (WithTop Int))
    (hdiagonal : ∀ j : Fin n, weight j j = 0)
    (hprevious : ∀ i j : Fin n,
      IsEdgeBoundedShortestPathWeight weight r i j (previous i j))
    (i j : Fin n) :
    IsEdgeBoundedShortestPathWeight weight (r + 1) i j
      (Finset.univ.inf fun k : Fin n => previous i k + weight k j) := by
  constructor
  · intro path hpath hbound
    cases path with
    | nil => exact False.elim (hpath.ne_nil rfl)
    | cons first tail =>
        cases tail with
        | nil =>
            have hij : i = j := by
              simpa using hpath.head_eq.symm.trans hpath.getLast_eq
            subst j
            have hpreviousZero : previous i i ≤ 0 := by
              simpa [pathWeight] using
                (hprevious i i).1 [i]
                  (Internal.weightedPath_singleton weight i) (by simp)
            apply Finset.inf_le_of_le (Finset.mem_univ i)
            simpa [hdiagonal i, pathWeight] using hpreviousZero
        | cons second rest =>
            obtain ⟨k, initial, hinitial, hedge, hdecomp⟩ :=
              weightedPath_cons_cons_unsnoc weight rest hpath
            have hinitialBound : initial.length - 1 ≤ r := by
              have hbound' := hbound
              rw [hdecomp, List.length_append] at hbound'
              simp only [List.length_singleton, Nat.add_sub_cancel] at hbound'
              have hinitialPos := hinitial.length_pos
              omega
            have hpair : IsWeightedPath weight k j [k, j] :=
              Internal.weightedPath_pair weight hedge
            have hweight :
                pathWeight weight (first :: second :: rest) =
                  pathWeight weight initial + weight k j := by
              rw [hdecomp]
              simpa [pathWeight] using
                (Internal.pathWeight_append_tail weight hinitial hpair)
            apply Finset.inf_le_of_le (Finset.mem_univ k)
            calc
              previous i k + weight k j ≤
                  pathWeight weight initial + weight k j :=
                add_le_add_left
                  ((hprevious i k).1 initial hinitial hinitialBound) _
              _ = pathWeight weight (first :: second :: rest) := hweight.symm
  · by_cases htop :
        (Finset.univ.inf fun k : Fin n => previous i k + weight k j) = ⊤
    · exact Or.inl htop
    · right
      have huniv : (Finset.univ : Finset (Fin n)).Nonempty :=
        ⟨i, Finset.mem_univ i⟩
      obtain ⟨k, _, hk⟩ :=
        Finset.exists_mem_eq_inf (Finset.univ : Finset (Fin n)) huniv
          (fun k : Fin n => previous i k + weight k j)
      have hsum : previous i k + weight k j ≠ ⊤ := by
        rw [← hk]
        exact htop
      obtain ⟨hpreviousFinite, hedge⟩ := WithTop.add_ne_top.mp hsum
      rcases (hprevious i k).2 with hpreviousTop |
        ⟨initial, hinitial, hinitialBound, hinitialWeight⟩
      · exact False.elim (hpreviousFinite hpreviousTop)
      · have hpair : IsWeightedPath weight k j [k, j] :=
          Internal.weightedPath_pair weight hedge
        refine ⟨initial ++ [j], ?_, ?_, ?_⟩
        · simpa using Internal.weightedPath_append_tail weight hinitial hpair
        · have hinitialPos := hinitial.length_pos
          simp only [List.length_append, List.length_singleton]
          omega
        · calc
            pathWeight weight (initial ++ [j]) =
                pathWeight weight initial + weight k j := by
              simpa [pathWeight] using
                (Internal.pathWeight_append_tail weight hinitial hpair)
            _ = previous i k + weight k j := by rw [hinitialWeight]
            _ = Finset.univ.inf
                (fun k : Fin n => previous i k + weight k j) := hk.symm

end Cslib.Algorithms.Lean.FloydWarshall

namespace Cslib.Algorithms.Lean.Matrix

/-- Each actual min-plus output entry is the minimum of its saved accumulator
and every ordered candidate from the two unchanged input matrices. -/
public theorem matrixAccumulate_minPlus_apply {n : Nat}
    (A B C : _root_.Vector (_root_.Vector (MinTropical (WithTop Int)) n) n)
    (i j : Fin n) :
    MinTropical.untrop (((matrixAccumulate A B C).ret.get i).get j) =
      min (MinTropical.untrop ((C.get i).get j))
        (Finset.univ.inf fun k : Fin n =>
          MinTropical.untrop ((A.get i).get k) +
            MinTropical.untrop ((B.get k).get j)) := by
  have h := congrArg
    (fun M => MinTropical.untrop (M i j))
    (matrixAccumulate_ret A B C)
  simpa [Matrix.mul_apply, MinTropical.Finset.untrop_sum',
    Function.comp_def] using h

/-- With a zero diagonal and a previous at-most-`r`-edge distance matrix,
the actual infinity-initialized min-plus run returns at-most-`r+1`-edge
shortest weights. This includes repeated walks and signed edge weights. -/
public theorem matrixAccumulate_edgeBounded {n r : Nat}
    (A B : _root_.Vector (_root_.Vector (MinTropical (WithTop Int)) n) n)
    (hdiag : ∀ j : Fin n, MinTropical.untrop ((B.get j).get j) = 0)
    (hprevious : ∀ i j : Fin n,
      FloydWarshall.IsEdgeBoundedShortestPathWeight
        (Matrix.of fun x y => MinTropical.untrop ((B.get x).get y))
        r i j (MinTropical.untrop ((A.get i).get j)))
    (i j : Fin n) :
    FloydWarshall.IsEdgeBoundedShortestPathWeight
      (Matrix.of fun x y => MinTropical.untrop ((B.get x).get y))
      (r + 1) i j
      (MinTropical.untrop (((matrixAccumulate A B
        (Vector.replicate n (Vector.replicate n 0))).ret.get i).get j)) := by
  rw [matrixAccumulate_minPlus_apply]
  simpa [Vector.get_eq_getElem] using FloydWarshall.edgeBounded_inf_add
    (Matrix.of fun x y => MinTropical.untrop ((B.get x).get y))
    (Matrix.of fun x y => MinTropical.untrop ((A.get x).get y)) hdiag hprevious i j

end Cslib.Algorithms.Lean.Matrix
