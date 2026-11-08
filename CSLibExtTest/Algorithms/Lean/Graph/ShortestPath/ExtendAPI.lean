/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.Extend

import Batteries.Data.Vector.Lemmas

/-!
# Ordinary-import shortest-path extension API checks

The infinity-initialized source call uses tropical zero, not underlying
integer zero. These examples consume the public API without import-all.
-/

set_option autoImplicit false

namespace CSLibExtTest.Algorithms.Lean.Graph.ShortestPath.Extend

open Cslib.Algorithms.Lean.Matrix

example {n : Nat}
    (A B : Vector (Vector (MinTropical (WithTop Int)) n) n) (i j : Fin n) :
    MinTropical.untrop (((matrixAccumulate A B
      (Vector.replicate n (Vector.replicate n 0))).ret.get i).get j) =
      Finset.univ.inf fun k : Fin n =>
        MinTropical.untrop ((A.get i).get k) + MinTropical.untrop ((B.get k).get j) := by
  simpa [Vector.get_eq_getElem] using
    matrixAccumulate_minPlus_apply A B (Vector.replicate n (Vector.replicate n 0)) i j

example {n : Nat} (A B : Vector (Vector (MinTropical (WithTop Int)) n) n) :
    Matrix.of (fun i j => ((matrixAccumulate A B
      (Vector.replicate n (Vector.replicate n 0))).ret.get i).get j) =
      Matrix.of (fun i k => (A.get i).get k) *
        Matrix.of (fun k j => (B.get k).get j) := by
  have hzero : Matrix.of (fun i j =>
      (((Vector.replicate n (Vector.replicate n (0 : MinTropical (WithTop Int)))).get i).get j)) =
      (0 : Matrix (Fin n) (Fin n) (MinTropical (WithTop Int))) := by
    funext i j
    simp [Vector.get_eq_getElem]
  have h := matrixAccumulate_ret A B (Vector.replicate n (Vector.replicate n 0))
  rw [hzero] at h
  simpa using h

example {n : Nat} (A B C : Vector (Vector (MinTropical (WithTop Int)) n) n) :
    (matrixAccumulate A B C).time = (n ^ 3, n ^ 3) := by
  exact matrixAccumulate_time A B C

example : (matrixAccumulate
    (#v[] : Vector (Vector (MinTropical (WithTop Int)) 0) 0) #v[] #v[]).time = (0, 0) := by
  simpa using matrixAccumulate_time
    (#v[] : Vector (Vector (MinTropical (WithTop Int)) 0) 0) #v[] #v[]

example {n : Nat} (weight : Matrix (Fin n) (Fin n) (WithTop Int)) (i : Fin n) :
    ¬Cslib.Algorithms.Lean.FloydWarshall.IsEdgeBoundedShortestPathWeight weight 0 i i ⊤ := by
  intro h
  have hbound := h.1 [i]
    (by simp [Cslib.Algorithms.Lean.FloydWarshall.IsWeightedPath]) (by simp)
  simp [Cslib.Algorithms.Lean.FloydWarshall.pathWeight] at hbound

example (i : Fin 1) :
    Cslib.Algorithms.Lean.FloydWarshall.IsEdgeBoundedShortestPathWeight
      (0 : Matrix (Fin 1) (Fin 1) (WithTop Int)) 0 i i 0 := by
  constructor
  · intro path hpath hbound
    cases path with
    | nil => exact False.elim (hpath.ne_nil rfl)
    | cons first tail =>
        cases tail with
        | nil => simp [Cslib.Algorithms.Lean.FloydWarshall.pathWeight]
        | cons second rest => simp at hbound
  · right
    refine ⟨[i], ?_, by simp, ?_⟩
    · simp [Cslib.Algorithms.Lean.FloydWarshall.IsWeightedPath]
    · simp [Cslib.Algorithms.Lean.FloydWarshall.pathWeight]

example (i : Fin 1) :
    ¬Cslib.Algorithms.Lean.FloydWarshall.IsEdgeBoundedShortestPathWeight
      (0 : Matrix (Fin 1) (Fin 1) (WithTop Int)) 0 i i (-1) := by
  intro h
  rcases h.2 with htop | ⟨path, hpath, hbound, hweight⟩
  · exact WithTop.coe_ne_top htop
  · cases path with
    | nil => exact False.elim (hpath.ne_nil rfl)
    | cons first tail =>
        cases tail with
        | nil =>
            have hne : (0 : WithTop Int) ≠ -1 := by decide
            exact hne (by simpa [Cslib.Algorithms.Lean.FloydWarshall.pathWeight] using hweight)
        | cons second rest => simp at hbound

example {n r : Nat} (A B : Vector (Vector (MinTropical (WithTop Int)) n) n)
    (hdiag : ∀ j : Fin n, MinTropical.untrop ((B.get j).get j) = 0)
    (hprevious : ∀ i j : Fin n,
      Cslib.Algorithms.Lean.FloydWarshall.IsEdgeBoundedShortestPathWeight
        (Matrix.of fun x y => MinTropical.untrop ((B.get x).get y))
        r i j (MinTropical.untrop ((A.get i).get j)))
    (i j : Fin n) :
    Cslib.Algorithms.Lean.FloydWarshall.IsEdgeBoundedShortestPathWeight
      (Matrix.of fun x y => MinTropical.untrop ((B.get x).get y))
      (r + 1) i j
      (MinTropical.untrop (((matrixAccumulate A B
        (Vector.replicate n (Vector.replicate n 0))).ret.get i).get j)) := by
  exact matrixAccumulate_edgeBounded A B hdiag hprevious i j

end CSLibExtTest.Algorithms.Lean.Graph.ShortestPath.Extend
