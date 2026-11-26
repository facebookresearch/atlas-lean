/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.Extend
public import Mathlib.Algebra.Order.Group.Int

import Batteries.Data.Vector.Lemmas

/-!
# Bounded min-plus matrix powers

The canonical matrix accumulator extends bounded walks by one edge. Its
arbitrary-power induction is shared by the saved-matrix APSP algorithms;
negative cycles are allowed in this bounded statement. No APSP executor,
alternative path carrier or unbounded shortest-path premise is introduced.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Matrix

open Cslib.Algorithms.Lean

private def vectorize {n : Nat}
    (M : Matrix (Fin n) (Fin n) (MinTropical (WithTop Int))) :
    Vector (Vector (MinTropical (WithTop Int)) n) n :=
  Vector.ofFn fun i => Vector.ofFn fun j => M i j

private lemma matrixAccumulate_vectorize_apply {n : Nat}
    (M : Matrix (Fin n) (Fin n) (MinTropical (WithTop Int)))
    (W : Vector (Vector (MinTropical (WithTop Int)) n) n)
    (i j : Fin n) :
    (((Matrix.matrixAccumulate (vectorize M) W
      (Vector.replicate n (Vector.replicate n 0))).ret.get i).get j) =
        (M * Matrix.of (fun x y => (W.get x).get y)) i j := by
  have h := congrArg (fun N => N i j)
    (Matrix.matrixAccumulate_ret (vectorize M) W
      (Vector.replicate n (Vector.replicate n 0)))
  have hM : Matrix.of (fun x y => M x y) = M := rfl
  simpa [vectorize, Vector.get_eq_getElem, hM] using h

private lemma identity_edgeBounded {n : Nat}
    (W L0 : Vector (Vector (MinTropical (WithTop Int)) n) n)
    (hinit : ∀ i j : Fin n,
      MinTropical.untrop ((L0.get i).get j) = if i = j then 0 else ⊤) :
    ∀ i j : Fin n,
      FloydWarshall.IsEdgeBoundedShortestPathWeight
        (Matrix.of fun x y => MinTropical.untrop ((W.get x).get y))
        0 i j (MinTropical.untrop ((L0.get i).get j)) := by
  intro i j
  constructor
  · intro path hpath hbound
    cases path with
    | nil => exact False.elim (hpath.ne_nil rfl)
    | cons first tail =>
        cases tail with
        | nil =>
            have hfirst : first = i := by simpa using hpath.head_eq
            subst first
            have hij : i = j := by simpa using hpath.getLast_eq
            subst j
            rw [hinit i i]
            simp [FloydWarshall.pathWeight]
        | cons second rest =>
            have : 1 ≤ (first :: second :: rest).length - 1 := by simp
            omega
  · by_cases hij : i = j
    · subst j
      right
      refine ⟨[i], List.isChainFromTo_singleton, by simp, ?_⟩
      simpa [FloydWarshall.pathWeight] using (hinit i i).symm
    · left
      simpa [hij] using hinit i j

private lemma matrixPower_edgeBounded {n : Nat}
    (W L0 : Vector (Vector (MinTropical (WithTop Int)) n) n)
    (hdiag : ∀ i : Fin n, MinTropical.untrop ((W.get i).get i) = 0)
    (hinit : ∀ i j : Fin n,
      MinTropical.untrop ((L0.get i).get j) = if i = j then 0 else ⊤)
    (r : Nat) :
    ∀ i j : Fin n,
      FloydWarshall.IsEdgeBoundedShortestPathWeight
        (Matrix.of fun x y => MinTropical.untrop ((W.get x).get y))
        r i j
        (MinTropical.untrop
          ((Matrix.of (fun x y => (L0.get x).get y) *
            (Matrix.of (fun x y => (W.get x).get y) :
              Matrix (Fin n) (Fin n) (MinTropical (WithTop Int))) ^ r) i j)) := by
  induction r with
  | zero =>
      simpa using identity_edgeBounded W L0 hinit
  | succ r induction =>
      intro i j
      let L : Matrix (Fin n) (Fin n) (MinTropical (WithTop Int)) :=
        Matrix.of (fun x y => (L0.get x).get y) *
          (Matrix.of (fun x y => (W.get x).get y) :
            Matrix (Fin n) (Fin n) (MinTropical (WithTop Int))) ^ r
      have hstep := Matrix.matrixAccumulate_edgeBounded
        (vectorize L) W hdiag (by
          intro x y
          simpa [L, vectorize, Vector.get_eq_getElem] using induction x y) i j
      rw [matrixAccumulate_vectorize_apply] at hstep
      simpa only [L, pow_succ, Matrix.mul_assoc] using hstep

/-- **Min-plus matrix powers give shortest path weights with at most $r$ edges.** Let $W$ be an
$n \times n$ matrix with entries in $\mathbb{Z} \cup \{\infty\}$, viewed in the min-plus
semiring, with $W_{ii} = 0$ for every $i$. Then for every natural number $r$ and all $i$ and $j$,
the entry $(W^r)_{ij}$ of the $r$-th min-plus power of $W$ is the shortest weight of a path from
$i$ to $j$ with at most $r$ edges for the weight matrix $W$.

Paths may repeat vertices. -/
public theorem matrix_pow_edgeBounded {n : Nat}
    (W : Matrix (Fin n) (Fin n) (MinTropical (WithTop Int)))
    (hdiag : ∀ i : Fin n, MinTropical.untrop (W i i) = 0)
    (r : Nat) (i j : Fin n) :
    FloydWarshall.IsEdgeBoundedShortestPathWeight
      (Matrix.of fun x y => MinTropical.untrop (W x y)) r i j
      (MinTropical.untrop ((W ^ r) i j)) := by
  have hinit : ∀ x y : Fin n,
      MinTropical.untrop (((vectorize (1 : Matrix (Fin n) (Fin n)
        (MinTropical (WithTop Int)))).get x).get y) =
        if x = y then 0 else ⊤ := by
    intro x y
    by_cases hxy : x = y
    · simp [vectorize, Vector.get_eq_getElem, Matrix.one_apply, hxy]
    · simp [vectorize, Vector.get_eq_getElem, Matrix.one_apply, hxy]
  have h := matrixPower_edgeBounded (vectorize W)
    (vectorize (1 : Matrix (Fin n) (Fin n) (MinTropical (WithTop Int))))
    (by simpa [vectorize, Vector.get_eq_getElem] using hdiag) hinit r i j
  have hid : Matrix.of (fun x y =>
      ((vectorize (1 : Matrix (Fin n) (Fin n)
        (MinTropical (WithTop Int)))).get x).get y) = 1 := by
    ext x y
    simp [vectorize, Vector.get_eq_getElem]
  have hW : Matrix.of (fun x y => ((vectorize W).get x).get y) = W := by
    ext x y
    simp [vectorize, Vector.get_eq_getElem]
  rw [hid, hW, one_mul] at h
  simpa [vectorize, Vector.get_eq_getElem] using h

end Cslib.Algorithms.Lean.Matrix
