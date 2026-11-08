/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.FasterAPSP
import Batteries.Data.Vector.Lemmas
import Mathlib.Tactic.FinCases

/-! Ordinary-import consumers of all six frozen FASTER-APSP roles. -/

set_option autoImplicit false
universe u

open Cslib.Algorithms.Lean.Matrix

namespace FasterAPSPAPITests

#check @fasterAPSP
#check @fasterAPSP_ret
#check @fasterAPSP_edgeBounded
#check @fasterAPSP_distance_spec
#check @fasterAPSP_time
#check @fasterAPSP_time_isTheta

example {α : Type u} [Add α] [Mul α] [Zero α] {n : Nat}
    (W : Vector (Vector α n) n) :
    Cslib.Algorithms.Lean.TimeM (Nat × (Nat × Nat)) (Vector (Vector α n) n) :=
  fasterAPSP W

example {α : Type u} [Semiring α] {n : Nat} (W : Vector (Vector α n) n) :
    Matrix.of (fun i j => ((fasterAPSP W).ret.get i).get j) =
      Matrix.of (fun i j => (W.get i).get j) ^ (2 ^ Nat.clog 2 (n - 1)) :=
  fasterAPSP_ret W

example {α : Type u} [Add α] [Mul α] [Zero α] {n : Nat}
    (W : Vector (Vector α n) n) :
    (fasterAPSP W).time =
      (n ^ 2 + 2 * Nat.clog 2 (n - 1) * n ^ 2,
        (Nat.clog 2 (n - 1) * n ^ 3, Nat.clog 2 (n - 1) * n ^ 3)) :=
  fasterAPSP_time W

example {α : Type u} [Add α] [Mul α] [Zero α]
    (W : (n : Nat) → Vector (Vector α n) n) :
    Asymptotics.IsTheta Filter.atTop
      (fun n => ((fasterAPSP (W n)).time.1 +
        (fasterAPSP (W n)).time.2.1 + (fasterAPSP (W n)).time.2.2 : ℝ))
      (fun n => (n : ℝ) ^ 3 * Real.log (n : ℝ)) :=
  fasterAPSP_time_isTheta W

example {n : Nat} (W : Vector (Vector (MinTropical (WithTop Int)) n) n)
    (hdiag : ∀ i : Fin n, MinTropical.untrop ((W.get i).get i) = 0)
    (i j : Fin n) :
    Cslib.Algorithms.Lean.FloydWarshall.IsEdgeBoundedShortestPathWeight
      (Matrix.of fun x y => MinTropical.untrop ((W.get x).get y))
      (2 ^ Nat.clog 2 (n - 1)) i j
      (MinTropical.untrop (((fasterAPSP W).ret.get i).get j)) :=
  fasterAPSP_edgeBounded W hdiag i j

example {n : Nat} (W : Vector (Vector (MinTropical (WithTop Int)) n) n)
    (hdiag : ∀ i : Fin n, MinTropical.untrop ((W.get i).get i) = 0)
    (hNoCycle : Cslib.Algorithms.Lean.FloydWarshall.NoNegativeCycle
      (Matrix.of fun x y => MinTropical.untrop ((W.get x).get y)))
    (i j : Fin n) :
    Cslib.Algorithms.Lean.FloydWarshall.IsStageShortestPathWeight
      (Matrix.of fun x y => MinTropical.untrop ((W.get x).get y)) n i j
      (MinTropical.untrop (((fasterAPSP W).ret.get i).get j)) :=
  fasterAPSP_distance_spec W hdiag hNoCycle i j

example {α : Type u} [Add α] [Mul α] [Zero α]
    (W : Vector (Vector α 0) 0) : (fasterAPSP W).time = (0, (0, 0)) := by
  simpa using fasterAPSP_time W

example {α : Type u} [Add α] [Mul α] [Zero α]
    (W : Vector (Vector α 1) 1) : (fasterAPSP W).time = (1, (0, 0)) := by
  simpa using fasterAPSP_time W

example {α : Type u} [Add α] [Mul α] [Zero α]
    (W : Vector (Vector α 2) 2) : (fasterAPSP W).time = (4, (0, 0)) := by
  simpa using fasterAPSP_time W

private lemma zero_pathWeight {n : Nat} (path : List (Fin n)) :
    Cslib.Algorithms.Lean.FloydWarshall.pathWeight (fun _ _ => 0) path = 0 := by
  induction path with
  | nil => rfl
  | cons first rest ih =>
      cases rest with
      | nil => rfl
      | cons second tail =>
          simpa [Cslib.Algorithms.Lean.FloydWarshall.pathWeight] using ih

private lemma zero_noNegativeCycle {n : Nat} :
    Cslib.Algorithms.Lean.FloydWarshall.NoNegativeCycle (fun _ _ : Fin n => 0) := by
  rintro ⟨cycle, base, _, _, _, hnegative⟩
  rw [zero_pathWeight] at hnegative
  exact (lt_irrefl (0 : WithTop Int)) hnegative

example : Cslib.Algorithms.Lean.FloydWarshall.IsStageShortestPathWeight
    (Matrix.of fun _ _ : Fin 1 => (0 : WithTop Int)) 1 0 0
    (MinTropical.untrop
      (((fasterAPSP
        (#v[#v[MinTropical.trop (0 : WithTop Int)]] :
          Vector (Vector (MinTropical (WithTop Int)) 1) 1)).ret.get 0).get 0)) := by
  let W : Vector (Vector (MinTropical (WithTop Int)) 1) 1 :=
    #v[#v[MinTropical.trop (0 : WithTop Int)]]
  have hw : (Matrix.of fun x y : Fin 1 => MinTropical.untrop ((W.get x).get y)) =
      (Matrix.of fun _ _ : Fin 1 => (0 : WithTop Int)) := by
    funext x y
    fin_cases x
    fin_cases y
    simp [W, Vector.get_eq_getElem]
  have hdiag : ∀ i : Fin 1, MinTropical.untrop ((W.get i).get i) = 0 := by
    intro i
    fin_cases i
    simp [W, Vector.get_eq_getElem]
  have hNoCycle : Cslib.Algorithms.Lean.FloydWarshall.NoNegativeCycle
      (Matrix.of fun x y => MinTropical.untrop ((W.get x).get y)) := by
    rw [hw]
    exact zero_noNegativeCycle
  have hspec := fasterAPSP_distance_spec W hdiag hNoCycle 0 0
  rw [hw] at hspec
  exact hspec

private def negativeCycleInput : Vector (Vector (MinTropical (WithTop Int)) 3) 3 :=
  (#v[#v[0, -2, 2], #v[1, 0, ⊤], #v[⊤, ⊤, 0]] :
    Vector (Vector (WithTop Int) 3) 3).map fun row => row.map MinTropical.trop

example (i j : Fin 3) :
    Cslib.Algorithms.Lean.FloydWarshall.IsEdgeBoundedShortestPathWeight
      (Matrix.of fun x y => MinTropical.untrop ((negativeCycleInput.get x).get y))
      (2 ^ Nat.clog 2 (3 - 1)) i j
      (MinTropical.untrop (((fasterAPSP negativeCycleInput).ret.get i).get j)) := by
  apply fasterAPSP_edgeBounded
  intro vertex
  fin_cases vertex <;> simp [negativeCycleInput, Vector.get_eq_getElem]

end FasterAPSPAPITests
