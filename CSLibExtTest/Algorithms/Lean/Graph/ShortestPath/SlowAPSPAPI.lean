/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Graph.ShortestPath.SlowAPSP
import Batteries.Data.Vector.Lemmas

/-!
# Ordinary public SLOW-APSP consumers

These examples require no import-all or supplied correctness certificate.
-/

set_option autoImplicit false

open Cslib.Algorithms.Lean

namespace U086OrdinaryConsumer

private abbrev Weight := MinTropical (WithTop Int)
private abbrev Table (n : Nat) := Vector (Vector Weight n) n

example {n : Nat} (W L0 : Table n) :
    Matrix.of (fun i j =>
      ((Matrix.slowAPSP W L0).ret.get i).get j) =
      Matrix.of (fun i j => (L0.get i).get j) *
        Matrix.of (fun i j => (W.get i).get j) ^ (n - 1) :=
  Matrix.slowAPSP_ret W L0

example {n : Nat} (W L0 : Table n) :
    (Matrix.slowAPSP W L0).time =
      (n ^ 2 + 2 * (n - 1) * n ^ 2,
        ((n - 1) * n ^ 3, (n - 1) * n ^ 3)) :=
  Matrix.slowAPSP_time W L0

example (W L0 : (n : Nat) → Table n) :
    Asymptotics.IsTheta Filter.atTop
      (fun n => ((Matrix.slowAPSP (W n) (L0 n)).time.1 +
        (Matrix.slowAPSP (W n) (L0 n)).time.2.1 +
        (Matrix.slowAPSP (W n) (L0 n)).time.2.2 : ℝ))
      (fun n => (n : ℝ) ^ 4) :=
  Matrix.slowAPSP_time_isTheta W L0

example (W L0 : Table 0) :
    (Matrix.slowAPSP W L0).ret = #v[] := by
  apply Vector.ext
  intro i hi
  omega

example (W L0 : Table 0) :
    (Matrix.slowAPSP W L0).time = (0, (0, 0)) := by
  simpa using Matrix.slowAPSP_time W L0

example (W L0 : Table 1) :
    (Matrix.slowAPSP W L0).ret = L0 := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  have hi0 : i = 0 := by omega
  have hj0 : j = 0 := by omega
  subst i
  subst j
  let fi : Fin 1 := ⟨0, hi⟩
  let fj : Fin 1 := ⟨0, hj⟩
  have h := congrFun (congrFun (Matrix.slowAPSP_ret W L0) fi) fj
  simpa [fi, fj, Vector.get_eq_getElem] using h

example (W L0 : Table 1) :
    (Matrix.slowAPSP W L0).time = (1, (0, 0)) := by
  simpa using Matrix.slowAPSP_time W L0

example (W : Table 1) :
    (Matrix.slowAPSP W #v[#v[MinTropical.trop (7 : WithTop Int)]]).ret =
      #v[#v[MinTropical.trop (7 : WithTop Int)]] := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  have hi0 : i = 0 := by omega
  have hj0 : j = 0 := by omega
  subst i
  subst j
  let fi : Fin 1 := ⟨0, hi⟩
  let fj : Fin 1 := ⟨0, hj⟩
  have h := congrFun
    (congrFun (Matrix.slowAPSP_ret W
      #v[#v[MinTropical.trop (7 : WithTop Int)]]) fi) fj
  simpa [fi, fj, Vector.get_eq_getElem] using h

example {n : Nat} (W L0 : Table n)
    (hdiag : ∀ i : Fin n, MinTropical.untrop ((W.get i).get i) = 0)
    (hinit : ∀ i j : Fin n,
      MinTropical.untrop ((L0.get i).get j) = if i = j then 0 else ⊤)
    (hNoCycle : FloydWarshall.NoNegativeCycle
      (Matrix.of fun x y => MinTropical.untrop ((W.get x).get y)))
    (i j : Fin n) (path : List (Fin n))
    (hpath : FloydWarshall.IsWeightedPath
      (Matrix.of fun x y => MinTropical.untrop ((W.get x).get y)) i j path) :
    MinTropical.untrop (((Matrix.slowAPSP W L0).ret.get i).get j) ≤
      FloydWarshall.pathWeight
        (Matrix.of fun x y => MinTropical.untrop ((W.get x).get y)) path := by
  apply (Matrix.slowAPSP_distance_spec W L0 hdiag hinit hNoCycle i j).1 path hpath
  intro vertex _
  exact vertex.isLt

#check @Matrix.slowAPSP

example {n : Nat} (W L0 : Table n)
    (hdiag : ∀ i : Fin n, MinTropical.untrop ((W.get i).get i) = 0)
    (hinit : ∀ i j : Fin n,
      MinTropical.untrop ((L0.get i).get j) = if i = j then 0 else ⊤)
    (i j : Fin n) :
    FloydWarshall.IsEdgeBoundedShortestPathWeight
      (Matrix.of fun x y => MinTropical.untrop ((W.get x).get y))
      (n - 1) i j
      (MinTropical.untrop (((Matrix.slowAPSP W L0).ret.get i).get j)) :=
  Matrix.slowAPSP_edgeBounded W L0 hdiag hinit i j

example {n : Nat} (W L0 : Table n)
    (hdiag : ∀ i : Fin n, MinTropical.untrop ((W.get i).get i) = 0)
    (hinit : ∀ i j : Fin n,
      MinTropical.untrop ((L0.get i).get j) = if i = j then 0 else ⊤)
    (hNoCycle : FloydWarshall.NoNegativeCycle
      (Matrix.of fun x y => MinTropical.untrop ((W.get x).get y)))
    (i j : Fin n) :
    FloydWarshall.IsStageShortestPathWeight
      (Matrix.of fun x y => MinTropical.untrop ((W.get x).get y))
      n i j
      (MinTropical.untrop (((Matrix.slowAPSP W L0).ret.get i).get j)) :=
  Matrix.slowAPSP_distance_spec W L0 hdiag hinit hNoCycle i j

end U086OrdinaryConsumer
