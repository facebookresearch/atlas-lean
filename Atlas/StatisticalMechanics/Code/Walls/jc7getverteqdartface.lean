/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































































import Mathlib
import Code.Lattice.OrbitEncloses
import Code.Lattice.OrbitLoopBridge

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice





















theorem jc7_dartOrbitFaceWalk_getVert (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    (n k : ℕ) (hk : k ≤ n) :
    (dartOrbitFaceWalk K e he n).getVert k = dartFace ((dartNext K)^[k] e) := by
  have hk2 : k ≤ (dartOrbitFaceWalk K e he n).length := by
    rw [dartOrbitFaceWalk_length]; exact hk
  rw [SimpleGraph.Walk.getVert_eq_support_getElem _ hk2]
  rw [List.getElem_of_eq (dartOrbitFaceWalk_support K e he n)]
  · rw [List.getElem_map, List.getElem_range]













theorem jc7_dartOrbitFaceLoop_getVert (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (n : ℕ)
    (hn : n ≤ (dartNext_periodic K hK e he).choose) :
    (dartOrbitFaceLoop K hK e he).getVert n = dartFace ((dartNext K)^[n] e) := by
  rw [dartOrbitFaceLoop, SimpleGraph.Walk.getVert_copy]
  exact jc7_dartOrbitFaceWalk_getVert K e he _ n hn













theorem jc7_orbitLoop_length_eq_period (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) :
    (olb_orbitLoop K hK e he).length = (dartNext_periodic K hK e he).choose := by
  rw [olb_orbitLoop_length, dartOrbitFaceLoop, SimpleGraph.Walk.length_copy,
    dartOrbitFaceWalk_length]








theorem jc7_orbitLoop_getVert_eq_dartFace_period (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (n : ℕ)
    (hn : n ≤ (dartNext_periodic K hK e he).choose) :
    (olb_orbitLoop K hK e he).getVert n = dartFace ((dartNext K)^[n] e) := by
  change ((dartOrbitFaceLoop K hK e he).map (Hom.ofLE (faceBoundaryGraph_le K))).getVert n = _
  rw [SimpleGraph.Walk.getVert_map]
  change (dartOrbitFaceLoop K hK e he).getVert n = _
  exact jc7_dartOrbitFaceLoop_getVert K hK e he n hn








theorem jc7_getVert_eq_dartFace (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (n : ℕ) (hn : n ≤ (olb_orbitLoop K hK e he).length) :
    (olb_orbitLoop K hK e he).getVert n = dartFace ((dartNext K)^[n] e) := by
  apply jc7_orbitLoop_getVert_eq_dartFace_period K hK e he n
  rwa [jc7_orbitLoop_length_eq_period K hK e he] at hn








theorem jc7_orbitLoop_getVert_zero (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) :
    (olb_orbitLoop K hK e he).getVert 0 = dartFace e := by
  rw [jc7_getVert_eq_dartFace K hK e he 0 (Nat.zero_le _)]
  simp

end Walls

end StatMech
