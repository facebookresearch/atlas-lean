/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartOrbit
import Code.Lattice.ContourLinksExits
import Code.Lattice.TurningNumber
import Code.Lattice.OrbitEncloses
import Code.Lattice.JordanSingleCycle
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.MinimalPeriodLoop

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice













theorem kc_orbitFaceLoop_edges (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (mpl_orbitFaceLoop K a).edges
      = (List.range (dartOrbitPeriod K a)).map
          (fun k => s(dartFace ((dartNext K)^[k] a.1), dartFace ((dartNext K)^[k + 1] a.1))) := by
  rw [mpl_orbitFaceLoop, SimpleGraph.Walk.edges_copy, orbitFaceWalk_edges]






theorem kc_orbitLoop_edges (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (mpl_orbitLoop K a).edges
      = (List.range (dartOrbitPeriod K a)).map
          (fun k => s(dartFace ((dartNext K)^[k] a.1), dartFace ((dartNext K)^[k + 1] a.1))) := by
  rw [mpl_orbitLoop_edges, kc_orbitFaceLoop_edges]










open Classical in




theorem kc_orbitLoop_rayCount_eq_countP (z : Site 2) (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    jec_rayCount z (mpl_orbitLoop K a)
      = (List.range (dartOrbitPeriod K a)).countP
          (fun k => decide (jec_rayEdge z
            s(dartFace ((dartNext K)^[k] a.1), dartFace ((dartNext K)^[k + 1] a.1)))) := by
  classical
  rw [jec_rayCount, kc_orbitLoop_edges, List.countP_map]
  rfl








theorem kc_rayCount_congr_of_face_eq (z : Site 2)
    {K K' : Set (Site 2)} (a : {e : Dart // IsBoundaryDart K e})
    (a' : {e : Dart // IsBoundaryDart K' e})
    (hper : dartOrbitPeriod K a = dartOrbitPeriod K' a')
    (hface : ∀ k ≤ dartOrbitPeriod K a,
      dartFace ((dartNext K)^[k] a.1) = dartFace ((dartNext K')^[k] a'.1)) :
    jec_rayCount z (mpl_orbitLoop K a) = jec_rayCount z (mpl_orbitLoop K' a') := by
  classical
  rw [kc_orbitLoop_rayCount_eq_countP, kc_orbitLoop_rayCount_eq_countP, ← hper]
  refine List.countP_congr ?_
  intro k hk
  rw [List.mem_range] at hk
  
  rw [hface k (le_of_lt hk), hface (k + 1) hk]

end Walls

end StatMech
