/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































import Mathlib
import Code.Lattice.ContourLinksExits
import Code.Lattice.ExteriorConnected

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice













theorem kc3_dartFace_down_eq_head (e : Dart) (hd : e.dir = ![0, -1]) :
    dartFace e = e.head := by
  rw [dartFace_of_dir_down e hd, dart_head_eq e, hd]
  funext i
  fin_cases i
  · simp
  · simp; ring











theorem kc3_down_head_notMem {K : Set (Site 2)} {e : Dart}
    (he : IsBoundaryDart K e) (_hd : e.dir = ![0, -1]) :
    e.head ∉ K :=
  he.head_not_mem





theorem kc3_dartFace_down_notMem {K : Set (Site 2)} {e : Dart}
    (he : IsBoundaryDart K e) (hd : e.dir = ![0, -1]) :
    dartFace e ∉ K := by
  rw [kc3_dartFace_down_eq_head e hd]
  exact kc3_down_head_notMem he hd


















theorem kc3_down_zInK_unattainable {K : Set (Site 2)} {e : Dart}
    (he : IsBoundaryDart K e) (hd : e.dir = ![0, -1]) :
    ¬ (dartFace e ∈ K) :=
  kc3_dartFace_down_notMem he hd




theorem kc3_down_zInK_false {K : Set (Site 2)} {e : Dart}
    (he : IsBoundaryDart K e) (hd : e.dir = ![0, -1]) (hmem : dartFace e ∈ K) :
    False :=
  kc3_down_zInK_unattainable he hd hmem


















theorem kc3_down_supportOdd_forces_even (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {e : Dart} (he : IsBoundaryDart K e)
    (hd : e.dir = ![0, -1]) (hsupp : dartFace e ∈ (mpl_orbitLoop K a).support)
    (hres : exc_SupportOddInK K a) :
    Even (jec_rayCount (dartFace e) (mpl_orbitLoop K a)) := by
  by_contra hodd
  exact kc3_down_zInK_unattainable he hd (hres (dartFace e) hsupp hodd)









def kc3_upperHalf : Set (Site 2) := {p | 0 ≤ p 1}


noncomputable def kc3_downDart : Dart :=
  mkDart (0 : Site 2) (![0, -1] : Site 2) (by
    unfold unitWt; rw [Fin.sum_univ_two]; decide)


theorem kc3_downDart_dir : kc3_downDart.dir = ![0, -1] := by
  rw [kc3_downDart, mkDart_dir]



theorem kc3_downDart_isBoundary : IsBoundaryDart kc3_upperHalf kc3_downDart := by
  constructor
  · 
    show kc3_downDart.tail ∈ kc3_upperHalf
    rw [kc3_downDart, mkDart_tail]
    change (0 : ℤ) ≤ (0 : Site 2) 1
    simp
  · 
    show kc3_downDart.head ∉ kc3_upperHalf
    have hhead : kc3_downDart.head 1 = -1 := by
      rw [dart_head_eq, kc3_downDart_dir, kc3_downDart, mkDart_tail]
      simp [Pi.add_apply]
    intro h
    simp only [kc3_upperHalf, Set.mem_setOf_eq] at h
    rw [hhead] at h
    norm_num at h




theorem kc3_downDart_face_notMem :
    dartFace kc3_downDart ∉ kc3_upperHalf :=
  kc3_dartFace_down_notMem kc3_downDart_isBoundary kc3_downDart_dir

end Walls

end StatMech
