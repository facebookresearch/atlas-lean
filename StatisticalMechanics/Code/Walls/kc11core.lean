/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































































import Code.Walls.kc10core
import Code.Lattice.NoDiagTouchClose

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice


















theorem kc11_face_dir_unique_of_noDiagTouch {K : Set (Site 2)} (hnt : npd_NoDiagTouch K)
    {e₁ e₂ : Dart} (he₁ : IsBoundaryDart K e₁) (he₂ : IsBoundaryDart K e₂)
    (hface : dartFace e₁ = dartFace e₂) :
    e₁.dir = e₂.dir :=
  npd_noPinch_local_of_noDiagTouch he₁ he₂ hface (hnt (dartFace e₁))





theorem kc11_dart_eq_of_noDiagTouch {K : Set (Site 2)} (hnt : npd_NoDiagTouch K)
    {e₁ e₂ : Dart} (he₁ : IsBoundaryDart K e₁) (he₂ : IsBoundaryDart K e₂)
    (hface : dartFace e₁ = dartFace e₂) :
    e₁ = e₂ :=
  npd_dart_eq_of_noDiagTouch he₁ he₂ hface (hnt (dartFace e₁))















theorem kc11_support_dart_dir_unique {K : Set (Site 2)} (hnt : npd_NoDiagTouch K)
    (a : {e : Dart // IsBoundaryDart K e}) {z : Site 2}
    {i j : ℕ} (hi : z = dartFace ((dartNext K)^[i] a.1))
    (hj : z = dartFace ((dartNext K)^[j] a.1)) :
    ((dartNext K)^[i] a.1).dir = ((dartNext K)^[j] a.1).dir :=
  kc11_face_dir_unique_of_noDiagTouch hnt
    (iterate_isBoundaryDart K a.1 a.2 i) (iterate_isBoundaryDart K a.1 a.2 j)
    (hi ▸ hj)
























theorem kc11_collarSlide_of_noDiagTouch_and_escape {K : Set (Site 2)}
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (_hnt : npd_NoDiagTouch K)
    (hsupp : oc_supportSet (mpl_orbitLoop K a) ⊆ box 2 R)
    (hesc : kc5_OffSupportReachesExterior (mpl_orbitLoop K a) R) :
    kc10_CollarSlide (mpl_orbitLoop K a) R :=
  kc10_collarSlide_of_offSupportReaches (mpl_orbitLoop K a) R hsupp hesc






theorem kc11_collarSlide_of_escape {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hesc : kc5_OffSupportReachesExterior Vc R) :
    kc10_CollarSlide Vc R :=
  kc10_collarSlide_of_offSupportReaches Vc R hsupp hesc











theorem kc11_starHull_noDiagTouch (K : Set (Site 2)) : npd_NoDiagTouch (ndt_StarHull K) :=
  ndt_noDiagTouch K




theorem kc11_starHull_face_dir_unique (K : Set (Site 2))
    {e₁ e₂ : Dart} (he₁ : IsBoundaryDart (ndt_StarHull K) e₁)
    (he₂ : IsBoundaryDart (ndt_StarHull K) e₂)
    (hface : dartFace e₁ = dartFace e₂) :
    e₁.dir = e₂.dir :=
  kc11_face_dir_unique_of_noDiagTouch (kc11_starHull_noDiagTouch K) he₁ he₂ hface











theorem kc11_starHull_collarSlide_of_escape (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) (R : ℕ)
    (hsupp : oc_supportSet (mpl_orbitLoop (ndt_StarHull K) a) ⊆ box 2 R)
    (hesc : kc5_OffSupportReachesExterior (mpl_orbitLoop (ndt_StarHull K) a) R) :
    kc10_CollarSlide (mpl_orbitLoop (ndt_StarHull K) a) R :=
  kc11_collarSlide_of_noDiagTouch_and_escape a R (kc11_starHull_noDiagTouch K) hsupp hesc








theorem kc11_unitCell_collarSlide :
    kc10_CollarSlide (mpl_orbitLoop unitCell ucBase) 1 :=
  kc11_collarSlide_of_escape (mpl_orbitLoop unitCell ucBase) 1
    kc8_unitCell_supp_box kc8_unitCell_offSupportReaches






































end Walls

end StatMech
