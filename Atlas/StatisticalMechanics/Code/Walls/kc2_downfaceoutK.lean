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














theorem kc2_dartFace_down_eq_head (e : Dart) (hd : e.dir = ![0, -1]) :
    dartFace e = e.head := by
  rw [dartFace_of_dir_down e hd, dart_head_eq e, hd]
  funext i
  fin_cases i
  · simp
  · simp; ring











theorem kc2_dartFace_down_notMem {K : Set (Site 2)} {e : Dart}
    (he : IsBoundaryDart K e) (hd : e.dir = ![0, -1]) :
    dartFace e ∉ K := by
  rw [kc2_dartFace_down_eq_head e hd]
  exact he.head_not_mem




















theorem kc2_down_face_even_of_supportOddInK (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {e : Dart} (he : IsBoundaryDart K e)
    (hd : e.dir = ![0, -1]) (hsupp : dartFace e ∈ (mpl_orbitLoop K a).support)
    (hres : exc_SupportOddInK K a) :
    Even (jec_rayCount (dartFace e) (mpl_orbitLoop K a)) := by
  by_contra hodd
  exact kc2_dartFace_down_notMem he hd (hres (dartFace e) hsupp hodd)

end Walls

end StatMech
