/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartInjective
import Code.Lattice.DartOrbit
import Code.Lattice.ContourLinksExits
import Code.Lattice.Umlaufsatz

open SimpleGraph Function Set

namespace StatMech

namespace Lattice










def npd_P00 (f : Site 2) : Site 2 := ![f 0, f 1]


def npd_P10 (f : Site 2) : Site 2 := ![f 0 + 1, f 1]


def npd_P11 (f : Site 2) : Site 2 := ![f 0 + 1, f 1 + 1]


def npd_P01 (f : Site 2) : Site 2 := ![f 0, f 1 + 1]




theorem npd_corners_right {K : Set (Site 2)} {e : Dart} (he : IsBoundaryDart K e)
    (hd : e.dir = ![1, 0]) :
    npd_P00 (dartFace e) ∈ K ∧ npd_P10 (dartFace e) ∉ K := by
  have htail : e.tail = npd_P00 (dartFace e) := dartFace_tail_of_dir_right e hd
  have hhead : e.head = npd_P10 (dartFace e) := by
    rw [dart_head_eq e, hd, htail, npd_P00, npd_P10]
    funext i; fin_cases i <;> simp
  exact ⟨htail ▸ he.1, hhead ▸ he.2⟩




theorem npd_corners_up {K : Set (Site 2)} {e : Dart} (he : IsBoundaryDart K e)
    (hd : e.dir = ![0, 1]) :
    npd_P10 (dartFace e) ∈ K ∧ npd_P11 (dartFace e) ∉ K := by
  have htail : e.tail = npd_P10 (dartFace e) := by
    rw [dartFace_tail_of_dir_up e hd, npd_P10]
  have hhead : e.head = npd_P11 (dartFace e) := by
    rw [dart_head_eq e, hd, dartFace_tail_of_dir_up e hd, npd_P11]
    funext i; fin_cases i <;> simp
  exact ⟨htail ▸ he.1, hhead ▸ he.2⟩




theorem npd_corners_left {K : Set (Site 2)} {e : Dart} (he : IsBoundaryDart K e)
    (hd : e.dir = ![-1, 0]) :
    npd_P11 (dartFace e) ∈ K ∧ npd_P01 (dartFace e) ∉ K := by
  have htail : e.tail = npd_P11 (dartFace e) := by
    rw [dartFace_tail_of_dir_left e hd, npd_P11]
  have hhead : e.head = npd_P01 (dartFace e) := by
    rw [dart_head_eq e, hd, dartFace_tail_of_dir_left e hd, npd_P01]
    funext i; fin_cases i <;> simp
  exact ⟨htail ▸ he.1, hhead ▸ he.2⟩




theorem npd_corners_down {K : Set (Site 2)} {e : Dart} (he : IsBoundaryDart K e)
    (hd : e.dir = ![0, -1]) :
    npd_P01 (dartFace e) ∈ K ∧ npd_P00 (dartFace e) ∉ K := by
  have htail : e.tail = npd_P01 (dartFace e) := by
    rw [dartFace_tail_of_dir_down e hd, npd_P01]
  have hhead : e.head = npd_P00 (dartFace e) := by
    rw [dart_head_eq e, hd, dartFace_tail_of_dir_down e hd, npd_P00]
    funext i; fin_cases i <;> simp
  exact ⟨htail ▸ he.1, hhead ▸ he.2⟩
















def npd_DiagTouch (K : Set (Site 2)) (f : Site 2) : Prop :=
  (npd_P00 f ∈ K ∧ npd_P11 f ∈ K ∧ npd_P10 f ∉ K ∧ npd_P01 f ∉ K) ∨
  (npd_P10 f ∈ K ∧ npd_P01 f ∈ K ∧ npd_P00 f ∉ K ∧ npd_P11 f ∉ K)









set_option linter.unnecessarySeqFocus false in









theorem npd_pinch_forces_diagTouch {K : Set (Site 2)} {e₁ e₂ : Dart}
    (he₁ : IsBoundaryDart K e₁) (he₂ : IsBoundaryDart K e₂)
    (hface : dartFace e₁ = dartFace e₂) (hdir : e₁.dir ≠ e₂.dir) :
    npd_DiagTouch K (dartFace e₁) := by
  
  have hf₂ : dartFace e₂ = dartFace e₁ := hface.symm
  unfold npd_DiagTouch
  rcases dartDir_cases e₁ with h1 | h1 | h1 | h1 <;>
    rcases dartDir_cases e₂ with h2 | h2 | h2 | h2 <;>
    
    first
      | exact absurd (h1.trans h2.symm) hdir
      | (first
          | (have c1 := npd_corners_right he₁ h1)
          | (have c1 := npd_corners_up he₁ h1)
          | (have c1 := npd_corners_left he₁ h1)
          | (have c1 := npd_corners_down he₁ h1)) <;>
        (first
          | (have c2 := npd_corners_right he₂ h2)
          | (have c2 := npd_corners_up he₂ h2)
          | (have c2 := npd_corners_left he₂ h2)
          | (have c2 := npd_corners_down he₂ h2)) <;>
        · rw [hf₂] at c2; tauto






theorem npd_noPinch_local_of_noDiagTouch {K : Set (Site 2)} {e₁ e₂ : Dart}
    (he₁ : IsBoundaryDart K e₁) (he₂ : IsBoundaryDart K e₂)
    (hface : dartFace e₁ = dartFace e₂) (hnt : ¬ npd_DiagTouch K (dartFace e₁)) :
    e₁.dir = e₂.dir := by
  by_contra hdir
  exact hnt (npd_pinch_forces_diagTouch he₁ he₂ hface hdir)






theorem npd_dart_eq_of_noDiagTouch {K : Set (Site 2)} {e₁ e₂ : Dart}
    (he₁ : IsBoundaryDart K e₁) (he₂ : IsBoundaryDart K e₂)
    (hface : dartFace e₁ = dartFace e₂) (hnt : ¬ npd_DiagTouch K (dartFace e₁)) :
    e₁ = e₂ :=
  dartFace_eq_of_dir_eq (npd_noPinch_local_of_noDiagTouch he₁ he₂ hface hnt) hface













def npd_NoDiagTouchAlongOrbit (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∀ k ∈ Set.Iio (dartOrbitPeriod K a), ¬ npd_DiagTouch K (dartFace ((dartNext K)^[k] a.1))









theorem npd_orbitFaceNoPinch_of_noDiagTouch (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : npd_NoDiagTouchAlongOrbit K a) :
    OrbitFaceNoPinch K a := by
  intro i hi j hj hface
  have hbi : IsBoundaryDart K ((dartNext K)^[i] a.1) := iterate_isBoundaryDart K a.1 a.2 i
  have hbj : IsBoundaryDart K ((dartNext K)^[j] a.1) := iterate_isBoundaryDart K a.1 a.2 j
  exact npd_noPinch_local_of_noDiagTouch hbi hbj hface (h i hi)





theorem npd_orbitFace_injOn_of_noDiagTouch (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : npd_NoDiagTouchAlongOrbit K a) :
    Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a)) :=
  orbitFace_injOn_of_noPinch K a (npd_orbitFaceNoPinch_of_noDiagTouch K a h)





def npd_NoDiagTouch (K : Set (Site 2)) : Prop := ∀ f : Site 2, ¬ npd_DiagTouch K f



theorem npd_noDiagTouchAlongOrbit_of_global {K : Set (Site 2)} (h : npd_NoDiagTouch K)
    (a : {e : Dart // IsBoundaryDart K e}) : npd_NoDiagTouchAlongOrbit K a :=
  fun k _ => h (dartFace ((dartNext K)^[k] a.1))











theorem npd_orbitFaceNoPinch_of_globalNoDiagTouch (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : npd_NoDiagTouch K) :
    OrbitFaceNoPinch K a :=
  npd_orbitFaceNoPinch_of_noDiagTouch K a (npd_noDiagTouchAlongOrbit_of_global h a)













theorem npd_diagTouch_example :
    npd_DiagTouch ({![0, 0], ![1, 1]} : Set (Site 2)) ![0, 0] := by
  left
  refine ⟨?_, ?_, ?_, ?_⟩
  · show npd_P00 (![0, 0] : Site 2) ∈ ({![0, 0], ![1, 1]} : Set (Site 2))
    left; funext i; fin_cases i <;> rfl
  · show npd_P11 (![0, 0] : Site 2) ∈ ({![0, 0], ![1, 1]} : Set (Site 2))
    right; funext i; fin_cases i <;> simp [npd_P11]
  · show npd_P10 (![0, 0] : Site 2) ∉ ({![0, 0], ![1, 1]} : Set (Site 2))
    rintro (h | h)
    · have := congrFun h 0; simp [npd_P10] at this
    · have := congrFun h 1; simp [npd_P10] at this
  · show npd_P01 (![0, 0] : Site 2) ∉ ({![0, 0], ![1, 1]} : Set (Site 2))
    rintro (h | h)
    · have := congrFun h 1; simp [npd_P01] at this
    · have := congrFun h 0; simp [npd_P01] at this








































end Lattice

end StatMech
