/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.ContourLinksExits
import Code.Lattice.Umlaufsatz
import Code.Lattice.NoPinchDual

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice








theorem kc2_P00_eq_self (f : Site 2) : npd_P00 f = f := by
  funext i; fin_cases i <;> simp [npd_P00]










theorem kc2_leftDart_face (e : Dart) (hd : e.dir = ![-1, 0]) :
    dartFace e = ![e.tail 0 - 1, e.tail 1 - 1] :=
  dartFace_of_dir_left e hd



theorem kc2_leftDart_tail_eq_P11 (e : Dart) (hd : e.dir = ![-1, 0]) :
    e.tail = npd_P11 (dartFace e) := by
  rw [dartFace_tail_of_dir_left e hd, npd_P11]



theorem kc2_leftDart_head_eq_P01 (e : Dart) (hd : e.dir = ![-1, 0]) :
    e.head = npd_P01 (dartFace e) := by
  rw [dart_head_eq e, hd, dartFace_tail_of_dir_left e hd, npd_P01]
  funext i; fin_cases i <;> simp





theorem kc2_leftDart_corners {K : Set (Site 2)} {e : Dart}
    (he : IsBoundaryDart K e) (hd : e.dir = ![-1, 0]) :
    npd_P11 (dartFace e) ∈ K ∧ npd_P01 (dartFace e) ∉ K :=
  npd_corners_left he hd









theorem kc2_upDart_face (e : Dart) (hd : e.dir = ![0, 1]) :
    dartFace e = ![e.tail 0 - 1, e.tail 1] :=
  dartFace_of_dir_up e hd



theorem kc2_upDart_tail_eq_P10 (e : Dart) (hd : e.dir = ![0, 1]) :
    e.tail = npd_P10 (dartFace e) := by
  rw [dartFace_tail_of_dir_up e hd, npd_P10]



theorem kc2_upDart_head_eq_P11 (e : Dart) (hd : e.dir = ![0, 1]) :
    e.head = npd_P11 (dartFace e) := by
  rw [dart_head_eq e, hd, dartFace_tail_of_dir_up e hd, npd_P11]
  funext i; fin_cases i <;> simp





theorem kc2_upDart_corners {K : Set (Site 2)} {e : Dart}
    (he : IsBoundaryDart K e) (hd : e.dir = ![0, 1]) :
    npd_P10 (dartFace e) ∈ K ∧ npd_P11 (dartFace e) ∉ K :=
  npd_corners_up he hd










theorem kc2_P00_ne_P11 (f : Site 2) : npd_P00 f ≠ npd_P11 f := by
  intro h; have := congrFun h 0; simp [npd_P00, npd_P11] at this



theorem kc2_P00_ne_P10 (f : Site 2) : npd_P00 f ≠ npd_P10 f := by
  intro h; have := congrFun h 0; simp [npd_P00, npd_P10] at this




theorem kc2_leftDart_face_ne_tail (e : Dart) (hd : e.dir = ![-1, 0]) :
    dartFace e ≠ e.tail := by
  rw [kc2_leftDart_tail_eq_P11 e hd]
  conv_lhs => rw [← kc2_P00_eq_self (dartFace e)]
  exact kc2_P00_ne_P11 (dartFace e)




theorem kc2_upDart_face_ne_tail (e : Dart) (hd : e.dir = ![0, 1]) :
    dartFace e ≠ e.tail := by
  rw [kc2_upDart_tail_eq_P10 e hd]
  conv_lhs => rw [← kc2_P00_eq_self (dartFace e)]
  exact kc2_P00_ne_P10 (dartFace e)






















theorem kc2_leftUp_faceCell {K : Set (Site 2)} {e : Dart}
    (he : IsBoundaryDart K e) (hdir : e.dir = ![-1, 0] ∨ e.dir = ![0, 1]) :
    dartFace e = npd_P00 (dartFace e) ∧
    npd_P00 (dartFace e) ≠ e.tail ∧
    ( (e.dir = ![-1, 0] ∧ dartFace e = ![e.tail 0 - 1, e.tail 1 - 1] ∧
        e.tail = npd_P11 (dartFace e) ∧ npd_P11 (dartFace e) ∈ K)
    ∨ (e.dir = ![0, 1] ∧ dartFace e = ![e.tail 0 - 1, e.tail 1] ∧
        e.tail = npd_P10 (dartFace e) ∧ npd_P10 (dartFace e) ∈ K) ) := by
  refine ⟨(kc2_P00_eq_self _).symm, ?_, ?_⟩
  · rcases hdir with hd | hd
    · rw [kc2_P00_eq_self]; exact kc2_leftDart_face_ne_tail e hd
    · rw [kc2_P00_eq_self]; exact kc2_upDart_face_ne_tail e hd
  · rcases hdir with hd | hd
    · exact Or.inl ⟨hd, kc2_leftDart_face e hd, kc2_leftDart_tail_eq_P11 e hd,
        (kc2_leftDart_corners he hd).1⟩
    · exact Or.inr ⟨hd, kc2_upDart_face e hd, kc2_upDart_tail_eq_P10 e hd,
        (kc2_upDart_corners he hd).1⟩












theorem kc2_dir_trichotomy_faceCell {K : Set (Site 2)} {e : Dart}
    (he : IsBoundaryDart K e) :
    e.dir = ![1, 0] ∨ e.dir = ![0, -1] ∨
      (dartFace e = npd_P00 (dartFace e) ∧ npd_P00 (dartFace e) ≠ e.tail) := by
  rcases dartDir_cases e with hd | hd | hd | hd
  · exact Or.inl hd
  · have h := kc2_leftUp_faceCell he (Or.inl hd)
    exact Or.inr (Or.inr ⟨h.1, h.2.1⟩)
  · have h := kc2_leftUp_faceCell he (Or.inr hd)
    exact Or.inr (Or.inr ⟨h.1, h.2.1⟩)
  · exact Or.inr (Or.inl hd)

















noncomputable def kc2_witLeftDart : Dart := mkDart ![1, 1] ![-1, 0] (by decide)

@[simp] theorem kc2_witLeftDart_dir : kc2_witLeftDart.dir = ![-1, 0] := mkDart_dir _ _ _

@[simp] theorem kc2_witLeftDart_tail : kc2_witLeftDart.tail = ![1, 1] := mkDart_tail _ _ _


theorem kc2_witLeftDart_face : dartFace kc2_witLeftDart = ![0, 0] := by
  rw [kc2_leftDart_face _ kc2_witLeftDart_dir, kc2_witLeftDart_tail]
  funext i; fin_cases i <;> norm_num


theorem kc2_witLeftDart_head : kc2_witLeftDart.head = ![0, 1] := by
  rw [dart_head_eq, kc2_witLeftDart_tail, kc2_witLeftDart_dir]
  funext i; fin_cases i <;> simp


theorem kc2_witLeftDart_boundary_K1 :
    IsBoundaryDart ({![1, 1]} : Set (Site 2)) kc2_witLeftDart := by
  refine ⟨?_, ?_⟩
  · rw [Set.mem_singleton_iff, kc2_witLeftDart_tail]
  · rw [Set.mem_singleton_iff, kc2_witLeftDart_head]; intro h
    have := congrFun h 0; simp at this


theorem kc2_witLeftDart_boundary_K2 :
    IsBoundaryDart ({![0, 0], ![1, 1]} : Set (Site 2)) kc2_witLeftDart := by
  refine ⟨?_, ?_⟩
  · rw [kc2_witLeftDart_tail]; right; rfl
  · rw [kc2_witLeftDart_head]; intro h
    rcases h with h | h
    · have := congrFun h 1; simp at this
    · rw [Set.mem_singleton_iff] at h; have := congrFun h 0; simp at this


theorem kc2_witLeftDart_P00_notin_K1 :
    npd_P00 (dartFace kc2_witLeftDart) ∉ ({![1, 1]} : Set (Site 2)) := by
  rw [kc2_P00_eq_self, kc2_witLeftDart_face, Set.mem_singleton_iff]
  intro h; have := congrFun h 0; simp at this


theorem kc2_witLeftDart_P00_in_K2 :
    npd_P00 (dartFace kc2_witLeftDart) ∈ ({![0, 0], ![1, 1]} : Set (Site 2)) := by
  rw [kc2_P00_eq_self, kc2_witLeftDart_face]; left; rfl






theorem kc2_face_membership_not_pinned :
    ∃ (e : Dart) (K₁ K₂ : Set (Site 2)),
      IsBoundaryDart K₁ e ∧ IsBoundaryDart K₂ e ∧
      npd_P00 (dartFace e) ∉ K₁ ∧ npd_P00 (dartFace e) ∈ K₂ :=
  ⟨kc2_witLeftDart, {![1, 1]}, {![0, 0], ![1, 1]},
    kc2_witLeftDart_boundary_K1, kc2_witLeftDart_boundary_K2,
    kc2_witLeftDart_P00_notin_K1, kc2_witLeftDart_P00_in_K2⟩

end Walls

end StatMech
