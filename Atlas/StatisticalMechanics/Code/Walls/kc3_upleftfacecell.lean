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

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice










theorem kc3_upDart_face (e : Dart) (hd : e.dir = ![0, 1]) :
    dartFace e = ![e.tail 0 - 1, e.tail 1] :=
  dartFace_of_dir_up e hd



theorem kc3_upDart_tail (e : Dart) (hd : e.dir = ![0, 1]) :
    e.tail = ![dartFace e 0 + 1, dartFace e 1] :=
  dartFace_tail_of_dir_up e hd



theorem kc3_upDart_head (e : Dart) (hd : e.dir = ![0, 1]) :
    e.head = ![dartFace e 0 + 1, dartFace e 1 + 1] := by
  rw [dart_head_eq e, hd, dartFace_tail_of_dir_up e hd]
  funext i; fin_cases i <;> simp





theorem kc3_upDart_face_ne_tail (e : Dart) (hd : e.dir = ![0, 1]) :
    dartFace e ≠ e.tail := by
  rw [kc3_upDart_tail e hd]
  intro h; have := congrFun h 0; simp at this



theorem kc3_upDart_face_ne_head (e : Dart) (hd : e.dir = ![0, 1]) :
    dartFace e ≠ e.head := by
  rw [kc3_upDart_head e hd]
  intro h; have := congrFun h 0; simp at this










theorem kc3_leftDart_face (e : Dart) (hd : e.dir = ![-1, 0]) :
    dartFace e = ![e.tail 0 - 1, e.tail 1 - 1] :=
  dartFace_of_dir_left e hd



theorem kc3_leftDart_tail (e : Dart) (hd : e.dir = ![-1, 0]) :
    e.tail = ![dartFace e 0 + 1, dartFace e 1 + 1] :=
  dartFace_tail_of_dir_left e hd



theorem kc3_leftDart_head (e : Dart) (hd : e.dir = ![-1, 0]) :
    e.head = ![dartFace e 0, dartFace e 1 + 1] := by
  rw [dart_head_eq e, hd, dartFace_tail_of_dir_left e hd]
  funext i; fin_cases i <;> simp




theorem kc3_leftDart_face_ne_tail (e : Dart) (hd : e.dir = ![-1, 0]) :
    dartFace e ≠ e.tail := by
  rw [kc3_leftDart_tail e hd]
  intro h; have := congrFun h 0; simp at this




theorem kc3_leftDart_face_ne_head (e : Dart) (hd : e.dir = ![-1, 0]) :
    dartFace e ≠ e.head := by
  rw [kc3_leftDart_head e hd]
  intro h; have := congrFun h 1; simp at this




















theorem kc3_upLeft_faceCell {K : Set (Site 2)} {e : Dart}
    (he : IsBoundaryDart K e) (hdir : e.dir = ![0, 1] ∨ e.dir = ![-1, 0]) :
    dartFace e ≠ e.tail ∧ dartFace e ≠ e.head ∧ e.tail ∈ K ∧ e.head ∉ K ∧
    ( (e.dir = ![0, 1] ∧ dartFace e = ![e.tail 0 - 1, e.tail 1] ∧
        e.tail = ![dartFace e 0 + 1, dartFace e 1])
    ∨ (e.dir = ![-1, 0] ∧ dartFace e = ![e.tail 0 - 1, e.tail 1 - 1] ∧
        e.tail = ![dartFace e 0 + 1, dartFace e 1 + 1]) ) := by
  obtain ⟨htail, hhead⟩ := he
  rcases hdir with hd | hd
  · refine ⟨kc3_upDart_face_ne_tail e hd, kc3_upDart_face_ne_head e hd, htail, hhead,
      Or.inl ⟨hd, kc3_upDart_face e hd, kc3_upDart_tail e hd⟩⟩
  · refine ⟨kc3_leftDart_face_ne_tail e hd, kc3_leftDart_face_ne_head e hd, htail, hhead,
      Or.inr ⟨hd, kc3_leftDart_face e hd, kc3_leftDart_tail e hd⟩⟩












theorem kc3_dir_trichotomy_faceCell {K : Set (Site 2)} {e : Dart}
    (_he : IsBoundaryDart K e) :
    e.dir = ![1, 0] ∨ e.dir = ![0, -1] ∨
      (dartFace e ≠ e.tail ∧ dartFace e ≠ e.head) := by
  rcases dartDir_cases e with hd | hd | hd | hd
  · exact Or.inl hd
  · exact Or.inr (Or.inr ⟨kc3_leftDart_face_ne_tail e hd, kc3_leftDart_face_ne_head e hd⟩)
  · exact Or.inr (Or.inr ⟨kc3_upDart_face_ne_tail e hd, kc3_upDart_face_ne_head e hd⟩)
  · exact Or.inr (Or.inl hd)












noncomputable def kc3_ul_witUpDart : Dart := mkDart ![1, 0] ![0, 1] (by decide)

@[simp] theorem kc3_ul_witUpDart_dir : kc3_ul_witUpDart.dir = ![0, 1] := mkDart_dir _ _ _

@[simp] theorem kc3_ul_witUpDart_tail : kc3_ul_witUpDart.tail = ![1, 0] := mkDart_tail _ _ _


theorem kc3_ul_witUpDart_face : dartFace kc3_ul_witUpDart = ![0, 0] := by
  rw [kc3_upDart_face _ kc3_ul_witUpDart_dir, kc3_ul_witUpDart_tail]
  funext i; fin_cases i <;> norm_num


theorem kc3_ul_witUpDart_head : kc3_ul_witUpDart.head = ![1, 1] := by
  rw [dart_head_eq, kc3_ul_witUpDart_tail, kc3_ul_witUpDart_dir]
  funext i; fin_cases i <;> simp



theorem kc3_ul_witUpDart_boundary_K1 :
    IsBoundaryDart ({![1, 0]} : Set (Site 2)) kc3_ul_witUpDart := by
  refine ⟨?_, ?_⟩
  · rw [Set.mem_singleton_iff, kc3_ul_witUpDart_tail]
  · rw [Set.mem_singleton_iff, kc3_ul_witUpDart_head]; intro h
    have := congrFun h 1; simp at this


theorem kc3_ul_witUpDart_boundary_K2 :
    IsBoundaryDart ({![0, 0], ![1, 0]} : Set (Site 2)) kc3_ul_witUpDart := by
  refine ⟨?_, ?_⟩
  · rw [kc3_ul_witUpDart_tail]; right; rfl
  · rw [kc3_ul_witUpDart_head]; intro h
    rcases h with h | h
    · have := congrFun h 1; simp at this
    · rw [Set.mem_singleton_iff] at h; have := congrFun h 1; simp at this


theorem kc3_ul_witUpDart_face_notin_K1 :
    dartFace kc3_ul_witUpDart ∉ ({![1, 0]} : Set (Site 2)) := by
  rw [kc3_ul_witUpDart_face, Set.mem_singleton_iff]
  intro h; have := congrFun h 0; simp at this


theorem kc3_ul_witUpDart_face_in_K2 :
    dartFace kc3_ul_witUpDart ∈ ({![0, 0], ![1, 0]} : Set (Site 2)) := by
  rw [kc3_ul_witUpDart_face]; left; rfl





noncomputable def kc3_ul_witLeftDart : Dart := mkDart ![1, 1] ![-1, 0] (by decide)

@[simp] theorem kc3_ul_witLeftDart_dir : kc3_ul_witLeftDart.dir = ![-1, 0] := mkDart_dir _ _ _

@[simp] theorem kc3_ul_witLeftDart_tail : kc3_ul_witLeftDart.tail = ![1, 1] := mkDart_tail _ _ _


theorem kc3_ul_witLeftDart_face : dartFace kc3_ul_witLeftDart = ![0, 0] := by
  rw [kc3_leftDart_face _ kc3_ul_witLeftDart_dir, kc3_ul_witLeftDart_tail]
  funext i; fin_cases i <;> norm_num


theorem kc3_ul_witLeftDart_head : kc3_ul_witLeftDart.head = ![0, 1] := by
  rw [dart_head_eq, kc3_ul_witLeftDart_tail, kc3_ul_witLeftDart_dir]
  funext i; fin_cases i <;> simp



theorem kc3_ul_witLeftDart_boundary_K1 :
    IsBoundaryDart ({![1, 1]} : Set (Site 2)) kc3_ul_witLeftDart := by
  refine ⟨?_, ?_⟩
  · rw [Set.mem_singleton_iff, kc3_ul_witLeftDart_tail]
  · rw [Set.mem_singleton_iff, kc3_ul_witLeftDart_head]; intro h
    have := congrFun h 0; simp at this


theorem kc3_ul_witLeftDart_boundary_K2 :
    IsBoundaryDart ({![0, 0], ![1, 1]} : Set (Site 2)) kc3_ul_witLeftDart := by
  refine ⟨?_, ?_⟩
  · rw [kc3_ul_witLeftDart_tail]; right; rfl
  · rw [kc3_ul_witLeftDart_head]; intro h
    rcases h with h | h
    · have := congrFun h 1; simp at this
    · rw [Set.mem_singleton_iff] at h; have := congrFun h 0; simp at this


theorem kc3_ul_witLeftDart_face_notin_K1 :
    dartFace kc3_ul_witLeftDart ∉ ({![1, 1]} : Set (Site 2)) := by
  rw [kc3_ul_witLeftDart_face, Set.mem_singleton_iff]
  intro h; have := congrFun h 0; simp at this


theorem kc3_ul_witLeftDart_face_in_K2 :
    dartFace kc3_ul_witLeftDart ∈ ({![0, 0], ![1, 1]} : Set (Site 2)) := by
  rw [kc3_ul_witLeftDart_face]; left; rfl







theorem kc3_face_membership_unpinned_up :
    ∃ (e : Dart) (K₁ K₂ : Set (Site 2)),
      e.dir = ![0, 1] ∧ IsBoundaryDart K₁ e ∧ IsBoundaryDart K₂ e ∧
      dartFace e ∉ K₁ ∧ dartFace e ∈ K₂ :=
  ⟨kc3_ul_witUpDart, {![1, 0]}, {![0, 0], ![1, 0]}, kc3_ul_witUpDart_dir,
    kc3_ul_witUpDart_boundary_K1, kc3_ul_witUpDart_boundary_K2,
    kc3_ul_witUpDart_face_notin_K1, kc3_ul_witUpDart_face_in_K2⟩




theorem kc3_face_membership_unpinned_left :
    ∃ (e : Dart) (K₁ K₂ : Set (Site 2)),
      e.dir = ![-1, 0] ∧ IsBoundaryDart K₁ e ∧ IsBoundaryDart K₂ e ∧
      dartFace e ∉ K₁ ∧ dartFace e ∈ K₂ :=
  ⟨kc3_ul_witLeftDart, {![1, 1]}, {![0, 0], ![1, 1]}, kc3_ul_witLeftDart_dir,
    kc3_ul_witLeftDart_boundary_K1, kc3_ul_witLeftDart_boundary_K2,
    kc3_ul_witLeftDart_face_notin_K1, kc3_ul_witLeftDart_face_in_K2⟩







theorem kc3_face_membership_unpinned :
    (∃ (e : Dart) (K₁ K₂ : Set (Site 2)),
      e.dir = ![0, 1] ∧ IsBoundaryDart K₁ e ∧ IsBoundaryDart K₂ e ∧
      dartFace e ∉ K₁ ∧ dartFace e ∈ K₂)
    ∧
    (∃ (e : Dart) (K₁ K₂ : Set (Site 2)),
      e.dir = ![-1, 0] ∧ IsBoundaryDart K₁ e ∧ IsBoundaryDart K₂ e ∧
      dartFace e ∉ K₁ ∧ dartFace e ∈ K₂) :=
  ⟨kc3_face_membership_unpinned_up, kc3_face_membership_unpinned_left⟩

end Walls

end StatMech
