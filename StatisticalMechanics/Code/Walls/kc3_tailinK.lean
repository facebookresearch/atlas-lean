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
import Code.Lattice.Umlaufsatz
import Code.Lattice.NoPinchDual

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice












theorem kc3_iterate_isBoundaryDart (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) (k : ℕ) :
    IsBoundaryDart K ((dartNext K)^[k] e) := by
  induction k with
  | zero => simpa using he
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact dartNext_isBoundaryDart K _ ih




theorem kc3_iterate_tail_mem (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) (k : ℕ) :
    ((dartNext K)^[k] e).tail ∈ K :=
  (kc3_iterate_isBoundaryDart K e he k).1





theorem kc3_iterate_head_not_mem (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) (k : ℕ) :
    ((dartNext K)^[k] e).head ∉ K :=
  (kc3_iterate_isBoundaryDart K e he k).2












theorem kc3_orbitSub_iterate_tail_mem (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (k : ℕ) :
    ((dartNextSub K)^[k] a).1.tail ∈ K := by
  rw [dartNextSub_iterate_val]
  exact kc3_iterate_tail_mem K a.1 a.2 k





theorem kc3_orbit_support_tail_mem (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {d : {e : Dart // IsBoundaryDart K e}}
    (_hd : d ∈ (dartOrbitWalk K a).support) :
    d.1.tail ∈ K :=
  d.2.1












def kc3_IsCellCorner (f q : Site 2) : Prop :=
  ∃ s t : ℤ, (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1) ∧ q = ![f 0 + s, f 1 + t]






theorem kc3_tail_isCellCorner (e : Dart) :
    kc3_IsCellCorner (dartFace e) e.tail := by
  rcases dartDir_cases e with hd | hd | hd | hd
  · 
    refine ⟨0, 0, Or.inl rfl, Or.inl rfl, ?_⟩
    rw [dartFace_tail_of_dir_right e hd]; funext i; fin_cases i <;> simp
  · 
    refine ⟨1, 1, Or.inr rfl, Or.inr rfl, ?_⟩
    rw [dartFace_tail_of_dir_left e hd]
  · 
    refine ⟨1, 0, Or.inr rfl, Or.inl rfl, ?_⟩
    rw [dartFace_tail_of_dir_up e hd]; funext i; fin_cases i <;> simp
  · 
    refine ⟨0, 1, Or.inl rfl, Or.inr rfl, ?_⟩
    rw [dartFace_tail_of_dir_down e hd]; funext i; fin_cases i <;> simp





theorem kc3_cellCorner_coord {f q : Site 2} (h : kc3_IsCellCorner f q) :
    (q 0 = f 0 ∨ q 0 = f 0 + 1) ∧ (q 1 = f 1 ∨ q 1 = f 1 + 1) := by
  obtain ⟨s, t, hs, ht, hq⟩ := h
  refine ⟨?_, ?_⟩
  · rcases hs with rfl | rfl <;> simp [hq]
  · rcases ht with rfl | rfl <;> simp [hq]





theorem kc3_faceCorner_in_K {K : Set (Site 2)} {e : Dart} (he : IsBoundaryDart K e) :
    kc3_IsCellCorner (dartFace e) e.tail ∧ e.tail ∈ K :=
  ⟨kc3_tail_isCellCorner e, he.1⟩







theorem kc3_iterate_faceCorner_in_K (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) (k : ℕ) :
    kc3_IsCellCorner (dartFace ((dartNext K)^[k] e)) ((dartNext K)^[k] e).tail ∧
      ((dartNext K)^[k] e).tail ∈ K :=
  kc3_faceCorner_in_K (kc3_iterate_isBoundaryDart K e he k)












theorem kc3_left_face_SW (e : Dart) (hd : e.dir = ![-1, 0]) :
    dartFace e = ![e.tail 0 - 1, e.tail 1 - 1] :=
  dartFace_of_dir_left e hd






theorem kc3_left_tail_eq_NE (e : Dart) (hd : e.dir = ![-1, 0]) :
    e.tail = npd_P11 (dartFace e) := by
  rw [dartFace_tail_of_dir_left e hd, npd_P11]







theorem kc3_left_extremeCell_mem {K : Set (Site 2)} {e : Dart} (he : IsBoundaryDart K e)
    (hd : e.dir = ![-1, 0]) :
    npd_P11 (dartFace e) ∈ K := by
  rw [← kc3_left_tail_eq_NE e hd]; exact he.tail_mem




theorem kc3_left_extremeCell_mem_coord {K : Set (Site 2)} {e : Dart} (he : IsBoundaryDart K e)
    (hd : e.dir = ![-1, 0]) :
    (![dartFace e 0 + 1, dartFace e 1 + 1] : Site 2) ∈ K := by
  have h := kc3_left_extremeCell_mem he hd
  rwa [npd_P11] at h





theorem kc3_left_face_ne_tail (e : Dart) (hd : e.dir = ![-1, 0]) :
    dartFace e ≠ e.tail := by
  rw [kc3_left_tail_eq_NE e hd]
  intro h
  have := congrFun h 0
  simp only [npd_P11, Matrix.cons_val_zero] at this
  omega





















theorem kc3_tailInK_node {K : Set (Site 2)} {e : Dart} (he : IsBoundaryDart K e) :
    e.tail ∈ K ∧ kc3_IsCellCorner (dartFace e) e.tail ∧
      (e.dir = ![-1, 0] →
        dartFace e = ![e.tail 0 - 1, e.tail 1 - 1] ∧
        e.tail = npd_P11 (dartFace e) ∧
        npd_P11 (dartFace e) ∈ K) := by
  refine ⟨he.tail_mem, kc3_tail_isCellCorner e, ?_⟩
  intro hd
  exact ⟨kc3_left_face_SW e hd, kc3_left_tail_eq_NE e hd, kc3_left_extremeCell_mem he hd⟩






theorem kc3_iterate_tailInK_node (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) (k : ℕ) :
    ((dartNext K)^[k] e).tail ∈ K ∧
      kc3_IsCellCorner (dartFace ((dartNext K)^[k] e)) ((dartNext K)^[k] e).tail ∧
      (((dartNext K)^[k] e).dir = ![-1, 0] →
        dartFace ((dartNext K)^[k] e) =
          ![((dartNext K)^[k] e).tail 0 - 1, ((dartNext K)^[k] e).tail 1 - 1] ∧
        ((dartNext K)^[k] e).tail = npd_P11 (dartFace ((dartNext K)^[k] e)) ∧
        npd_P11 (dartFace ((dartNext K)^[k] e)) ∈ K) :=
  kc3_tailInK_node (kc3_iterate_isBoundaryDart K e he k)










noncomputable def kc3_witLeftDart : Dart := mkDart ![1, 1] ![-1, 0] (by decide)

@[simp] theorem kc3_witLeftDart_dir : kc3_witLeftDart.dir = ![-1, 0] := mkDart_dir _ _ _

@[simp] theorem kc3_witLeftDart_tail : kc3_witLeftDart.tail = ![1, 1] := mkDart_tail _ _ _


theorem kc3_witLeftDart_face : dartFace kc3_witLeftDart = ![0, 0] := by
  rw [kc3_left_face_SW _ kc3_witLeftDart_dir, kc3_witLeftDart_tail]
  funext i; fin_cases i <;> norm_num


theorem kc3_witLeftDart_head : kc3_witLeftDart.head = ![0, 1] := by
  rw [dart_head_eq, kc3_witLeftDart_tail, kc3_witLeftDart_dir]
  funext i; fin_cases i <;> simp


theorem kc3_witLeftDart_boundary :
    IsBoundaryDart ({![1, 1]} : Set (Site 2)) kc3_witLeftDart := by
  refine ⟨?_, ?_⟩
  · rw [Set.mem_singleton_iff, kc3_witLeftDart_tail]
  · rw [Set.mem_singleton_iff, kc3_witLeftDart_head]; intro h
    have := congrFun h 0; simp at this





theorem kc3_node_nonvacuous :
    kc3_witLeftDart.tail ∈ ({![1, 1]} : Set (Site 2)) ∧
      kc3_IsCellCorner (dartFace kc3_witLeftDart) kc3_witLeftDart.tail ∧
      (kc3_witLeftDart.dir = ![-1, 0] →
        dartFace kc3_witLeftDart =
          ![kc3_witLeftDart.tail 0 - 1, kc3_witLeftDart.tail 1 - 1] ∧
        kc3_witLeftDart.tail = npd_P11 (dartFace kc3_witLeftDart) ∧
        npd_P11 (dartFace kc3_witLeftDart) ∈ ({![1, 1]} : Set (Site 2))) :=
  kc3_tailInK_node kc3_witLeftDart_boundary

end Walls

end StatMech
