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

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice











theorem kc2_iterate_isBoundaryDart (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) (k : ℕ) :
    IsBoundaryDart K ((dartNext K)^[k] e) := by
  induction k with
  | zero => simpa using he
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact dartNext_isBoundaryDart K _ ih




theorem kc2_iterate_tail_mem (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) (k : ℕ) :
    ((dartNext K)^[k] e).tail ∈ K :=
  (kc2_iterate_isBoundaryDart K e he k).1





theorem kc2_iterate_head_not_mem (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) (k : ℕ) :
    ((dartNext K)^[k] e).head ∉ K :=
  (kc2_iterate_isBoundaryDart K e he k).2












theorem kc2_orbitSub_iterate_tail_mem (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (k : ℕ) :
    ((dartNextSub K)^[k] a).1.tail ∈ K := by
  rw [dartNextSub_iterate_val]
  exact kc2_iterate_tail_mem K a.1 a.2 k





theorem kc2_orbit_support_tail_mem (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {d : {e : Dart // IsBoundaryDart K e}}
    (_hd : d ∈ (dartOrbitWalk K a).support) :
    d.1.tail ∈ K :=
  d.2.1












def kc2_IsCellCorner (f q : Site 2) : Prop :=
  ∃ s t : ℤ, (s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1) ∧ q = ![f 0 + s, f 1 + t]







theorem kc2_tail_isCellCorner (e : Dart) :
    kc2_IsCellCorner (dartFace e) e.tail := by
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





theorem kc2_faceCorner_in_K {K : Set (Site 2)} {e : Dart} (he : IsBoundaryDart K e) :
    kc2_IsCellCorner (dartFace e) e.tail ∧ e.tail ∈ K :=
  ⟨kc2_tail_isCellCorner e, he.1⟩







theorem kc2_iterate_faceCorner_in_K (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) (k : ℕ) :
    kc2_IsCellCorner (dartFace ((dartNext K)^[k] e)) ((dartNext K)^[k] e).tail ∧
      ((dartNext K)^[k] e).tail ∈ K :=
  kc2_faceCorner_in_K (kc2_iterate_isBoundaryDart K e he k)












theorem kc2_cellCorner_coord {f q : Site 2} (h : kc2_IsCellCorner f q) :
    (q 0 = f 0 ∨ q 0 = f 0 + 1) ∧ (q 1 = f 1 ∨ q 1 = f 1 + 1) := by
  obtain ⟨s, t, hs, ht, hq⟩ := h
  refine ⟨?_, ?_⟩
  · rcases hs with rfl | rfl <;> simp [hq]
  · rcases ht with rfl | rfl <;> simp [hq]

end Walls

end StatMech
