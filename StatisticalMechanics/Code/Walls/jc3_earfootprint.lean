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
import Code.Lattice.TurningNumber
import Code.Lattice.BalancePreservingContraction
import Code.Walls.jc_steplocal
import Code.Walls.jc2_runframe
import Code.Walls.jc2_thickshelf

open SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice











def jc3_earFootprint (r : Site 2) : Set (Site 2) :=
  {r, r + ![1, 0], r + ![(-1 : ℤ), 0], r + ![0, 1], r + ![0, (-1 : ℤ)]}


theorem jc3_mem_earFootprint (r x : Site 2) :
    x ∈ jc3_earFootprint r ↔
      x = r ∨ x = r + ![1, 0] ∨ x = r + ![(-1 : ℤ), 0] ∨ x = r + ![0, 1] ∨
        x = r + ![0, (-1 : ℤ)] := by
  unfold jc3_earFootprint
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]


theorem jc3_self_mem_earFootprint (r : Site 2) : r ∈ jc3_earFootprint r := by
  rw [jc3_mem_earFootprint]; exact Or.inl rfl


theorem jc3_right_mem_earFootprint (r : Site 2) : r + ![1, 0] ∈ jc3_earFootprint r := by
  rw [jc3_mem_earFootprint]; exact Or.inr (Or.inl rfl)


theorem jc3_left_mem_earFootprint (r : Site 2) :
    r + ![(-1 : ℤ), 0] ∈ jc3_earFootprint r := by
  rw [jc3_mem_earFootprint]; exact Or.inr (Or.inr (Or.inl rfl))


theorem jc3_up_mem_earFootprint (r : Site 2) : r + ![0, 1] ∈ jc3_earFootprint r := by
  rw [jc3_mem_earFootprint]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))


theorem jc3_down_mem_earFootprint (r : Site 2) :
    r + ![0, (-1 : ℤ)] ∈ jc3_earFootprint r := by
  rw [jc3_mem_earFootprint]; exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))


theorem jc3_earFootprint_finite (r : Site 2) : (jc3_earFootprint r).Finite := by
  unfold jc3_earFootprint
  exact Set.toFinite _













def jc3_AvoidsEarFootprint (r : Site 2) (e : Dart) : Prop :=
  jc_headTravel e ∉ jc3_earFootprint r ∧ jc_tailTravel e ∉ jc3_earFootprint r





theorem jc3_notProbed_of_avoidsEarFootprint (r : Site 2) (e : Dart)
    (h : jc3_AvoidsEarFootprint r e) : bpc_NotProbed r e := by
  obtain ⟨hhead, htail⟩ := h
  refine ⟨?_, ?_⟩
  · 
    intro heq
    apply hhead
    rw [jc_headTravel_eq] at *
    rw [heq]
    exact jc3_self_mem_earFootprint r
  · intro heq
    apply htail
    rw [jc_tailTravel_eq] at *
    rw [heq]
    exact jc3_self_mem_earFootprint r





















theorem jc3_dartNext_eq_of_avoidsEarFootprint (K : Set (Site 2)) (r : Site 2) (e : Dart)
    (h : jc3_AvoidsEarFootprint r e) :
    dartNext (K \ {r}) e = dartNext K e :=
  bpc_dartNext_diff_singleton K r e (jc3_notProbed_of_avoidsEarFootprint r e h)











theorem jc3_turnZ_eq_of_avoidsEarFootprint (K : Set (Site 2)) (r : Site 2) (e : Dart)
    (h : jc3_AvoidsEarFootprint r e) :
    turnZ (K \ {r}) e = turnZ K e :=
  bpc_turnZ_diff_singleton K r e (jc3_notProbed_of_avoidsEarFootprint r e h)








theorem jc3_step_eq_of_avoidsEarFootprint (K : Set (Site 2)) (r : Site 2) (e : Dart)
    (h : jc3_AvoidsEarFootprint r e) :
    dartNext (K \ {r}) e = dartNext K e ∧ turnZ (K \ {r}) e = turnZ K e :=
  ⟨jc3_dartNext_eq_of_avoidsEarFootprint K r e h,
   jc3_turnZ_eq_of_avoidsEarFootprint K r e h⟩













theorem jc3_earFootprintLocality (K : Set (Site 2)) (r : Site 2) (e : Dart)
    (h : jc3_AvoidsEarFootprint r e) :
    dartNext (K \ {r}) e = dartNext K e ∧ turnZ (K \ {r}) e = turnZ K e ∧
      turn (K \ {r}) e = turn K e := by
  
  obtain ⟨hnp1, hnp2⟩ := jc3_notProbed_of_avoidsEarFootprint r e h
  refine jc_step_local (K \ {r}) K e ?_ ?_
  · constructor
    · intro hmem; exact (Set.mem_diff _).mp hmem |>.1
    · intro hmem
      refine (Set.mem_diff _).mpr ⟨hmem, ?_⟩
      simp only [Set.mem_singleton_iff]
      exact hnp1
  · constructor
    · intro hmem; exact (Set.mem_diff _).mp hmem |>.1
    · intro hmem
      refine (Set.mem_diff _).mpr ⟨hmem, ?_⟩
      simp only [Set.mem_singleton_iff]
      exact hnp2










theorem jc3_mem_diff_singleton_of_ne (K : Set (Site 2)) (r x : Site 2) (hx : x ≠ r) :
    x ∈ K \ {r} ↔ x ∈ K := by
  rw [Set.mem_diff, Set.mem_singleton_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩



theorem jc3_symmDiff_diff_singleton_subset (K : Set (Site 2)) (r : Site 2) :
    (K \ (K \ {r})) ∪ ((K \ {r}) \ K) ⊆ {r} := by
  intro x hx
  rcases hx with hx | hx
  · 
    obtain ⟨hxK, hxnd⟩ := hx
    simp only [Set.mem_diff, Set.mem_singleton_iff, not_and, not_not] at hxnd
    exact hxnd hxK
  · 
    obtain ⟨hxd, hxK⟩ := hx
    exact absurd hxd.1 hxK










def jc3_farDart : Dart :=
  mkDart (![10, 0] : Site 2) (![1, 0] : Site 2) (by
    unfold unitWt
    rw [Fin.sum_univ_two]
    simp)

@[simp] theorem jc3_farDart_dir : jc3_farDart.dir = ![1, 0] := by
  unfold jc3_farDart; rw [mkDart_dir]





theorem jc3_farDart_avoidsOrigin :
    jc3_AvoidsEarFootprint (![0, 0] : Site 2) jc3_farDart := by
  
  have hdir : jc3_farDart.dir = ![1, 0] := jc3_farDart_dir
  constructor
  · 
    rw [jc_headTravel_eq, hdir]
    rw [jc3_mem_earFootprint]
    
    intro hcon
    have h0 : (jc3_farDart.head + (-rot90Fun (![1, 0] : Site 2))) 0 = 11 := by
      unfold jc3_farDart rot90Fun
      simp only [mkDart_head, Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      norm_num
    rcases hcon with h | h | h | h | h <;>
      · rw [h] at h0
        revert h0
        simp only [Pi.add_apply, Matrix.cons_val_zero]
        norm_num
  · 
    rw [jc_tailTravel_eq, hdir]
    rw [jc3_mem_earFootprint]
    intro hcon
    have h0 : (jc3_farDart.tail + (-rot90Fun (![1, 0] : Site 2))) 0 = 10 := by
      unfold jc3_farDart rot90Fun
      simp only [mkDart_tail, Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      norm_num
    rcases hcon with h | h | h | h | h <;>
      · rw [h] at h0
        revert h0
        simp only [Pi.add_apply, Matrix.cons_val_zero]
        norm_num




theorem jc3_farDart_step_eq (K : Set (Site 2)) :
    dartNext (K \ {(![0, 0] : Site 2)}) jc3_farDart = dartNext K jc3_farDart ∧
      turnZ (K \ {(![0, 0] : Site 2)}) jc3_farDart = turnZ K jc3_farDart :=
  jc3_step_eq_of_avoidsEarFootprint K (![0, 0] : Site 2) jc3_farDart jc3_farDart_avoidsOrigin

























end Walls

end StatMech
