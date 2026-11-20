/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































































import Mathlib
import Code.Lattice.ContourLinksExits
import Code.Walls.jc_steplocal
import Code.Walls.jc3_earfootprint
import Code.Walls.jc4_firstreturnK
import Code.Walls.jc5_footprintdartsfinite
import Code.Walls.jc7getverteqdartface
import Code.Lattice.OrbitLoopBridge

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice













theorem jc8tf_earFootprint_row (r x : Site 2) (hx : x ∈ jc3_earFootprint r) :
    r 1 - 1 ≤ x 1 ∧ x 1 ≤ r 1 + 1 := by
  rw [jc3_mem_earFootprint] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨?_, ?_⟩ <;>
    (try simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]) <;> omega























theorem jc8tf_dartFace_row_near_probes (d : Dart) :
    (dartFace d 1 - jc_headTravel d 1).natAbs ≤ 2 ∧
      (dartFace d 1 - jc_tailTravel d 1).natAbs ≤ 2 := by
  
  have hhead : d.head = d.tail + d.dir := by rw [Dart.dir_def]; abel
  rcases dartDir_cases d with hd | hd | hd | hd
  · 
    have hf : dartFace d 1 = d.tail 1 := by rw [dartFace_of_dir_right d hd]; simp
    have hh : jc_headTravel d 1 = d.tail 1 - 1 := by
      rw [jc_headTravel_eq, hd, hhead, hd]
      simp only [rot90Fun, Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.neg_apply]
      ring
    have ht : jc_tailTravel d 1 = d.tail 1 - 1 := by
      rw [jc_tailTravel_eq, hd]
      simp only [rot90Fun, Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.neg_apply]
      ring
    rw [hf, hh, ht]; omega
  · 
    have hf : dartFace d 1 = d.tail 1 - 1 := by rw [dartFace_of_dir_left d hd]; simp
    have hh : jc_headTravel d 1 = d.tail 1 + 1 := by
      rw [jc_headTravel_eq, hd, hhead, hd]
      simp only [rot90Fun, Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.neg_apply]
      ring
    have ht : jc_tailTravel d 1 = d.tail 1 + 1 := by
      rw [jc_tailTravel_eq, hd]
      simp only [rot90Fun, Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.neg_apply]
      ring
    rw [hf, hh, ht]; omega
  · 
    have hf : dartFace d 1 = d.tail 1 := by rw [dartFace_of_dir_up d hd]; simp
    have hh : jc_headTravel d 1 = d.tail 1 + 1 := by
      rw [jc_headTravel_eq, hd, hhead, hd]
      simp only [rot90Fun, Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.neg_apply]
      ring
    have ht : jc_tailTravel d 1 = d.tail 1 := by
      rw [jc_tailTravel_eq, hd]
      simp only [rot90Fun, Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.neg_apply]
      ring
    rw [hf, hh, ht]; omega
  · 
    have hf : dartFace d 1 = d.tail 1 - 1 := by rw [dartFace_of_dir_down d hd]; simp
    have hh : jc_headTravel d 1 = d.tail 1 - 1 := by
      rw [jc_headTravel_eq, hd, hhead, hd]
      simp only [rot90Fun, Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.neg_apply]
      ring
    have ht : jc_tailTravel d 1 = d.tail 1 := by
      rw [jc_tailTravel_eq, hd]
      simp only [rot90Fun, Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.neg_apply]
      ring
    rw [hf, hh, ht]; omega


















theorem jc8tf_probingDart_dartFace_row_band (r : Site 2) (d : Dart)
    (hprobe : jc5_ProbesEarFootprint r d) :
    r 1 - 3 ≤ dartFace d 1 ∧ dartFace d 1 ≤ r 1 + 3 := by
  obtain ⟨hgh, hgt⟩ := jc8tf_dartFace_row_near_probes d
  rcases hprobe with hh | ht
  · 
    obtain ⟨hlo, hhi⟩ := jc8tf_earFootprint_row r _ hh
    
    
    omega
  · 
    obtain ⟨hlo, hhi⟩ := jc8tf_earFootprint_row r _ ht
    omega
















theorem jc8tf_touchingDart_of_touchingStep (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    (r : Site 2) (j : ℕ) (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j) :
    jc5_ProbesEarFootprint r ((dartNext K)^[j] e) := by
  unfold jc4_FootprintFree at htouch
  rw [jc5_not_avoidsEarFootprint_iff_probes] at htouch
  exact htouch


















theorem jc8tf_touchingFace_row_band (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (j : ℕ)
    (hj : j ≤ (olb_orbitLoop K hK e he).length)
    (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j) :
    r 1 - 3 ≤ (olb_orbitLoop K hK e he).getVert j 1 ∧
      (olb_orbitLoop K hK e he).getVert j 1 ≤ r 1 + 3 := by
  
  have hgv : (olb_orbitLoop K hK e he).getVert j = dartFace ((dartNext K)^[j] e) :=
    jc7_getVert_eq_dartFace K hK e he j hj
  rw [hgv]
  
  exact jc8tf_probingDart_dartFace_row_band r _
    (jc8tf_touchingDart_of_touchingStep K e he r j htouch)

















theorem jc8tf_touchingFace_within_three (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (j : ℕ)
    (hj : j ≤ (olb_orbitLoop K hK e he).length)
    (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j) :
    ((olb_orbitLoop K hK e he).getVert j 1 - r 1).natAbs ≤ 3 := by
  obtain ⟨hlo, hhi⟩ := jc8tf_touchingFace_row_band K hK e he r j hj htouch
  omega





theorem jc8tf_touchingFace_lower (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (j : ℕ)
    (hj : j ≤ (olb_orbitLoop K hK e he).length)
    (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j) :
    r 1 - 3 ≤ (olb_orbitLoop K hK e he).getVert j 1 :=
  (jc8tf_touchingFace_row_band K hK e he r j hj htouch).1




theorem jc8tf_touchingFace_upper (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (j : ℕ)
    (hj : j ≤ (olb_orbitLoop K hK e he).length)
    (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j) :
    (olb_orbitLoop K hK e he).getVert j 1 ≤ r 1 + 3 :=
  (jc8tf_touchingFace_row_band K hK e he r j hj htouch).2










theorem jc8tf_dartFace_row_near_probes_self :
    (dartFace (mkDart (![0, 0] : Site 2) (![1, 0] : Site 2)
        (by unfold unitWt; rw [Fin.sum_univ_two]; simp)) 1 -
      jc_headTravel (mkDart (![0, 0] : Site 2) (![1, 0] : Site 2)
        (by unfold unitWt; rw [Fin.sum_univ_two]; simp)) 1).natAbs ≤ 2 :=
  (jc8tf_dartFace_row_near_probes _).1





theorem jc8tf_band_nonvacuous :
    (![0, 0] : Site 2) 1 - 3 ≤
        dartFace (mkDart (![0, 1] : Site 2) (![1, 0] : Site 2)
          (by unfold unitWt; rw [Fin.sum_univ_two]; simp)) 1 ∧
      dartFace (mkDart (![0, 1] : Site 2) (![1, 0] : Site 2)
          (by unfold unitWt; rw [Fin.sum_univ_two]; simp)) 1 ≤ (![0, 0] : Site 2) 1 + 3 :=
  jc8tf_probingDart_dartFace_row_band (![0, 0] : Site 2) _ jc5_someDart_probes






























end Walls

end StatMech
