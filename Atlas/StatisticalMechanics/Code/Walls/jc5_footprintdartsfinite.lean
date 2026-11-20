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
import Code.Walls.jc_steplocal
import Code.Walls.jc3_earfootprint
import Code.Walls.jc4_footprintagree

open SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice













def jc5_ProbesEarFootprint (r : Site 2) (e : Dart) : Prop :=
  jc_headTravel e ∈ jc3_earFootprint r ∨ jc_tailTravel e ∈ jc3_earFootprint r







theorem jc5_not_avoidsEarFootprint_iff_probes (r : Site 2) (e : Dart) :
    ¬ jc3_AvoidsEarFootprint r e ↔ jc5_ProbesEarFootprint r e := by
  unfold jc3_AvoidsEarFootprint jc5_ProbesEarFootprint
  rw [not_and_or, not_not, not_not, or_comm]












theorem jc5_tail_eq_of_tailTravel (e : Dart) :
    e.tail = jc_tailTravel e + rot90Fun e.dir := by
  rw [jc_tailTravel_eq]; abel




theorem jc5_head_eq_of_headTravel (e : Dart) :
    e.head = jc_headTravel e + rot90Fun e.dir := by
  rw [jc_headTravel_eq]; abel














theorem jc5_tailTouching_finite (r : Site 2) :
    {e : Dart | jc_tailTravel e ∈ jc3_earFootprint r}.Finite := by
  apply Set.Finite.of_finite_image (f := fun e : Dart => (jc_tailTravel e, e.dir))
  · 
    apply Set.Finite.subset ((jc3_earFootprint_finite r).prod unitVectors_finite)
    rintro _ ⟨e, he, rfl⟩
    exact ⟨he, unitWt_dir e⟩
  · 
    rintro e₁ _ e₂ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hprobe, hdir⟩ := h
    
    have htail : e₁.tail = e₂.tail := by
      rw [jc5_tail_eq_of_tailTravel e₁, jc5_tail_eq_of_tailTravel e₂, hprobe, hdir]
    exact dart_eq_of_tail_dir htail hdir







theorem jc5_headTouching_finite (r : Site 2) :
    {e : Dart | jc_headTravel e ∈ jc3_earFootprint r}.Finite := by
  apply Set.Finite.of_finite_image (f := fun e : Dart => (jc_headTravel e, e.dir))
  · apply Set.Finite.subset ((jc3_earFootprint_finite r).prod unitVectors_finite)
    rintro _ ⟨e, he, rfl⟩
    exact ⟨he, unitWt_dir e⟩
  · rintro e₁ _ e₂ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hprobe, hdir⟩ := h
    have hhead : e₁.head = e₂.head := by
      rw [jc5_head_eq_of_headTravel e₁, jc5_head_eq_of_headTravel e₂, hprobe, hdir]
    exact dart_eq_of_head_dir hhead hdir

























theorem jc5_footprintDarts_finite (r : Site 2) :
    {e : Dart | jc5_ProbesEarFootprint r e}.Finite := by
  
  have hsub : {e : Dart | jc5_ProbesEarFootprint r e} ⊆
      {e : Dart | jc_headTravel e ∈ jc3_earFootprint r} ∪
      {e : Dart | jc_tailTravel e ∈ jc3_earFootprint r} := by
    intro e he
    rcases he with hh | ht
    · exact Or.inl hh
    · exact Or.inr ht
  exact ((jc5_headTouching_finite r).union (jc5_tailTouching_finite r)).subset hsub











theorem jc5_touchingDart_tail_dir_injOn (r : Site 2) :
    Set.InjOn (fun e : Dart => (jc_tailTravel e, e.dir))
      {e : Dart | jc_tailTravel e ∈ jc3_earFootprint r} := by
  rintro e₁ _ e₂ _ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨hprobe, hdir⟩ := h
  have htail : e₁.tail = e₂.tail := by
    rw [jc5_tail_eq_of_tailTravel e₁, jc5_tail_eq_of_tailTravel e₂, hprobe, hdir]
  exact dart_eq_of_tail_dir htail hdir




theorem jc5_touchingDart_finite_image (r : Site 2) :
    (jc3_earFootprint r ×ˢ {z : Site 2 | unitWt z = 1}).Finite :=
  (jc3_earFootprint_finite r).prod unitVectors_finite












theorem jc5_farDart_not_probes :
    ¬ jc5_ProbesEarFootprint (![0, 0] : Site 2) jc3_farDart := by
  rw [← jc5_not_avoidsEarFootprint_iff_probes, not_not]
  exact jc3_farDart_avoidsOrigin





theorem jc5_someDart_probes :
    jc5_ProbesEarFootprint (![0, 0] : Site 2)
      (mkDart (![0, 1] : Site 2) (![1, 0] : Site 2)
        (by unfold unitWt; rw [Fin.sum_univ_two]; simp)) := by
  
  right
  rw [jc_tailTravel_eq, mkDart_tail, mkDart_dir]
  have hprobe : (![0, 1] : Site 2) + (-rot90Fun (![1, 0] : Site 2)) = (![0, 0] : Site 2) := by
    funext i; fin_cases i <;> simp [rot90Fun]
  rw [hprobe]
  exact jc3_self_mem_earFootprint _































end Walls

end StatMech
