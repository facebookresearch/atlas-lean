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

open SimpleGraph

namespace StatMech

namespace Walls

open StatMech.Lattice










def jc_travel (e : Dart) : Site 2 := -rot90Fun e.dir




def jc_headTravel (e : Dart) : Site 2 := e.head + jc_travel e




def jc_tailTravel (e : Dart) : Site 2 := e.tail + jc_travel e

@[simp] theorem jc_headTravel_eq (e : Dart) :
    jc_headTravel e = e.head + (-rot90Fun e.dir) := rfl

@[simp] theorem jc_tailTravel_eq (e : Dart) :
    jc_tailTravel e = e.tail + (-rot90Fun e.dir) := rfl
















theorem jc_dartNext_congr (K K' : Set (Site 2)) (e : Dart)
    (hhead : jc_headTravel e ∈ K ↔ jc_headTravel e ∈ K')
    (htail : jc_tailTravel e ∈ K ↔ jc_tailTravel e ∈ K') :
    dartNext K e = dartNext K' e := by
  classical
  
  simp only [jc_headTravel_eq, jc_tailTravel_eq] at hhead htail
  by_cases hA : e.head + (-rot90Fun e.dir) ∈ K
  · 
    have hA' : e.head + (-rot90Fun e.dir) ∈ K' := hhead.mp hA
    rw [dartNext_of_front_mem K e hA, dartNext_of_front_mem K' e hA']
  · have hA' : e.head + (-rot90Fun e.dir) ∉ K' := fun h => hA (hhead.mpr h)
    by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · 
      have hB' : e.tail + (-rot90Fun e.dir) ∈ K' := htail.mp hB
      rw [dartNext_of_side_mem K e hA hB, dartNext_of_side_mem K' e hA' hB']
    · 
      have hB' : e.tail + (-rot90Fun e.dir) ∉ K' := fun h => hB (htail.mpr h)
      rw [dartNext_of_corner K e hA hB, dartNext_of_corner K' e hA' hB']



theorem jc_turnZ_congr (K K' : Set (Site 2)) (e : Dart)
    (hhead : jc_headTravel e ∈ K ↔ jc_headTravel e ∈ K')
    (htail : jc_tailTravel e ∈ K ↔ jc_tailTravel e ∈ K') :
    turnZ K e = turnZ K' e := by
  classical
  simp only [jc_headTravel_eq, jc_tailTravel_eq] at hhead htail
  unfold turnZ
  by_cases hA : e.head + (-rot90Fun e.dir) ∈ K
  · rw [if_pos hA, if_pos (hhead.mp hA)]
  · rw [if_neg hA, if_neg (fun h => hA (hhead.mpr h))]
    by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · rw [if_pos hB, if_pos (htail.mp hB)]
    · rw [if_neg hB, if_neg (fun h => hB (htail.mpr h))]



theorem jc_turn_congr (K K' : Set (Site 2)) (e : Dart)
    (hhead : jc_headTravel e ∈ K ↔ jc_headTravel e ∈ K')
    (htail : jc_tailTravel e ∈ K ↔ jc_tailTravel e ∈ K') :
    turn K e = turn K' e := by
  classical
  simp only [jc_headTravel_eq, jc_tailTravel_eq] at hhead htail
  unfold turn
  by_cases hA : e.head + (-rot90Fun e.dir) ∈ K
  · rw [if_pos hA, if_pos (hhead.mp hA)]
  · rw [if_neg hA, if_neg (fun h => hA (hhead.mpr h))]
    by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · rw [if_pos hB, if_pos (htail.mp hB)]
    · rw [if_neg hB, if_neg (fun h => hB (htail.mpr h))]






theorem jc_step_local (K K' : Set (Site 2)) (e : Dart)
    (hhead : jc_headTravel e ∈ K ↔ jc_headTravel e ∈ K')
    (htail : jc_tailTravel e ∈ K ↔ jc_tailTravel e ∈ K') :
    dartNext K e = dartNext K' e ∧ turnZ K e = turnZ K' e ∧ turn K e = turn K' e :=
  ⟨jc_dartNext_congr K K' e hhead htail,
   jc_turnZ_congr K K' e hhead htail,
   jc_turn_congr K K' e hhead htail⟩















theorem jc_step_local_of_agree_on_probes (K K' : Set (Site 2)) (e : Dart)
    (hagree : ∀ x, (x = jc_headTravel e ∨ x = jc_tailTravel e) → (x ∈ K ↔ x ∈ K')) :
    dartNext K e = dartNext K' e ∧ turnZ K e = turnZ K' e ∧ turn K e = turn K' e :=
  jc_step_local K K' e (hagree _ (Or.inl rfl)) (hagree _ (Or.inr rfl))






theorem jc_step_local_of_symmDiff_avoids (K K' : Set (Site 2)) (e : Dart)
    (hhead : jc_headTravel e ∉ (K \ K') ∪ (K' \ K))
    (htail : jc_tailTravel e ∉ (K \ K') ∪ (K' \ K)) :
    dartNext K e = dartNext K' e ∧ turnZ K e = turnZ K' e ∧ turn K e = turn K' e := by
  refine jc_step_local K K' e ?_ ?_
  · constructor
    · intro h
      by_contra h'
      exact hhead (Or.inl ⟨h, h'⟩)
    · intro h
      by_contra h'
      exact hhead (Or.inr ⟨h, h'⟩)
  · constructor
    · intro h
      by_contra h'
      exact htail (Or.inl ⟨h, h'⟩)
    · intro h
      by_contra h'
      exact htail (Or.inr ⟨h, h'⟩)

end Walls

end StatMech
