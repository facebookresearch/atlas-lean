/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.JordanEnclosure
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartOrbit
import Code.Lattice.OrbitEncloses
import Code.Lattice.OrbitLoopBridge
import Code.Walls.jc7loopiscycle
import Code.Walls.jc7getverteqdartface

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice











theorem jc8_loopIsCycle (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hp : 3 ≤ jc7_choosePeriod K hK e he)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e))
      (Set.Iio (jc7_choosePeriod K hK e he))) :
    (olb_orbitLoop K hK e he).IsCycle :=
  jc7_LoopIsCycle K hK e he hp hinj















theorem jc8_count_one_of_tail_nodup {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u : V}
    (p : G.Walk u u) (htail : p.support.tail.Nodup) {v : V}
    (hv : v ∈ p.support) (hvu : v ≠ u) :
    p.support.count v = 1 := by
  have hs : p.support = u :: p.support.tail := (Walk.cons_tail_support p).symm
  have hvtail : v ∈ p.support.tail := by
    rw [hs] at hv
    rcases List.mem_cons.mp hv with h | h
    · exact absurd h hvu
    · exact h
  rw [hs, List.count_cons]
  simp only [beq_iff_eq]
  rw [if_neg (fun h => hvu h.symm), List.count_eq_one_of_mem htail hvtail]









theorem jc8_tail_nodup_of_count {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u : V}
    (p : G.Walk u u) (hu : p.support.count u = 2)
    (hother : ∀ v ∈ p.support, v ≠ u → p.support.count v = 1) :
    p.support.tail.Nodup := by
  have hs : p.support = u :: p.support.tail := (Walk.cons_tail_support p).symm
  have hut : p.support.tail.count u = 1 := by
    have hu' := hu
    rw [hs, List.count_cons] at hu'
    simp only [beq_self_eq_true, if_true] at hu'
    omega
  rw [List.nodup_iff_count_le_one]
  intro a
  by_cases hau : a = u
  · subst hau; omega
  · by_cases hamem : a ∈ p.support.tail
    · have hamem_s : a ∈ p.support := by rw [hs]; exact List.mem_cons_of_mem _ hamem
      have hc1 : p.support.count a = 1 := hother a hamem_s hau
      rw [hs, List.count_cons] at hc1
      simp only [beq_iff_eq] at hc1
      rw [if_neg (fun h => hau h.symm)] at hc1
      omega
    · rw [List.count_eq_zero_of_not_mem hamem]; omega






theorem jc8_support_tail_nodup_iff_count {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u : V}
    (p : G.Walk u u) (hu : p.support.count u = 2) :
    p.support.tail.Nodup ↔ ∀ v ∈ p.support, v ≠ u → p.support.count v = 1 :=
  ⟨fun htail _ hv hvu => jc8_count_one_of_tail_nodup p htail hv hvu,
    fun hother => jc8_tail_nodup_of_count p hu hother⟩













theorem jc8_loopIsCycle_support_nodup (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hp : 3 ≤ jc7_choosePeriod K hK e he)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e))
      (Set.Iio (jc7_choosePeriod K hK e he))) :
    (olb_orbitLoop K hK e he).support.tail.Nodup :=
  (jc8_loopIsCycle K hK e he hp hinj).support_nodup











theorem jc8_loopIsCycle_count_support_of_mem (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hp : 3 ≤ jc7_choosePeriod K hK e he)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e))
      (Set.Iio (jc7_choosePeriod K hK e he)))
    {v : Site 2} (hv : v ∈ (olb_orbitLoop K hK e he).support) (hvb : v ≠ dartFace e) :
    (olb_orbitLoop K hK e he).support.count v = 1 :=
  (jc8_loopIsCycle K hK e he hp hinj).count_support_of_mem hv hvb





theorem jc8_loopIsCycle_count_support (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hp : 3 ≤ jc7_choosePeriod K hK e he)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e))
      (Set.Iio (jc7_choosePeriod K hK e he))) :
    (olb_orbitLoop K hK e he).support.count (dartFace e) = 2 :=
  (jc8_loopIsCycle K hK e he hp hinj).count_support













theorem jc8_loop_support_tail_nodup_iff_count (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hp : 3 ≤ jc7_choosePeriod K hK e he)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e))
      (Set.Iio (jc7_choosePeriod K hK e he))) :
    (olb_orbitLoop K hK e he).support.tail.Nodup ↔
      ∀ v ∈ (olb_orbitLoop K hK e he).support, v ≠ dartFace e →
        (olb_orbitLoop K hK e he).support.count v = 1 :=
  jc8_support_tail_nodup_iff_count (olb_orbitLoop K hK e he)
    (jc8_loopIsCycle_count_support K hK e he hp hinj)















theorem jc8_contour_face_ne_basepoint (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e))
      (Set.Iio (jc7_choosePeriod K hK e he)))
    {n : ℕ} (hn0 : 0 < n) (hnp : n < jc7_choosePeriod K hK e he) :
    dartFace ((dartNext K)^[n] e) ≠ dartFace e := by
  intro hcontra
  have h0 : dartFace ((dartNext K)^[0] e) = dartFace e := by simp
  have heq : (fun k => dartFace ((dartNext K)^[k] e)) n
      = (fun k => dartFace ((dartNext K)^[k] e)) 0 := by
    simp only
    rw [h0]; exact hcontra
  have := hinj (Set.mem_Iio.mpr hnp) (Set.mem_Iio.mpr (by omega)) heq
  omega










theorem jc8_contour_face_count_eq_one (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hp : 3 ≤ jc7_choosePeriod K hK e he)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e))
      (Set.Iio (jc7_choosePeriod K hK e he)))
    {n : ℕ} (hn0 : 0 < n) (hnp : n < jc7_choosePeriod K hK e he) :
    (olb_orbitLoop K hK e he).support.count (dartFace ((dartNext K)^[n] e)) = 1 := by
  have hgv : (olb_orbitLoop K hK e he).getVert n = dartFace ((dartNext K)^[n] e) :=
    jc7_orbitLoop_getVert_eq_dartFace_period K hK e he n
      (show n ≤ jc7_choosePeriod K hK e he by omega)
  have hmem : dartFace ((dartNext K)^[n] e) ∈ (olb_orbitLoop K hK e he).support := by
    rw [← hgv]; exact SimpleGraph.Walk.getVert_mem_support _ n
  have hne : dartFace ((dartNext K)^[n] e) ≠ dartFace e :=
    jc8_contour_face_ne_basepoint K hK e he hinj hn0 hnp
  exact jc8_loopIsCycle_count_support_of_mem K hK e he hp hinj hmem hne














theorem jc8_minimalPeriod_support_nodup (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1))
      (Set.Iio (dartOrbitPeriod K a))) :
    (mpl_orbitLoop K a).support.tail.Nodup :=
  (jc7_minimalPeriod_loopIsCycle K a hp hinj).support_nodup






theorem jc8_unitCell_support_nodup : (mpl_orbitLoop unitCell ucBase).support.tail.Nodup :=
  jc7_unitCell_minimalPeriod_loopIsCycle.support_nodup



































end Walls

end StatMech
