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
import Code.Lattice.TurningNumber
import Code.Lattice.OrbitEncloses
import Code.Lattice.OrbitLoopBridge
import Code.Lattice.JordanSingleCycle
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.Umlaufsatz
import Code.Walls.jc6_singlecycle

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice









noncomputable def jc7_choosePeriod (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) : ℕ := (dartNext_periodic K hK e he).choose


theorem jc7_choosePeriod_pos (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) : 0 < jc7_choosePeriod K hK e he :=
  (dartNext_periodic K hK e he).choose_spec.1


theorem jc7_choosePeriod_iterate (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) :
    (dartNext K)^[jc7_choosePeriod K hK e he] e = e :=
  (dartNext_periodic K hK e he).choose_spec.2





theorem jc7_dartOrbitPeriod_dvd_choose (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) :
    dartOrbitPeriod K ⟨e, he⟩ ∣ jc7_choosePeriod K hK e he := by
  have hsub : Function.IsPeriodicPt (dartNextSub K) (jc7_choosePeriod K hK e he) ⟨e, he⟩ := by
    change (dartNextSub K)^[jc7_choosePeriod K hK e he] ⟨e, he⟩ = ⟨e, he⟩
    apply Subtype.ext
    rw [dartNextSub_iterate_val]
    exact jc7_choosePeriod_iterate K hK e he
  exact hsub.minimalPeriod_dvd



















theorem jc7_choose_eq_dartOrbitPeriod_of_injOn (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e))
      (Set.Iio (jc7_choosePeriod K hK e he))) :
    jc7_choosePeriod K hK e he = dartOrbitPeriod K ⟨e, he⟩ := by
  set P := jc7_choosePeriod K hK e he with hPdef
  set p := dartOrbitPeriod K ⟨e, he⟩ with hpdef
  have hdvd : p ∣ P := jc7_dartOrbitPeriod_dvd_choose K hK e he
  have hPpos : 0 < P := jc7_choosePeriod_pos K hK e he
  have hppos : 0 < p := dartOrbitPeriod_pos K hK ⟨e, he⟩
  have hple : p ≤ P := Nat.le_of_dvd hPpos hdvd
  rcases lt_or_eq_of_le hple with hlt | heq
  · exfalso
    
    have hface_p : (dartNext K)^[p] e = e := by
      have := orbit_iterate_period_eq K ⟨e, he⟩
      simpa using this
    have hf : (fun k => dartFace ((dartNext K)^[k] e)) p
        = (fun k => dartFace ((dartNext K)^[k] e)) 0 := by
      simp only
      rw [hface_p]; simp
    have := hinj (Set.mem_Iio.mpr hlt) (Set.mem_Iio.mpr hPpos) hf
    omega
  · exact heq.symm



















theorem jc7_dartOrbitFaceLoop_isCycle (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hp : 3 ≤ jc7_choosePeriod K hK e he)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e))
      (Set.Iio (jc7_choosePeriod K hK e he))) :
    (dartOrbitFaceLoop K hK e he).IsCycle := by
  have hcyc := orbitFaceWalk_isCycle K e he (jc7_choosePeriod K hK e he) hp
    (jc7_choosePeriod_iterate K hK e he) hinj
  
  unfold dartOrbitFaceLoop
  exact hcyc

























theorem jc7_LoopIsCycle (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hp : 3 ≤ jc7_choosePeriod K hK e he)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e))
      (Set.Iio (jc7_choosePeriod K hK e he))) :
    (olb_orbitLoop K hK e he).IsCycle := by
  
  have hdual : (dartOrbitFaceLoop K hK e he).IsCycle :=
    jc7_dartOrbitFaceLoop_isCycle K hK e he hp hinj
  
  have hprimal : ((dartOrbitFaceLoop K hK e he).mapLe (faceBoundaryGraph_le K)).IsCycle :=
    hdual.mapLe (faceBoundaryGraph_le K)
  
  rwa [olb_orbitLoop]












theorem jc7_loopIsCycle_support_nodup (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hp : 3 ≤ jc7_choosePeriod K hK e he)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e))
      (Set.Iio (jc7_choosePeriod K hK e he))) :
    (olb_orbitLoop K hK e he).support.tail.Nodup :=
  (jc7_LoopIsCycle K hK e he hp hinj).support_nodup




theorem jc7_loopIsCycle_count_support_of_mem (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hp : 3 ≤ jc7_choosePeriod K hK e he)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e))
      (Set.Iio (jc7_choosePeriod K hK e he)))
    {v : Site 2} (hv : v ∈ (olb_orbitLoop K hK e he).support) (hvb : v ≠ dartFace e) :
    (olb_orbitLoop K hK e he).support.count v = 1 :=
  (jc7_LoopIsCycle K hK e he hp hinj).count_support_of_mem hv hvb






theorem jc7_loopIsCycle_count_support (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hp : 3 ≤ jc7_choosePeriod K hK e he)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e))
      (Set.Iio (jc7_choosePeriod K hK e he))) :
    (olb_orbitLoop K hK e he).support.count (dartFace e) = 2 :=
  (jc7_LoopIsCycle K hK e he hp hinj).count_support






















theorem jc7_minimalPeriod_loopIsCycle (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1))
      (Set.Iio (dartOrbitPeriod K a))) :
    (mpl_orbitLoop K a).IsCycle :=
  mpl_orbitLoop_isCycle K a hp hinj





theorem jc7_dartOrbitWalk_isCycle (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    (dartOrbitWalk K a).IsCycle :=
  jc6_dartOrbitWalk_isCycle K hK a










theorem jc7_unitCell_faceInj :
    Set.InjOn (fun k => dartFace ((dartNext unitCell)^[k] ucBase.1))
      (Set.Iio (dartOrbitPeriod unitCell ucBase)) := by
  rw [unitCell_orbitPeriod_eq_four, show ucBase.1 = ucDart0 from rfl]
  exact unitCell_orbitFace_injOn






theorem jc7_unitCell_minimalPeriod_loopIsCycle : (mpl_orbitLoop unitCell ucBase).IsCycle :=
  jc7_minimalPeriod_loopIsCycle unitCell ucBase
    (by rw [unitCell_orbitPeriod_eq_four]; norm_num)
    jc7_unitCell_faceInj







































end Walls

end StatMech
