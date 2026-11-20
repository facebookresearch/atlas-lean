/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































import Mathlib
import Code.Lattice.DartOrbit
import Code.Walls.jc4_dartnextperm

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice


















theorem jc5_orbit_injOn_Iio (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    Set.InjOn (fun k => (dartNextSub K)^[k] a) (Set.Iio (dartOrbitPeriod K a)) := by
  intro j hj k hk h
  exact Function.iterate_injOn_Iio_minimalPeriod (f := dartNextSub K) (x := a)
    (Set.mem_Iio.mpr (Set.mem_Iio.mp hj)) (Set.mem_Iio.mpr (Set.mem_Iio.mp hk)) h












theorem jc5_visited_once (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {j k : ℕ} (hj : j < dartOrbitPeriod K a) (hk : k < dartOrbitPeriod K a) :
    (dartNextSub K)^[j] a = (dartNextSub K)^[k] a ↔ j = k :=
  Function.iterate_eq_iterate_iff_of_lt_minimalPeriod (f := dartNextSub K) (x := a) hj hk




theorem jc5_orbit_distinct (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {j k : ℕ} (hj : j < dartOrbitPeriod K a) (hk : k < dartOrbitPeriod K a) (hjk : j ≠ k) :
    (dartNextSub K)^[j] a ≠ (dartNextSub K)^[k] a := by
  intro h
  exact hjk ((jc5_visited_once K a hj hk).mp h)









theorem jc5_orbit_injOn_range (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    Set.InjOn (fun k => (dartNextSub K)^[k] a) (Finset.range (dartOrbitPeriod K a)) := by
  intro j hj k hk h
  exact jc5_orbit_injOn_Iio K a (by simpa using Finset.mem_range.mp hj)
    (by simpa using Finset.mem_range.mp hk) h








theorem jc5_orbit_darts_nodup (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    ((List.range (dartOrbitPeriod K a)).map (fun k => (dartNextSub K)^[k] a)).Nodup := by
  apply List.Nodup.map_on (l := List.range (dartOrbitPeriod K a))
    (f := fun k => (dartNextSub K)^[k] a)
  · intro j hj k hk h
    exact jc5_orbit_injOn_Iio K a
      (Set.mem_Iio.mpr (List.mem_range.mp hj)) (Set.mem_Iio.mpr (List.mem_range.mp hk)) h
  · exact List.nodup_range





theorem jc5_orbit_darts_card (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    letI : DecidableEq {e : Dart // IsBoundaryDart K e} := Classical.decEq _
    ((Finset.range (dartOrbitPeriod K a)).image (fun k => (dartNextSub K)^[k] a)).card
      = dartOrbitPeriod K a := by
  letI : DecidableEq {e : Dart // IsBoundaryDart K e} := Classical.decEq _
  rw [Finset.card_image_of_injOn (jc5_orbit_injOn_range K a), Finset.card_range]












theorem jc5_dartOrbitWalk_isCycle (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    (dartOrbitWalk K a).IsCycle :=
  jc4_dartOrbitWalk_isCycle K hK a





theorem jc5_dartOrbitWalk_support_tail_nodup (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    (dartOrbitWalk K a).support.tail.Nodup :=
  dartOrbitWalk_support_tail_nodup K hK a
















def jc5_SingleCycle (K : Set (Site 2)) : Prop :=
  ∀ a : {e : Dart // IsBoundaryDart K e},
    Set.InjOn (fun k => (dartNextSub K)^[k] a) (Set.Iio (dartOrbitPeriod K a)) ∧
    (∀ {j k : ℕ}, j < dartOrbitPeriod K a → k < dartOrbitPeriod K a →
      ((dartNextSub K)^[j] a = (dartNextSub K)^[k] a ↔ j = k)) ∧
    ((List.range (dartOrbitPeriod K a)).map (fun k => (dartNextSub K)^[k] a)).Nodup ∧
    (dartOrbitWalk K a).IsCycle







theorem jc5_singleCycle (K : Set (Site 2)) (hK : K.Finite) : jc5_SingleCycle K := by
  intro a
  exact ⟨jc5_orbit_injOn_Iio K a,
    fun hj hk => jc5_visited_once K a hj hk,
    jc5_orbit_darts_nodup K a,
    jc5_dartOrbitWalk_isCycle K hK a⟩






























end Walls

end StatMech
