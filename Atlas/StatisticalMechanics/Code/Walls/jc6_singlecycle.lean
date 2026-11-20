/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Mathlib
import Code.Lattice.DartOrbit
import Code.Walls.jc5_singlecycle
import Code.Walls.jc5_footprintdartsfinite

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice
















theorem jc6_orbit_injOn_Iio (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    Set.InjOn (fun k => (dartNextSub K)^[k] a) (Set.Iio (dartOrbitPeriod K a)) :=
  jc5_orbit_injOn_Iio K a










theorem jc6_iterate_eq_iff (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {j k : ℕ} (hj : j < dartOrbitPeriod K a) (hk : k < dartOrbitPeriod K a) :
    (dartNextSub K)^[j] a = (dartNextSub K)^[k] a ↔ j = k :=
  jc5_visited_once K a hj hk



theorem jc6_orbit_distinct (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {j k : ℕ} (hj : j < dartOrbitPeriod K a) (hk : k < dartOrbitPeriod K a) (hjk : j ≠ k) :
    (dartNextSub K)^[j] a ≠ (dartNextSub K)^[k] a :=
  fun h => hjk ((jc6_iterate_eq_iff K a hj hk).mp h)


















theorem jc6_no_dart_recurs (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {d : {e : Dart // IsBoundaryDart K e}} {j k : ℕ}
    (hj : j < dartOrbitPeriod K a) (hk : k < dartOrbitPeriod K a)
    (hjd : (dartNextSub K)^[j] a = d) (hkd : (dartNextSub K)^[k] a = d) : j = k :=
  (jc6_iterate_eq_iff K a hj hk).mp (hjd.trans hkd.symm)





theorem jc6_recur_step_injOn (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (d : {e : Dart // IsBoundaryDart K e}) :
    Set.InjOn (id : ℕ → ℕ)
      {k | k ∈ Set.Iio (dartOrbitPeriod K a) ∧ (dartNextSub K)^[k] a = d} := by
  intro j hj k hk _
  exact jc6_no_dart_recurs K a hj.1 hk.1 hj.2 hk.2





theorem jc6_recur_step_subsingleton (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (d : {e : Dart // IsBoundaryDart K e}) :
    Subsingleton {k : ℕ // k < dartOrbitPeriod K a ∧ (dartNextSub K)^[k] a = d} :=
  ⟨fun j k => Subtype.ext (jc6_no_dart_recurs K a j.2.1 k.2.1 j.2.2 k.2.2)⟩

















theorem jc6_no_lframe_dart_recurs (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) {d : {e : Dart // IsBoundaryDart K e}}
    (_hd : jc5_ProbesEarFootprint r d.1) {j k : ℕ}
    (hj : j < dartOrbitPeriod K a) (hk : k < dartOrbitPeriod K a)
    (hjd : (dartNextSub K)^[j] a = d) (hkd : (dartNextSub K)^[k] a = d) : j = k :=
  jc6_no_dart_recurs K a hj hk hjd hkd





theorem jc6_lframe_recur_step_subsingleton (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    {d : {e : Dart // IsBoundaryDart K e}} (_hd : jc5_ProbesEarFootprint r d.1) :
    Subsingleton {k : ℕ // k < dartOrbitPeriod K a ∧ (dartNextSub K)^[k] a = d} :=
  jc6_recur_step_subsingleton K a d









theorem jc6_orbit_injOn_range (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    Set.InjOn (fun k => (dartNextSub K)^[k] a) (Finset.range (dartOrbitPeriod K a)) :=
  jc5_orbit_injOn_range K a




theorem jc6_orbit_darts_nodup (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    ((List.range (dartOrbitPeriod K a)).map (fun k => (dartNextSub K)^[k] a)).Nodup :=
  jc5_orbit_darts_nodup K a



theorem jc6_period_darts_card (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    letI : DecidableEq {e : Dart // IsBoundaryDart K e} := Classical.decEq _
    ((Finset.range (dartOrbitPeriod K a)).image (fun k => (dartNextSub K)^[k] a)).card
      = dartOrbitPeriod K a :=
  jc5_orbit_darts_card K a










theorem jc6_dartOrbitWalk_isCycle (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    (dartOrbitWalk K a).IsCycle :=
  jc5_dartOrbitWalk_isCycle K hK a

















def jc6_SingleCycle (K : Set (Site 2)) : Prop :=
  ∀ a : {e : Dart // IsBoundaryDart K e},
    Set.InjOn (fun k => (dartNextSub K)^[k] a) (Set.Iio (dartOrbitPeriod K a)) ∧
    (∀ {j k : ℕ}, j < dartOrbitPeriod K a → k < dartOrbitPeriod K a →
      ((dartNextSub K)^[j] a = (dartNextSub K)^[k] a ↔ j = k)) ∧
    (∀ {d : {e : Dart // IsBoundaryDart K e}} {j k : ℕ},
      j < dartOrbitPeriod K a → k < dartOrbitPeriod K a →
      (dartNextSub K)^[j] a = d → (dartNextSub K)^[k] a = d → j = k) ∧
    ((List.range (dartOrbitPeriod K a)).map (fun k => (dartNextSub K)^[k] a)).Nodup ∧
    (dartOrbitWalk K a).IsCycle






theorem jc6_singleCycle (K : Set (Site 2)) (hK : K.Finite) : jc6_SingleCycle K := by
  intro a
  exact ⟨jc6_orbit_injOn_Iio K a,
    fun hj hk => jc6_iterate_eq_iff K a hj hk,
    fun hj hk hjd hkd => jc6_no_dart_recurs K a hj hk hjd hkd,
    jc6_orbit_darts_nodup K a,
    jc6_dartOrbitWalk_isCycle K hK a⟩

































end Walls

end StatMech
