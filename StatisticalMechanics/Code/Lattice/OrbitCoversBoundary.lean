/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartOrbit
import Code.Lattice.ContourLinksExits
import Code.Lattice.InterfaceOrbit
import Code.Lattice.NoPinchDual
import Code.Lattice.NoDiagTouchClose
import Code.Lattice.StarHullWinding
import Code.Lattice.WindingEarInduction
import Code.Lattice.LexMinOrientation
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.StarHullPeriod
import Code.Lattice.StarHullFinite
import Code.Lattice.StarHullTurning

open Set SimpleGraph Function

namespace StatMech

namespace Lattice














theorem ocb_leftFence_data (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ z₀ ∈ K, IsBoundaryDart K (lmo_leftDartAt z₀) ∧ (lmo_leftDartAt z₀).dir = ![-1, 0] ∧
      (lmo_leftDartAt z₀).tail 0 = z₀ 0 ∧ (∀ w ∈ K, z₀ 0 ≤ w 0) := by
  obtain ⟨z₀, hz₀, hwest, _hsouth, hmin⟩ := lmo_lexMinCell K hK hne
  refine ⟨z₀, hz₀, lmo_leftDartAt_isBoundaryDart hz₀ hwest, lmo_leftDartAt_dir z₀, ?_, hmin⟩
  rw [lmo_leftDartAt_tail]












theorem ocb_on_orbit_index_lt_period (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) {e : Dart} {n : ℕ}
    (hn : (dartNext K)^[n] a.1 = e) :
    ∃ k < dartOrbitPeriod K a, (dartNext K)^[k] a.1 = e := by
  have hpos : 0 < dartOrbitPeriod K a := dartOrbitPeriod_pos K hK a
  refine ⟨n % dartOrbitPeriod K a, Nat.mod_lt _ hpos, ?_⟩
  
  have hsub : (dartNextSub K)^[n % dartOrbitPeriod K a] a = (dartNextSub K)^[n] a := by
    have := Function.iterate_mod_minimalPeriod_eq (f := dartNextSub K) (x := a)
      (n := n)
    simp only [dartOrbitPeriod]; exact this
  have hval := congrArg Subtype.val hsub
  rw [dartNextSub_iterate_val, dartNextSub_iterate_val] at hval
  rw [hval, hn]










theorem ocb_reachesLeftmost_of_leftFence_on_orbit (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z₀ : Site 2) (m : ℤ) (hm : z₀ 0 = m)
    (hon : ∃ n : ℕ, (dartNext K)^[n] a.1 = lmo_leftDartAt z₀) :
    lmo_OrbitReachesLeftmost K a m := by
  obtain ⟨n, hn⟩ := hon
  obtain ⟨k, hk, hke⟩ := ocb_on_orbit_index_lt_period K hK a hn
  refine lmo_reachesLeftmost_of_left_tail K a m hk ?_ ?_
  · 
    rw [hke, lmo_leftDartAt_tail, hm]
  · 
    rw [hke, lmo_leftDartAt_dir]







theorem ocb_windingWitness_of_leftFence_on_orbit (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z₀ : Site 2) (m : ℤ) (hm : z₀ 0 = m)
    (hmin : ∀ w ∈ K, m ≤ w 0)
    (hcyc : (mpl_orbitLoop K a).IsCycle)
    (hon : ∃ n : ℕ, (dartNext K)^[n] a.1 = lmo_leftDartAt z₀) :
    wei_WindingWitness K a :=
  lmo_windingWitness_of_reachesLeftmost K a m hmin hcyc
    (ocb_reachesLeftmost_of_leftFence_on_orbit K hK a z₀ m hm hon)













theorem ocb_leftFence_head {K : Set (Site 2)} {z₀ : Site 2}
    (hbd : IsBoundaryDart K (lmo_leftDartAt z₀)) :
    (lmo_leftDartAt z₀).head ∉ K := hbd.2






theorem ocb_leftFence_head_sameComponent_of_on_orbit {K : Set (Site 2)}
    (a : {e : Dart // IsBoundaryDart K e}) {z₀ : Site 2}
    (hbd : IsBoundaryDart K (lmo_leftDartAt z₀))
    (hon : ∃ n : ℕ, (dartNext K)^[n] a.1 = lmo_leftDartAt z₀) :
    ((hypercubicLattice 2).induce Kᶜ).Reachable
      ⟨a.1.head, a.2.2⟩ ⟨(lmo_leftDartAt z₀).head, hbd.2⟩ := by
  obtain ⟨n, hn⟩ := hon
  exact dartNext_orbit_head_sameComponent K a.1 (lmo_leftDartAt z₀) a.2 hbd hn












theorem ocb_leftFence_on_orbit_of_sameComponent {K : Set (Site 2)}
    (a : {e : Dart // IsBoundaryDart K e}) {z₀ : Site 2}
    (hbd : IsBoundaryDart K (lmo_leftDartAt z₀))
    (hInt : InterfaceConnected K)
    (hcomp : ((hypercubicLattice 2).induce Kᶜ).Reachable
      ⟨a.1.head, a.2.2⟩ ⟨(lmo_leftDartAt z₀).head, hbd.2⟩) :
    ∃ n : ℕ, (dartNext K)^[n] a.1 = lmo_leftDartAt z₀ :=
  hInt a.1 (lmo_leftDartAt z₀) a.2 hbd hcomp







theorem ocb_leftFence_on_orbit_iff_headSameComponent {K : Set (Site 2)}
    (a : {e : Dart // IsBoundaryDart K e}) {z₀ : Site 2}
    (hbd : IsBoundaryDart K (lmo_leftDartAt z₀))
    (hInt : InterfaceConnected K) :
    (∃ n : ℕ, (dartNext K)^[n] a.1 = lmo_leftDartAt z₀)
      ↔ ((hypercubicLattice 2).induce Kᶜ).Reachable
          ⟨a.1.head, a.2.2⟩ ⟨(lmo_leftDartAt z₀).head, hbd.2⟩ :=
  ⟨ocb_leftFence_head_sameComponent_of_on_orbit a hbd,
    ocb_leftFence_on_orbit_of_sameComponent a hbd hInt⟩




















theorem ocb_starHull_windingWitness_of_interfaceConnected (K : Set (Site 2)) (hK : K.Finite)
    (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull K) a)
    (hInt : InterfaceConnected (ndt_StarHull K)) :
    (∀ (z₀ : Site 2) (hbd : IsBoundaryDart (ndt_StarHull K) (lmo_leftDartAt z₀)),
        z₀ ∈ ndt_StarHull K → (∀ w ∈ ndt_StarHull K, z₀ 0 ≤ w 0) →
        ((hypercubicLattice 2).induce (ndt_StarHull K)ᶜ).Reachable
          ⟨a.1.head, a.2.2⟩ ⟨(lmo_leftDartAt z₀).head, hbd.2⟩) →
      wei_WindingWitness (ndt_StarHull K) a := by
  intro hreach
  have hSK : (ndt_StarHull K).Finite := starHull_finite K hK
  obtain ⟨z₀, hz₀, hbd, _hdir, _htail, hmin⟩ := ocb_leftFence_data (ndt_StarHull K) hSK
    (sht_starHull_nonempty K hne)
  have hcyc : (mpl_orbitLoop (ndt_StarHull K) a).IsCycle := shw_starHull_mpl_isCycle K a hp
  have hcomp := hreach z₀ hbd hz₀ hmin
  have hon : ∃ n : ℕ, (dartNext (ndt_StarHull K))^[n] a.1 = lmo_leftDartAt z₀ :=
    ocb_leftFence_on_orbit_of_sameComponent a hbd hInt hcomp
  exact ocb_windingWitness_of_leftFence_on_orbit (ndt_StarHull K) hSK a z₀ (z₀ 0) rfl hmin hcyc hon











theorem ocb_unitCell_reachesLeftmost : lmo_OrbitReachesLeftmost unitCell ucBase 0 :=
  lmo_unitCell_reachesLeftmost




theorem ocb_unitCell_windingWitness : wei_WindingWitness unitCell ucBase :=
  lmo_unitCell_windingWitness















































end Lattice

end StatMech
