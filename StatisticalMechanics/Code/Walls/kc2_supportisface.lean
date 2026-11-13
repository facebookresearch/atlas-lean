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
import Code.Lattice.TurningNumber
import Code.Lattice.OrbitEncloses
import Code.Lattice.JordanSingleCycle
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.MinimalPeriodLoop

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice

















theorem kc2_mpl_orbitLoop_support_eq (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (mpl_orbitLoop K a).support
      = (List.range (dartOrbitPeriod K a + 1)).map
          (fun k => dartFace ((dartNext K)^[k] a.1)) := by
  rw [mpl_orbitLoop_support, mpl_orbitFaceLoop, SimpleGraph.Walk.support_copy,
    dartOrbitFaceWalk_support]
















theorem kc2_support_is_face (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {z : Site 2} (hz : z ∈ (mpl_orbitLoop K a).support) :
    ∃ i ≤ dartOrbitPeriod K a,
      z = dartFace ((dartNext K)^[i] a.1) ∧ IsBoundaryDart K ((dartNext K)^[i] a.1) := by
  rw [kc2_mpl_orbitLoop_support_eq, List.mem_map] at hz
  obtain ⟨k, hkrange, hk⟩ := hz
  rw [List.mem_range] at hkrange
  exact ⟨k, by omega, hk.symm, iterate_isBoundaryDart K a.1 a.2 k⟩




theorem kc2_support_is_face_exists (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {z : Site 2} (hz : z ∈ (mpl_orbitLoop K a).support) :
    ∃ i, z = dartFace ((dartNext K)^[i] a.1) ∧ IsBoundaryDart K ((dartNext K)^[i] a.1) := by
  obtain ⟨i, _, hzi, hbd⟩ := kc2_support_is_face K a hz
  exact ⟨i, hzi, hbd⟩















theorem kc2_dartFace_iterate_mem_support (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (n : ℕ) :
    dartFace ((dartNext K)^[n] a.1) ∈ (mpl_orbitLoop K a).support := by
  classical
  set p := dartOrbitPeriod K a with hp
  have hper : (dartNext K)^[p] a.1 = a.1 := orbit_iterate_period_eq K a
  have hppos : 0 < p := dartOrbitPeriod_pos K hK a
  have heq : (dartNext K)^[n] a.1 = (dartNext K)^[n % p] a.1 :=
    iterate_eq_mod_of_period (dartNext K) a.1 hper n
  rw [heq, mpl_orbitLoop_support, mpl_orbitFaceLoop, SimpleGraph.Walk.support_copy]
  exact dartFace_iterate_mem_dartOrbitFaceWalk_support K a.1 a.2 (le_of_lt (Nat.mod_lt _ hppos))






theorem kc2_support_iff (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) {z : Site 2} :
    z ∈ (mpl_orbitLoop K a).support ↔ ∃ i, z = dartFace ((dartNext K)^[i] a.1) := by
  constructor
  · intro hz
    obtain ⟨i, hzi, _⟩ := kc2_support_is_face_exists K a hz
    exact ⟨i, hzi⟩
  · rintro ⟨i, rfl⟩
    exact kc2_dartFace_iterate_mem_support K hK a i









theorem kc2_base_mem_support (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    dartFace a.1 ∈ (mpl_orbitLoop K a).support := by
  rw [kc2_mpl_orbitLoop_support_eq, List.mem_map]
  exact ⟨0, List.mem_range.mpr (by omega), by simp⟩

end Walls

end StatMech
