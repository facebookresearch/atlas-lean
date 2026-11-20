/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.UniqueInfiniteComponent
import Code.Lattice.Clusters
import Code.Lattice.DartDef
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.ExteriorConnected
import Code.Lattice.OrbitWindingWitness

open Set SimpleGraph

namespace StatMech

namespace Walls

open StatMech.Lattice
open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}















theorem kc3_exists_farLeft_notMem {K F : Set (Site 2)} (hK : K.Finite) (hF : F.Finite) :
    ∃ q : Site 2, (∀ p ∈ F, q 0 ≤ p 0) ∧ q ∉ K := by
  obtain ⟨R, hR⟩ := finite_subset_box (K ∪ F) (hK.union hF)
  refine ⟨![-((R : ℤ) + 1), 0], ?_, ?_⟩
  · 
    intro p hp
    have hpbox : p ∈ box 2 R := hR (Or.inr hp)
    have h2 : |p 0| ≤ (R : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast (mem_box.mp hpbox) 0
    rw [abs_le] at h2
    simp only [Matrix.cons_val_zero]
    omega
  · 
    intro hqK
    have hqbox : (![-((R : ℤ) + 1), 0] : Site 2) ∈ box 2 R := hR (Or.inl hqK)
    have hc := (mem_box.mp hqbox) 0
    simp only [Matrix.cons_val_zero] at hc
    rw [Int.natAbs_neg,
      show ((R : ℤ) + 1).natAbs = R + 1 by rw [Int.natAbs_eq_iff]; left; push_cast; ring] at hc
    omega













theorem kc3_exists_farLeft_orbitLoop {K : Set (Site 2)} (a : {e : Dart // IsBoundaryDart K e})
    (hK : K.Finite) :
    ∃ q : Site 2, (∀ p ∈ (mpl_orbitLoop K a).support, q 0 ≤ p 0) ∧ q ∉ K := by
  obtain ⟨q, hleft, hqK⟩ := kc3_exists_farLeft_notMem hK (exc_loopSupport_finite K a)
  exact ⟨q, fun p hp => hleft p hp, hqK⟩





theorem kc3_exists_farLeft_clusterOrigin
    (hfin : (cluster 2 ω (origin 2)).Finite)
    (a : {e : Dart // IsBoundaryDart (cluster 2 ω (origin 2)) e}) :
    ∃ q : Site 2, (∀ p ∈ (mpl_orbitLoop (cluster 2 ω (origin 2)) a).support, q 0 ≤ p 0) ∧
      q ∉ cluster 2 ω (origin 2) :=
  kc3_exists_farLeft_orbitLoop a hfin














theorem kc3_farLeft_rayCount_zero {K : Set (Site 2)} (a : {e : Dart // IsBoundaryDart K e})
    {q : Site 2} (hq : ∀ p ∈ (mpl_orbitLoop K a).support, q 0 ≤ p 0) :
    jec_rayCount q (mpl_orbitLoop K a) = 0 :=
  jec_rayCount_eq_zero_of_right q (mpl_orbitLoop K a) hq




theorem kc3_farLeft_notMem_leftRegion {K : Set (Site 2)} (a : {e : Dart // IsBoundaryDart K e})
    {q : Site 2} (hq : ∀ p ∈ (mpl_orbitLoop K a).support, q 0 ≤ p 0) :
    q ∉ jec_leftRegion (mpl_orbitLoop K a) :=
  pww_farLeft_notMem_leftRegion (mpl_orbitLoop K a) hq















theorem kc3_escapeWalk_base_farLeft (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hoff : exc_OffSupportReachesExterior K a)
    {z : Site 2} (hzK : z ∉ K) (hzsupp : z ∉ (mpl_orbitLoop K a).support) :
    ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
      (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0) ∧
      jec_rayCount z0 (mpl_orbitLoop K a) = 0 := by
  obtain ⟨z0, p, hpoff, hfar⟩ := exc_offSupport_of_reaches K a hoff z hzK hzsupp
  exact ⟨z0, p, hpoff, hfar, kc3_farLeft_rayCount_zero a hfar⟩

end Walls

end StatMech
