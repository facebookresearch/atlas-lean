/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.CrossingParity
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.OrbitExteriorEven
import Code.Lattice.WindingEarInduction
import Code.Lattice.JordanSeparationFull
import Code.Lattice.ClosedContourSeparation
import Code.Lattice.BdEdgeMatchClose
import Code.Lattice.BdEdgeMatchStarHull
import Code.Lattice.UniqueInfiniteComponent
import Code.Walls.jc8core
import Code.Walls.jc8crossparityleftregion

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice
















theorem jc9_crossCount_parity_side (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {x y : Site 2} (w : (hypercubicLattice 2).Walk x y) :
    Even (crossCount (jec_leftRegion (mpl_orbitLoop K a)) w) ↔
      (x ∈ jec_leftRegion (mpl_orbitLoop K a) ↔ y ∈ jec_leftRegion (mpl_orbitLoop K a)) :=
  crossCount_parity (jec_leftRegion (mpl_orbitLoop K a)) w






theorem jc9_crossCount_ge_one_of_opposite_side (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y)
    (hx : x ∈ jec_leftRegion (mpl_orbitLoop K a))
    (hy : y ∉ jec_leftRegion (mpl_orbitLoop K a)) :
    1 ≤ crossCount (jec_leftRegion (mpl_orbitLoop K a)) w := by
  rcases Nat.eq_zero_or_pos (crossCount (jec_leftRegion (mpl_orbitLoop K a)) w) with h0 | hp
  · exfalso
    have heven : Even (crossCount (jec_leftRegion (mpl_orbitLoop K a)) w) := by
      rw [h0]; exact Nat.even_iff.mpr rfl
    exact hy ((jc9_crossCount_parity_side K a w).mp heven |>.mp hx)
  · exact hp













theorem jc9_exists_farLeft_notMem {K F : Set (Site 2)} (hK : K.Finite) (hF : F.Finite) :
    ∃ q : Site 2, (∀ p ∈ F, q 0 ≤ p 0) ∧ q ∉ K := by
  obtain ⟨R, hR⟩ := finite_subset_box (K ∪ F) (hK.union hF)
  refine ⟨![-((R : ℤ) + 1), 0], ?_, ?_⟩
  · intro p hp
    have hpbox : p ∈ box 2 R := hR (Or.inr hp)
    have h2 : |p 0| ≤ (R : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast (mem_box.mp hpbox) 0
    rw [abs_le] at h2
    simp only [Matrix.cons_val_zero]
    omega
  · intro hqK
    have hqbox : (![-((R : ℤ) + 1), 0] : Site 2) ∈ box 2 R := hR (Or.inl hqK)
    have hc := (mem_box.mp hqbox) 0
    simp only [Matrix.cons_val_zero] at hc
    rw [Int.natAbs_neg,
      show ((R : ℤ) + 1).natAbs = R + 1 by rw [Int.natAbs_eq_iff]; left; push_cast; ring] at hc
    omega



theorem jc9_orbitLoop_support_finite (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    {p : Site 2 | p ∈ (mpl_orbitLoop K a).support}.Finite :=
  List.finite_toSet _





theorem jc9_farLeft_even (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hfar : ∀ p ∈ (mpl_orbitLoop K a).support, z 0 ≤ p 0) :
    Even (jec_rayCount z (mpl_orbitLoop K a)) := by
  rw [jec_rayCount_eq_zero_of_right z (mpl_orbitLoop K a) hfar]
  exact Nat.even_iff.mpr rfl













theorem jc9_exterior_even (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) {z z0 : Site 2}
    (p : (hypercubicLattice 2).Walk z z0)
    (hp : ∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support)
    (hfar : ∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0) :
    Even (jec_rayCount z (mpl_orbitLoop K a)) :=
  (oee_rayParity_const_along_walk (mpl_orbitLoop K a) p hp).mpr (jc9_farLeft_even K a z0 hfar)







theorem jc9_outsideHalf (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
      (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)) :
    ∀ z, z ∉ K → Even (jec_rayCount z (mpl_orbitLoop K a)) := by
  intro z hz
  obtain ⟨z0, p, hp, hfar⟩ := hExt z hz
  exact jc9_exterior_even K a p hp hfar
















theorem jc9_inside_odd (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {z0 : Site 2} (hz0K : z0 ∈ K)
    (hodd0 : ¬ Even (jec_rayCount z0 (mpl_orbitLoop K a)))
    (hInt : ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support)) :
    ∀ z, z ∈ K → ¬ Even (jec_rayCount z (mpl_orbitLoop K a)) :=
  wei_insideHalf_of_windingWitness K a hz0K hodd0 hInt














theorem jc9_clusterEqLeftRegion_of_windingWitness (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
      (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0))
    {z0 : Site 2} (hz0K : z0 ∈ K)
    (hodd0 : ¬ Even (jec_rayCount z0 (mpl_orbitLoop K a)))
    (hInt : ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support)) :
    K = jec_leftRegion (mpl_orbitLoop K a) :=
  ccs_cluster_eq_leftRegion (mpl_orbitLoop K a)
    (jc9_inside_odd K a hz0K hodd0 hInt)
    (jc9_outsideHalf K a hExt)




















theorem jc9_bdEdgeMatch_of_windingWitness (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
      (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0))
    {z0 : Site 2} (hz0K : z0 ∈ K)
    (hodd0 : ¬ Even (jec_rayCount z0 (mpl_orbitLoop K a)))
    (hInt : ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support)) :
    pww_BdEdgeMatch K (mpl_orbitLoop K a) :=
  pbs_bdEdgeMatch_of_leftRegion_eq (mpl_orbitLoop K a)
    (jc9_clusterEqLeftRegion_of_windingWitness K a hExt hz0K hodd0 hInt)













theorem jc9_bdEdgeMatch_iff_setIdentity (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    pww_BdEdgeMatch K (mpl_orbitLoop K a) ↔
      (K = jec_leftRegion (mpl_orbitLoop K a) ∨ K = (jec_leftRegion (mpl_orbitLoop K a))ᶜ) :=
  pbs_bdEdgeMatch_iff_setIdentity (mpl_orbitLoop K a)



theorem jc9_bdEdgeMatch_of_leftRegion_eq (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (h : K = jec_leftRegion (mpl_orbitLoop K a)) :
    pww_BdEdgeMatch K (mpl_orbitLoop K a) :=
  pbs_bdEdgeMatch_of_leftRegion_eq (mpl_orbitLoop K a) h





theorem jc9_bdEdgeMatch_iff_leftRegion_eq (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hsupp : ∀ p ∈ (mpl_orbitLoop K a).support, p ∈ box 2 R) (hKfin : K.Finite) :
    pww_BdEdgeMatch K (mpl_orbitLoop K a) ↔ K = jec_leftRegion (mpl_orbitLoop K a) :=
  bemc_minimalLoop_bdEdgeMatch_iff_leftRegion_eq K a R hsupp hKfin
















theorem jc9_unitCell_bdEdgeMatch :
    pww_BdEdgeMatch unitCell (mpl_orbitLoop unitCell ucBase) :=
  jsf_unitCell_bdEdgeMatch





theorem jc9_unitCell_eq_leftRegion :
    unitCell = jec_leftRegion (mpl_orbitLoop unitCell ucBase) :=
  jsf_unitCell_eq_leftRegion





theorem jc9_unitCell_windingWitness :
    ¬ Even (jec_rayCount (![0, 0] : Site 2) (mpl_orbitLoop unitCell ucBase)) :=
  jsf_unitCell_inside_odd (![0, 0] : Site 2) origin_mem_unitCell















theorem jc9_FaceInsideInterval_iff_clusterInterval (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (h : K = jec_leftRegion (olb_orbitLoop K hK e he)) :
    jc8c_FaceInsideInterval K hK e he ↔
      (∀ i j k : ℕ, i < j → j < k →
        dartFace ((dartNext K)^[i] e) ∈ K →
        dartFace ((dartNext K)^[k] e) ∈ K →
        dartFace ((dartNext K)^[j] e) ∈ K) := by
  unfold jc8c_FaceInsideInterval
  rw [← h]










def jc9_InteriornessInputs (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (z0 : Site 2) : Prop :=
  (∀ z, z ∉ K → ∃ z1 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z1,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
      (∀ q ∈ (mpl_orbitLoop K a).support, z1 0 ≤ q 0)) ∧
  z0 ∈ K ∧
  (¬ Even (jec_rayCount z0 (mpl_orbitLoop K a))) ∧
  (∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support))



theorem jc9_bdEdgeMatch_of_inputs (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {z0 : Site 2} (h : jc9_InteriornessInputs K a z0) :
    pww_BdEdgeMatch K (mpl_orbitLoop K a) := by
  obtain ⟨hExt, hz0K, hodd0, hInt⟩ := h
  exact jc9_bdEdgeMatch_of_windingWitness K a hExt hz0K hodd0 hInt




theorem jc9_inputs_realised_unitCell :
    pww_BdEdgeMatch unitCell (mpl_orbitLoop unitCell ucBase) :=
  jc9_unitCell_bdEdgeMatch













































end Walls

end StatMech
