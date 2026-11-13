/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.UniqueInfiniteComponent
import Code.Lattice.CrossingParity
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.EulerGeometricFaces
import Code.Lattice.JordanLeftRegionInterior
import Code.Lattice.FloodFillConnected
import Code.Lattice.InsideConnected
import Code.Lattice.OutsideConnected
import Code.Lattice.StraightWalk

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

variable {a : Site 2}










theorem woc_offSupport_eq_ffc (Vc : (hypercubicLattice 2).Walk a a) :
    offSupport Vc = ffc_offSupportLattice (oc_supportSet Vc) := by
  ext x y
  simp [offSupport_adj, ffc_offSupportLattice_adj, oc_mem_supportSet]


theorem woc_reachable_iff (Vc : (hypercubicLattice 2).Walk a a) {x y : Site 2} :
    (offSupport Vc).Reachable x y ↔
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y := by
  rw [woc_offSupport_eq_ffc]









theorem woc_beacon_row_ge_R (R : ℕ) : (R : ℤ) ≤ (beacon 2 R) 1 := by
  show (R : ℤ) ≤ (R : ℤ) + 1; omega


theorem woc_beacon_mem_exterior (R : ℕ) : beacon 2 R ∈ exterior 2 R :=
  beacon_mem_exterior R (by norm_num)






theorem woc_exterior_reachesTop (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {e : Site 2} (he : e ∈ exterior 2 R) :
    ∃ w : Site 2, (R : ℤ) ≤ w 1 ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable e w :=
  ⟨beacon 2 R, woc_beacon_row_ge_R R,
    oc_exterior_reachable_offSupport Vc R hsupp he (woc_beacon_mem_exterior R)⟩












theorem woc_reachesExterior_reachesTop (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z e : Site 2} (hzoff : z ∉ Vc.support)
    (he : e ∈ exterior 2 R)
    (hze : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e) :
    ∃ w : Site 2, (R : ℤ) ≤ w 1 ∧
      ∃ p : (hypercubicLattice 2).Walk z w, ∀ u ∈ p.support, u ∉ Vc.support := by
  obtain ⟨w, hwrow, hew⟩ := woc_exterior_reachesTop Vc R hsupp he
  have hzw : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z w := hze.trans hew
  obtain ⟨p, hp⟩ := (oc_offSupportLattice_reachable_iff Vc hzoff).mp hzw
  exact ⟨w, hwrow, p, hp⟩




theorem woc_reachesTop_of_reachesExterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) (h : oc_OutsideReachesExterior Vc R) :
    oc_OutsideReachesTop Vc R := by
  intro z hz
  obtain ⟨e, he, hze⟩ := h z hz
  
  have hzoff : z ∉ Vc.support := by
    rcases hze with ⟨w⟩
    cases w with
    | nil => exact oc_exterior_offSupport Vc R hsupp he
    | cons hadj _ => exact hadj.2.1
  exact woc_reachesExterior_reachesTop Vc R hsupp hzoff he hze







theorem woc_reachesTop_iff_reachesExterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    oc_OutsideReachesTop Vc R ↔ oc_OutsideReachesExterior Vc R :=
  ⟨oc_outsideReachesExterior_of_reachesTop Vc R hsupp,
    woc_reachesTop_of_reachesExterior Vc R hsupp⟩















theorem woc_infiniteComponent_outside (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {z e : Site 2} (hzoff : z ∉ Vc.support)
    (he : e ∈ exterior 2 R)
    (hze : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e) :
    z ∉ jec_leftRegion Vc := by
  
  have hze' : (offSupport Vc).Reachable z e := (woc_reachable_iff Vc).mpr hze
  
  have heout : e ∉ jec_leftRegion Vc := oc_exterior_outside Vc R hsupp he
  
  exact fun hz => heout ((inside_sameRegion_offSupport Vc hze' hzoff).mp hz)






theorem woc_interiorComponent_bounded (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {seed : Site 2} (hseed : seed ∈ jec_leftRegion Vc)
    (hsoff : seed ∉ Vc.support) :
    (offSupportComponent Vc seed).Finite :=
  (egf_leftRegion_finite Vc R hsupp).subset
    (offSupportComponent_subset_interior Vc hseed hsoff)



theorem woc_interior_not_reachesExterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {z : Site 2} (hzin : z ∈ jec_leftRegion Vc)
    (hzoff : z ∉ Vc.support) :
    ¬ ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
  rintro ⟨e, he, hze⟩
  exact woc_infiniteComponent_outside Vc R hsupp hzoff he hze hzin














def woc_OutsideReachesExterior_residue (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) : Prop :=
  ∀ z, z ∉ jec_leftRegion Vc →
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e


theorem woc_residue_eq (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) :
    woc_OutsideReachesExterior_residue Vc R ↔ oc_OutsideReachesExterior Vc R := Iff.rfl





theorem woc_reachesTop_of_residue (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) (h : woc_OutsideReachesExterior_residue Vc R) :
    oc_OutsideReachesTop Vc R :=
  woc_reachesTop_of_reachesExterior Vc R hsupp h




theorem woc_residue_iff_reachesTop (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) :
    woc_OutsideReachesExterior_residue Vc R ↔ oc_OutsideReachesTop Vc R :=
  (woc_reachesTop_iff_reachesExterior Vc R hsupp).symm



















noncomputable def woc_lexKey (v : Site 2) : ℤ ×ₗ ℤ := toLex (v 1, v 0)



theorem woc_component_has_lexMax (Vc : (hypercubicLattice 2).Walk a a) {seed : Site 2}
    (hfin : (offSupportComponent Vc seed).Finite) :
    ∃ m ∈ offSupportComponent Vc seed,
      ∀ v ∈ offSupportComponent Vc seed, woc_lexKey v ≤ woc_lexKey m := by
  have hne : (offSupportComponent Vc seed).Nonempty :=
    ⟨seed, seed_mem_offSupportComponent Vc seed⟩
  have hfne : hfin.toFinset.Nonempty := by rwa [Set.Finite.toFinset_nonempty]
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image hfin.toFinset woc_lexKey hfne
  refine ⟨m, by rwa [Set.Finite.mem_toFinset] at hm, ?_⟩
  intro v hv
  exact hmax v (by rwa [Set.Finite.mem_toFinset])




theorem woc_up_not_mem_of_lexMax (Vc : (hypercubicLattice 2).Walk a a) {seed m : Site 2}
    (hmax : ∀ v ∈ offSupportComponent Vc seed, woc_lexKey v ≤ woc_lexKey m) :
    (![m 0, m 1 + 1] : Site 2) ∉ offSupportComponent Vc seed := by
  intro hup
  have h := hmax _ hup
  unfold woc_lexKey at h
  rw [Prod.Lex.toLex_le_toLex] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rcases h with h | ⟨h1, h2⟩ <;> omega









theorem woc_extreme_up_onSupport (Vc : (hypercubicLattice 2).Walk a a) {seed m : Site 2}
    (hsoff : seed ∉ Vc.support) (hm : m ∈ offSupportComponent Vc seed)
    (hmax : ∀ v ∈ offSupportComponent Vc seed, woc_lexKey v ≤ woc_lexKey m) :
    (![m 0, m 1 + 1] : Site 2) ∈ Vc.support := by
  by_contra hupoff
  
  have hmoff : m ∉ Vc.support := offSupportComponent_offSupport Vc hsoff hm
  
  have hmeq : m = ![m 0, m 1] := by ext i; fin_cases i <;> simp
  
  have hadj : (hypercubicLattice 2).Adj m (![m 0, m 1 + 1]) := by
    rw [hmeq]; exact sw_adj_vertSucc (m 0) (m 1)
  
  have hadj' : (offSupport Vc).Adj m (![m 0, m 1 + 1]) := ⟨hadj, hmoff, hupoff⟩
  
  have hreach : (offSupport Vc).Reachable seed (![m 0, m 1 + 1]) :=
    ((mem_offSupportComponent Vc).mp hm).trans hadj'.reachable
  have hupmem : (![m 0, m 1 + 1] : Site 2) ∈ offSupportComponent Vc seed :=
    (mem_offSupportComponent Vc).mpr hreach
  exact woc_up_not_mem_of_lexMax Vc hmax hupmem



























def woc_NoBoundedEvenComponent (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∀ z : Site 2, z ∉ Vc.support → (offSupportComponent Vc z).Finite → z ∈ jec_leftRegion Vc








theorem woc_infinite_reachesExterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    {z : Site 2} (_hzoff : z ∉ Vc.support)
    (hinf : (offSupportComponent Vc z).Infinite) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
  
  have hnotsub : ¬ offSupportComponent Vc z ⊆ box 2 R := by
    intro hsub
    exact hinf ((box_finite 2 R).subset hsub)
  rw [Set.not_subset] at hnotsub
  obtain ⟨e, hemem, hebox⟩ := hnotsub
  have heext : e ∈ exterior 2 R := by rw [exterior_eq_compl_box]; exact hebox
  
  have hze : (offSupport Vc).Reachable z e := (mem_offSupportComponent Vc).mp hemem
  exact ⟨e, heext, (woc_reachable_iff Vc).mp hze⟩







theorem woc_residue_of_noBoundedEven (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hoffOut : ∀ z, z ∉ jec_leftRegion Vc → z ∉ Vc.support)
    (h : woc_NoBoundedEvenComponent Vc) :
    woc_OutsideReachesExterior_residue Vc R := by
  intro z hz
  have hzoff : z ∉ Vc.support := hoffOut z hz
  
  have hinf : (offSupportComponent Vc z).Infinite := by
    intro hfin
    exact hz (h z hzoff hfin)
  exact woc_infinite_reachesExterior Vc R hzoff hinf






theorem woc_reachesTop_of_noBoundedEven (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hoffOut : ∀ z, z ∉ jec_leftRegion Vc → z ∉ Vc.support)
    (h : woc_NoBoundedEvenComponent Vc) :
    oc_OutsideReachesTop Vc R :=
  woc_reachesTop_of_residue Vc R hsupp (woc_residue_of_noBoundedEven Vc R hoffOut h)









theorem woc_two_components_of_noBoundedEven (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
    (hInOff : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support)
    (hoffOut : ∀ z, z ∉ jec_leftRegion Vc → z ∉ Vc.support)
    (h : woc_NoBoundedEvenComponent Vc) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 :=
  oc_two_components_of_reachesTop Vc R hsupp hp hq hInOff
    (woc_reachesTop_of_noBoundedEven Vc R hsupp hoffOut h)
















theorem woc_interior_satisfies_residue (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {z : Site 2} (hzin : z ∈ jec_leftRegion Vc)
    (hzoff : z ∉ Vc.support) :
    (offSupportComponent Vc z).Finite ∧ z ∈ jec_leftRegion Vc :=
  ⟨woc_interiorComponent_bounded Vc R hsupp hzin hzoff, hzin⟩

end Lattice

end StatMech
