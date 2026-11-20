/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Code.BeffaraDC.ClusterMoments
import Code.Percolation.SurfaceReassembly
import Code.Percolation.DctDifferential
import Code.Percolation.BurtonKeane

open scoped BigOperators NNReal ENNReal
open Set Filter Topology MeasureTheory

namespace StatMech

namespace BeffaraDC

open StatMech.Percolation StatMech.Lattice

variable {d : ℕ}












theorem geometricTail_of_expDecay {f : ℕ → ℝ} {C c : ℝ} (hc : 0 < c)
    (hf : ∀ n, f n ≤ C * Real.exp (-c * n)) :
    ∃ r, 0 < r ∧ r < 1 ∧ ∀ n, f n ≤ C * r ^ n := by
  refine ⟨Real.exp (-c), Real.exp_pos _, ?_, fun n => ?_⟩
  · rw [Real.exp_lt_one_iff]; linarith
  · have hrw : Real.exp (-c * n) = Real.exp (-c) ^ n := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [← hrw]; exact hf n





















theorem crossProb_geometricTail (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (hphi : phi d p hp S < 1)
    (L : ℕ) (hL : 1 ≤ L) (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) :
    ∃ C, 0 < C ∧ ∃ r, 0 < r ∧ r < 1 ∧
      ∀ n, crossProb d p hp n ≤ C * r ^ n := by
  obtain ⟨c, hc, C, hC, hbound⟩ :=
    subcritical_decay_unconditional p hp S hoS hphi L hL hSbox
  obtain ⟨r, hr0, hr1, hgeo⟩ := geometricTail_of_expDecay hc hbound
  exact ⟨C, hC, r, hr0, hr1, hgeo⟩



















noncomputable def clusterRadiusDomination (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (hphi : phi d p hp S < 1)
    (L : ℕ) (hL : 1 ≤ L) (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) :
    ClusterSizeDomination :=
  let h := crossProb_geometricTail p hp S hoS hphi L hL hSbox
  clusterSizeDomination_of_geometricTail (dist := fun n => crossProb d p hp n)
    (C := h.choose) (r := h.choose_spec.2.choose)
    (fun n => crossProb_nonneg d p hp n)
    h.choose_spec.2.choose_spec.1.le
    h.choose_spec.2.choose_spec.2.1
    h.choose_spec.2.choose_spec.2.2

@[simp] theorem clusterRadiusDomination_dist (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (hphi : phi d p hp S < 1)
    (L : ℕ) (hL : 1 ≤ L) (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) :
    (clusterRadiusDomination p hp S hoS hphi L hL hSbox).dist
      = fun n => crossProb d p hp n := rfl













theorem clusterRadiusMoment_summable (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (hphi : phi d p hp S < 1)
    (L : ℕ) (hL : 1 ≤ L) (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) (d' : ℕ) :
    Summable (fun n : ℕ => (n : ℝ) ^ d' * crossProb d p hp n) :=
  (clusterRadiusDomination p hp S hoS hphi L hL hSbox).summand_summable d'









theorem clusterRadiusMoment_lt_top (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (hphi : phi d p hp S < 1)
    (L : ℕ) (hL : 1 ≤ L) (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) (d' : ℕ) :
    ∃ C r, 0 ≤ r ∧ r < 1 ∧
      clusterMoment (fun n => crossProb d p hp n) d'
        ≤ ∑' n : ℕ, (n : ℝ) ^ d' * (C * r ^ n) := by
  set D := clusterRadiusDomination p hp S hoS hphi L hL hSbox with hD
  refine ⟨D.const, D.rate, D.rate_nonneg, D.rate_lt_one, ?_⟩
  have := D.allMoments_lt_top d'
  simpa [hD] using this


theorem clusterRadiusMoment_nonneg (p : ℝ≥0) (hp : p ≤ 1) (d' : ℕ) :
    0 ≤ clusterMoment (fun n => crossProb d p hp n) d' :=
  clusterMoment_nonneg (fun n => crossProb_nonneg d p hp n) d'













theorem crossingEvent_eq_cluster_not_subset (n : ℕ)
    (ω : ConfigSpace (Sym2 (Site d))) :
    ω ∈ crossingEvent d n ↔ ¬ (cluster d ω (origin d) ⊆ box d (n - 1)) := by
  rw [mem_crossingEvent]
  constructor
  · rintro ⟨v, hconn, hv⟩ hsub
    exact hv (hsub hconn)
  · intro h
    rw [Set.not_subset] at h
    obtain ⟨v, hv, hvb⟩ := h
    exact ⟨v, hv, hvb⟩






theorem cluster_finite_card_le_of_subset {m : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    (hsub : cluster d ω (origin d) ⊆ box d m) :
    ∃ hfin : (cluster d ω (origin d)).Finite, hfin.toFinset.card ≤ (boxFinset d m).card := by
  refine ⟨(box_finite d m).subset hsub, ?_⟩
  refine Finset.card_le_card (fun y hy => ?_)
  rw [Set.Finite.mem_toFinset] at hy
  rw [mem_boxFinset]
  exact hsub hy











theorem clusterSize_large_subset_crossing (n : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (hsize : ¬ ∃ hfin : (cluster d ω (origin d)).Finite,
        hfin.toFinset.card ≤ (boxFinset d (n - 1)).card) :
    ω ∈ crossingEvent d n := by
  rw [crossingEvent_eq_cluster_not_subset]
  intro hsub
  exact hsize (cluster_finite_card_le_of_subset ω hsub)







theorem clusterSize_le_boxCard_of_finite (ω : ConfigSpace (Sym2 (Site d)))
    (hfin : (cluster d ω (origin d)).Finite) :
    ∃ m, hfin.toFinset.card ≤ (boxFinset d m).card := by
  obtain ⟨m, hm⟩ := finite_subset_box (cluster d ω (origin d)) hfin
  refine ⟨m, Finset.card_le_card (fun y hy => ?_)⟩
  rw [Set.Finite.mem_toFinset] at hy
  rw [mem_boxFinset]
  exact hm hy














def clusterSizeLargeEvent (d n : ℕ) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | ¬ ∃ hfin : (cluster d ω (origin d)).Finite,
      hfin.toFinset.card ≤ (boxFinset d (n - 1)).card}




theorem clusterSizeLargeEvent_subset_crossing (n : ℕ) :
    clusterSizeLargeEvent d n ⊆ crossingEvent d n :=
  fun _ hω => clusterSize_large_subset_crossing n _ hω





theorem clusterSizeLargeProb_le_crossProb (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (clusterSizeLargeEvent d n)
      ≤ crossProb d p hp n :=
  measureReal_mono (clusterSizeLargeEvent_subset_crossing n) (measure_ne_top _ _)








theorem clusterSizeTail_geometricTail (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (hphi : phi d p hp S < 1)
    (L : ℕ) (hL : 1 ≤ L) (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) :
    ∃ C, 0 < C ∧ ∃ r, 0 < r ∧ r < 1 ∧
      ∀ n, (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
              (clusterSizeLargeEvent d n)
            ≤ C * r ^ n := by
  obtain ⟨C, hC, r, hr0, hr1, hgeo⟩ :=
    crossProb_geometricTail p hp S hoS hphi L hL hSbox
  refine ⟨C, hC, r, hr0, hr1, fun n => ?_⟩
  exact le_trans (clusterSizeLargeProb_le_crossProb p hp n) (hgeo n)








noncomputable def clusterSizeDomination (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (hphi : phi d p hp S < 1)
    (L : ℕ) (hL : 1 ≤ L) (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) :
    ClusterSizeDomination :=
  let h := clusterSizeTail_geometricTail p hp S hoS hphi L hL hSbox
  clusterSizeDomination_of_geometricTail
    (dist := fun n => (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (clusterSizeLargeEvent d n))
    (C := h.choose) (r := h.choose_spec.2.choose)
    (fun _ => measureReal_nonneg)
    h.choose_spec.2.choose_spec.1.le
    h.choose_spec.2.choose_spec.2.1
    h.choose_spec.2.choose_spec.2.2









theorem clusterSizeMoment_lt_top (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (hphi : phi d p hp S < 1)
    (L : ℕ) (hL : 1 ≤ L) (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) (d' : ℕ) :
    ∃ C r, 0 ≤ r ∧ r < 1 ∧
      clusterMoment (fun n => (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
            (clusterSizeLargeEvent d n)) d'
        ≤ ∑' n : ℕ, (n : ℝ) ^ d' * (C * r ^ n) := by
  set D := clusterSizeDomination p hp S hoS hphi L hL hSbox with hD
  refine ⟨D.const, D.rate, D.rate_nonneg, D.rate_lt_one, ?_⟩
  have := D.allMoments_lt_top d'
  simpa [hD] using this

end BeffaraDC

end StatMech
