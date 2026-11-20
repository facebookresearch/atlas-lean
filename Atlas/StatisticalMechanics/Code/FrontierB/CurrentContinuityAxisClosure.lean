/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierB.MixedCurrentAxisPersistence
import Code.FrontierB.CurrentContinuityMagnetizationFK

open Filter MeasureTheory Set Topology

namespace StatMech.FrontierB

open ConfigSpace FK Ising Lattice Percolation Sharpness
open StatMech.IsingFK
open StatMech.OSSS.FKSharpnessWeightedPhaseTransport

variable {d : Nat}



theorem freeInfiniteVolume_noPercolation_of_currentContinuityFreeAxisLROZero
    (beta : Real) (hbeta : 0 < beta) (hd : 1 ≤ d)
    (hLRO : CurrentContinuityFreeAxisLROZero d hd beta) :
    (freeInfiniteVolume d
        (p := 1 - Real.exp (-2 * beta)) (q := 2)
        (by exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
        (by linarith [Real.exp_pos (-2 * beta)])
        (by norm_num : (0 : Real) < 2) : Measure _).real
      (percolationEvent d) = 0 := by
  let p : Real := 1 - Real.exp (-2 * beta)
  have hp : 0 < p := by
    dsimp [p]
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hp1 : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-2 * beta)]
  let phi : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))) :=
    freeInfiniteVolume d hp hp1 (by norm_num : (0 : Real) < 2)
  let mu := (phi : Measure (ConfigSpace (Sym2 (Site d))))
  let E := clusterInfiniteEvent d (Percolation.origin d)
  change mu.real (percolationEvent d) = 0
  apply le_antisymm
  · by_contra hne
    have htheta : 0 < mu.real E := by
      simpa [E] using (lt_of_not_ge hne)
    have hcorr := freeInfiniteVolume_eventPairCorrelationAverage_tendsto
      hd hp hp1 E E (measurableSet_clusterInfiniteEvent (Percolation.origin d))
        (measurableSet_clusterInfiniteEvent (Percolation.origin d))
    have huniq : mu (atLeastTwoInfinite d) = 0 := by
      dsimp [mu, phi]
      exact (freeInfinite_q2_canonical_uniqueness_all_parameters
        hd hp hp1).2.1
    have hterm : Tendsto (fun k : Nat =>
        mu.real (E ∩ shift (FK.freeAxisTranslationPower hd k) ⁻¹' E))
        atTop (nhds 0) := by
      rw [Metric.tendsto_atTop]
      intro epsilon hepsilon
      obtain ⟨K, hK⟩ := hLRO epsilon hepsilon
      refine ⟨max K 1, ?_⟩
      intro k hk
      have hkK : K ≤ k := (le_max_left K 1).trans hk
      have hk1 : 1 ≤ k := (le_max_right K 1).trans hk
      have hxo : Percolation.origin d ≠ currentContinuityAxisSite hd k := by
        intro h
        have hcoord := congrFun h ⟨0, hd⟩
        simp [currentContinuityAxisSite, FK.freeAxisTranslationPower,
          smul_site_apply, Percolation.origin] at hcoord
        omega
      have hshift :
          (shift (FK.freeAxisTranslationPower hd k) :
            ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹' E =
            clusterInfiniteEvent d (currentContinuityAxisSite hd k) := by
        simpa [E, currentContinuityAxisSite] using
          (shift_preimage_clusterInfiniteEvent (d := d)
            (FK.freeAxisTranslationPower hd k)
            (currentContinuityAxisSite hd k))
      have hinter : mu.real
          (E ∩ shift (FK.freeAxisTranslationPower hd k) ⁻¹' E) ≤
          infiniteTwoPointReal mu (Percolation.origin d)
            (currentContinuityAxisSite hd k) := by
        rw [hshift]
        exact infinite_cluster_inter_le_twoPoint mu huniq
          (Percolation.origin d) (currentContinuityAxisSite hd k)
      have heq := currentContinuityFreeTwoPoint_eq_freeInfiniteTwoPoint
        beta hbeta hd (Percolation.origin d) (currentContinuityAxisSite hd k) hxo
      have hsmall := hK k hkK
      have hfree0 : 0 ≤ currentContinuityFreeTwoPoint d beta (Percolation.origin d)
          (currentContinuityAxisSite hd k) := by
        rw [heq]
        exact measureReal_nonneg
      rw [abs_of_nonneg hfree0] at hsmall
      rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
      rw [← heq] at hinter
      exact hinter.trans_lt hsmall
    have hmean0 := hterm.cesaro
    have hcorr' : Tendsto (fun n : Nat => (n : Real)⁻¹ *
        ∑ k ∈ Finset.range n,
          mu.real (E ∩ shift (FK.freeAxisTranslationPower hd k) ⁻¹' E))
        atTop (nhds (mu.real E * mu.real E)) := by
      simpa only [mu, phi] using hcorr
    have hzero : mu.real E * mu.real E = 0 :=
      tendsto_nhds_unique hcorr' hmean0
    nlinarith
  · exact measureReal_nonneg




theorem currentContinuity_magnetization_and_phase_eq_of_freeAxisLROZero
    (beta : Real) (hbeta : 0 < beta) (hd : 1 ≤ d)
    (hLRO : CurrentContinuityFreeAxisLROZero d hd beta) :
    (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real
          (percolationEvent d) = 0 ∧
      (freeInfiniteVolume d
          (p := 1 - Real.exp (-2 * beta)) (q := 2)
          (by exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
          (by linarith [Real.exp_pos (-2 * beta)])
          (by norm_num : (0 : Real) < 2) :
            Measure (ConfigSpace (Sym2 (Site d)))) =
        (wiredInfiniteVolume d
          (p := 1 - Real.exp (-2 * beta)) (q := 2)
          (by exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
          (by linarith [Real.exp_pos (-2 * beta)])
          (by norm_num : (0 : Real) < 2) :
            Measure (ConfigSpace (Sym2 (Site d)))) ∧
      magnetization d beta = 0 ∧
      (plusState d beta 0 : Measure (ConfigSpace (Site d))) =
        (minusState d beta 0 : Measure (ConfigSpace (Site d))) := by
  let p : Real := 1 - Real.exp (-2 * beta)
  have hp : 0 < p := by
    dsimp [p]
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hp1 : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-2 * beta)]
  have hnoperco := currentContinuity_no_percolation_of_freeAxisLROZero
    hd beta hbeta hLRO
  have hfk :=
    currentContinuity_freeInfiniteVolume_eq_wiredInfiniteVolume_of_noPercolation
      beta hbeta hd hnoperco
  have hfree :=
    freeInfiniteVolume_noPercolation_of_currentContinuityFreeAxisLROZero
      beta hbeta hd hLRO
  have hwired :
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : Real) < 2) :
        Measure _).real (percolationEvent d) = 0 := by
    have hmass := congrArg
      (fun rho : Measure (ConfigSpace (Sym2 (Site d))) =>
        rho.real (percolationEvent d)) hfk
    simpa only [p] using hmass.symm.trans hfree
  have hmagId := mfc_magPercoId d hd (hbx_hisingBox d)
    beta hbeta hp hp1
  have hmag : magnetization d beta = 0 := by
    rw [hmagId]
    simpa only [FK.fkTheta, pOfBeta, p] using hwired
  exact ⟨hnoperco, hfk, hmag,
    plusState_eq_minusState_of_magnetization_eq_zero beta hbeta.le hmag⟩

end StatMech.FrontierB
