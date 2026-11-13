/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierB.CurrentContinuityEdwardsSokal
import Code.FrontierB.CurrentContinuityPhaseCollapse
import Code.FK.PairMixingGenMixing
import Code.FK.FreePairMixingFromTail
import Code.IsingFK.MagnetizationCorrespondence

open Filter MeasureTheory Set Topology BoundedContinuousFunction

namespace StatMech.FrontierB

open ConfigSpace FK Ising Lattice Percolation
open StatMech.IsingFK

variable {d : Nat}



theorem allClustersEven_pair_iff_reachable
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (omega : ConfigSpace (Sym2 V)) (x y : V) (hxy : x ≠ y) :
    AllClustersEven G omega ({x, y} : Finset V) ↔
      (openSub G omega).Reachable x y := by
  classical
  rw [allClustersEven_iff_mark_reachability]
  constructor
  · intro h
    have hx := h x (by simp)
    by_contra hn
    have hfilter : ({x, y} : Finset V).filter
        (fun z => (openSub G omega).Reachable x z) = {x} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hz⟩
        · simp
        · exact (hn hz).elim
      · intro hz
        subst z
        exact ⟨Or.inl rfl, SimpleGraph.Reachable.refl x⟩
    unfold markReachableCount at hx
    rw [hfilter] at hx
    norm_num at hx
  · intro h z hz
    have hzxy : z = x ∨ z = y := by simpa using hz
    unfold markReachableCount
    have hfilter : ({x, y} : Finset V).filter
        (fun w => (openSub G omega).Reachable z w) = {x, y} := by
      ext w
      simp only [Finset.mem_filter]
      constructor
      · exact fun hw => hw.1
      · intro hw
        have hwxy : w = x ∨ w = y := by simpa using hw
        rcases hzxy with rfl | rfl <;> rcases hwxy with rfl | rfl
        · exact ⟨by simp, SimpleGraph.Reachable.rfl⟩
        · exact ⟨by simp, h⟩
        · exact ⟨by simp, h.symm⟩
        · exact ⟨by simp, SimpleGraph.Reachable.rfl⟩
    rw [hfilter]
    simp [hxy]



theorem currentContinuityFreeTwoPoint_eq_freeInfiniteTwoPoint
    (beta : Real) (hbeta : 0 < beta) (hd : 1 ≤ d)
    (x y : Site d) (hxy : x ≠ y) :
    currentContinuityFreeTwoPoint d beta x y =
      infiniteTwoPointReal
        (freeInfiniteVolume d
          (p := 1 - Real.exp (-2 * beta)) (q := 2)
          (by exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
          (by linarith [Real.exp_pos (-2 * beta)])
          (by norm_num : (0 : Real) < 2) : Measure _)
        x y := by
  unfold currentContinuityFreeTwoPoint
  rw [integral_freeState_spinProd_eq_freeInfinite_allClustersEven
    d beta hbeta hd ({x, y} : Finset (Site d))]
  · unfold infiniteTwoPointReal
    congr 1
    ext omega
    exact allClustersEven_pair_iff_reachable
      (hypercubicLattice d) omega x y hxy
  · simp [hxy]



theorem freeInfiniteVolume_noPercolation_of_currentContinuityFreeLROZero
    (beta : Real) (hbeta : 0 < beta) (hd : 1 ≤ d)
    (hLRO : CurrentContinuityFreeLROZero d beta) :
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
  have hprinciple : CurrentContinuityPercolationPrinciple d (phi : Measure _) :=
    currentContinuityPercolationPrinciple_of_genMixing d hd phi
      (bdp_freeIV_isTranslationInvariant hp hp1)
      (fmu_genMixing_of_pairMixing
        (freeInfiniteVolume_pairMixing_all_parameters hd hp hp1))
      (freeInfinite_q2_canonical_uniqueness_all_parameters hd hp hp1).2.1
  apply le_antisymm
  · by_contra hne
    have hpos : 0 < (phi : Measure _).real (percolationEvent d) :=
      lt_of_not_ge hne
    obtain ⟨epsilon, hepsilon, hpersist⟩ := hprinciple hpos
    obtain ⟨R, hR⟩ := hLRO epsilon hepsilon
    obtain ⟨x, hxout, hxlower⟩ := hpersist R
    have hxo : Percolation.origin d ≠ x := by
      intro hx
      subst x
      exact hxout (origin_mem_box' R)
    have heq := currentContinuityFreeTwoPoint_eq_freeInfiniteTwoPoint
      beta hbeta hd (Percolation.origin d) x hxo
    have hsmall := hR x hxout
    rw [heq] at hsmall
    unfold infiniteTwoPointReal at hsmall hxlower
    rw [abs_of_nonneg measureReal_nonneg] at hsmall
    exact (not_lt_of_ge hxlower) hsmall
  · exact measureReal_nonneg



theorem currentContinuity_magnetization_and_phase_eq_of_freeLROZero
    (beta : Real) (hbeta : 0 < beta) (hd : 1 ≤ d)
    (hLRO : CurrentContinuityFreeLROZero d beta) :
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
  have hfk := (currentContinuity_FK_phase_eq_of_freeLROZero
    beta hbeta hd hLRO).2
  have hfree :=
    freeInfiniteVolume_noPercolation_of_currentContinuityFreeLROZero
      beta hbeta hd hLRO
  have hwired :
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : Real) < 2) : Measure _).real
        (percolationEvent d) = 0 := by
    have hmass := congrArg
      (fun mu : Measure (ConfigSpace (Sym2 (Site d))) =>
        mu.real (percolationEvent d)) hfk
    simpa only [p] using hmass.symm.trans hfree
  have hmagId := mfc_magPercoId d hd (hbx_hisingBox d)
    beta hbeta hp hp1
  have hmag : magnetization d beta = 0 := by
    rw [hmagId]
    simpa only [FK.fkTheta, pOfBeta, p] using hwired
  exact ⟨hmag,
    plusState_eq_minusState_of_magnetization_eq_zero beta hbeta.le hmag⟩



theorem currentContinuity_gibbs_unique_of_freeLROZero
    (beta : Real) (hbeta : 0 < beta) (hd : 1 ≤ d)
    (hLRO : CurrentContinuityFreeLROZero d beta)
    (mu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure mu]
    (hmu : IsDLRState d beta 0 mu) :
    mu = (minusState d beta 0 : Measure (ConfigSpace (Site d))) := by
  exact gsi_gibbs_unique_of_phases_eq beta 0 hbeta.le le_rfl mu hmu
    (currentContinuity_magnetization_and_phase_eq_of_freeLROZero
      beta hbeta hd hLRO).2



theorem currentContinuity_localExpectation_tendsto_of_freeLROZero
    (beta : Real) (hbeta : 0 < beta) (hd : 1 ≤ d)
    (hLRO : CurrentContinuityFreeLROZero d beta)
    (mu : Nat → ProbabilityMeasure (ConfigSpace (Site d)))
    (muLim : ProbabilityMeasure (ConfigSpace (Site d)))
    (hconv : WeakConvergesTo mu muLim)
    (hDLR : IsDLRState d beta 0 (muLim : Measure _))
    (f : ConfigSpace (Site d) →ᵇ Real) :
    Tendsto (fun n => ∫ omega, f omega ∂(mu n : Measure _)) atTop
      (nhds (∫ omega, f omega
        ∂(minusState d beta 0 : Measure (ConfigSpace (Site d))))) := by
  exact currentContinuity_localExpectation_tendsto_of_unique_limit
    beta hbeta.le mu muLim hconv hDLR
      (currentContinuity_magnetization_and_phase_eq_of_freeLROZero
        beta hbeta hd hLRO).2 f

end StatMech.FrontierB
