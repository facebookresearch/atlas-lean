/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch
import Code.FrontierD.SixVertexBetheFixedOddChargeContinuation
import Code.FrontierD.SixVertexBetheOddAnalyticCandidateSheet





open Filter Topology

namespace StatMech.FrontierD

noncomputable section

private theorem sixVertexCoordinateBetheWave_oddFinCast_ne_zero
    {N n m : Nat} (h : n = m) (c : Real) (p : Fin n → Real)
    (hwave : sixVertexCoordinateBetheWave (N := N) c p ≠ 0) :
    sixVertexCoordinateBetheWave (N := N) c
        (fun i : Fin m => p (Fin.cast h.symm i)) ≠ 0 := by
  subst m
  simpa using hwave

private theorem sixVertexSectorTopEigenvalue_oddFinCast
    {N n m : Nat} (h : n = m) (hn : n ≤ N) (hm : m ≤ N)
    (c value : Real)
    (hv : value = sixVertexSectorTopEigenvalue N n hn c) :
    value = sixVertexSectorTopEigenvalue N m hm c := by
  subst m
  simpa using hv

private theorem sixVertexZeroPhaseBetheEigenvalueValue_finCast
    {N n m : Nat} (h : n = m) (c : Real) (p : Fin n → Real)
    (ell : Fin n) :
    sixVertexZeroPhaseBetheEigenvalueValue c N
        (fun i : Fin m => p (Fin.cast h.symm i)) (Fin.cast h ell) =
      sixVertexZeroPhaseBetheEigenvalueValue c N p ell := by
  subst m
  simp

private theorem sixVertexFixedOddChargeCentralIndex_cast
    (s k : Nat) :
    Fin.cast (sixVertexFixedOddChargeBetheParticleCount_eq s k)
        (sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k) =
      sixVertexOddCentralIndex (s + k + 1) := by
  apply Fin.ext
  simp [sixVertexFixedChargeBetheCentralIndex,
    sixVertexOddCentralIndex]
  omega

def SixVertexFixedOddChargePerronBranchWitness
    (c : Real) (s k : Nat)
    (p : Fin (((s + k + 1) + 1) + (s + k + 1)) → Real) : Prop :=
  SixVertexOpenRootSimplex p ∧
    SixVertexSatisfiesBetheEquations c
      (sixVertexFourWidth (2 * s + 1) k)
      (((s + k + 1) + 1) + (s + k + 1)) p ∧
    sixVertexZeroPhaseBetheEigenvalueValue c
        (sixVertexFourWidth (2 * s + 1) k) p
        (sixVertexOddCentralIndex (s + k + 1)) =
      sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s + 1) k)
        (((s + k + 1) + 1) + (s + k + 1)) (by
          unfold sixVertexFourWidth
          omega) c

theorem eventually_exists_sixVertexFixedOddChargeBethePerronBranch_with_densityFloor
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∃ lower : Real, 0 < lower ∧ ∀ᶠ k : Nat in atTop,
      ∃ p, SixVertexFixedOddChargePerronBranchWitness c s k p ∧
        ∀ x, lower ≤ sixVertexFiniteRootDensity c
          (sixVertexFourWidth (2 * s + 1) k)
          (((s + k + 1) + 1) + (s + k + 1)) p x := by
  let a := (2 + c) / 2
  have ha : 2 < a := by dsimp [a]; linarith
  have hac : a < c := by dsimp [a]; linarith
  obtain ⟨rhoLower, hrhoLower, hrho⟩ :=
    exists_uniformLower_sixVertexFourierPhysicalDensity_Ici ha
  refine ⟨rhoLower / 2, by positivity, ?_⟩
  obtain ⟨inner, outer, houterPos, hio, houter, hmargins⟩ :=
    exists_uniform_sixVertexFixedChargeDensityGaugeNumericalMargins_Ici
      ha hrhoLower (2 * s + 1)
  have hwidth : Tendsto (sixVertexFourWidth (2 * s + 1)) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro N
    refine ⟨N, ?_⟩
    intro k hk
    unfold sixVertexFourWidth
    omega
  have hmarginsK : ∀ᶠ k : Nat in atTop, ∀ t, a ≤ t →
      sixVertexRootDensityContractionRate t * outer +
          sixVertexFixedChargeDensityStabilityErrorOfLower t
            (sixVertexFourWidth (2 * s + 1) k) (2 * s + 1)
              (rhoLower / 2) ≤ inner ∧
        sixVertexSymmetricScatteringBoundaryBound t +
            2 * sixVertexSymmetricJacobianTotalErrorOfLower t
              (sixVertexFourWidth (2 * s + 1) k) (rhoLower / 2) <
                2 * Real.pi :=
    hwidth.eventually hmargins
  have hchargeRatio : Tendsto (fun k : Nat =>
      (((2 * s + 1 : Nat) : Real) /
        sixVertexFourWidth (2 * s + 1) k)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp hwidth)
  have hchargeSmall : ∀ᶠ k : Nat in atTop,
      (((2 * s + 1 : Nat) : Real) /
          sixVertexFourWidth (2 * s + 1) k) < outer * (2 * Real.pi) :=
    hchargeRatio.eventually
      (Iio_mem_nhds (mul_pos houterPos (by positivity)))
  filter_upwards [hmarginsK, hchargeSmall] with k hkMargins hkCharge
  have hbaseGauge := eventually_sixVertexFixedChargeContinuationGauge_lt
    ha (2 * s + 1) k hkCharge
  have hbasePerron :=
    eventually_sixVertexFixedOddChargeBetheCandidate_eq_top s k
  have hbaseWave :=
    eventually_sixVertexFixedChargeCoordinateBetheWave_ne_zero (2 * s + 1) k
  obtain ⟨c₀, hc₀Gauge, hc₀Perron, hc₀Wave, hc₀large⟩ :=
    (hbaseGauge.and
      (hbasePerron.and (hbaseWave.and
        (eventually_ge_atTop (c + 1))))).exists
  let b := c₀ + 1
  have hc₀Ioo : c₀ ∈ Set.Ioo a b := by
    dsimp [b]
    exact ⟨by linarith, by linarith⟩
  have hc₀Icc : c₀ ∈ Set.Icc a b :=
    ⟨hc₀Ioo.1.le, hc₀Ioo.2.le⟩
  have hcIoo : c ∈ Set.Ioo a b := by
    dsimp [b]
    exact ⟨hac, by linarith⟩
  have hcIcc : c ∈ Set.Icc a b := ⟨hcIoo.1.le, hcIoo.2.le⟩
  let m := s + k + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hcharge : sixVertexFourWidth (2 * s + 1) k =
      2 * ((m + 1) + m) + 2 * (2 * s + 1) := by
    dsimp [m]
    unfold sixVertexFourWidth
    omega
  let z₀ := sixVertexFixedOddChargeBetheContinuationPoint
    ha hc₀Icc s k
  have hz₀g : sixVertexContinuationWeightedFiniteDensityGauge ha
      (sixVertexFourWidth (2 * s + 1) k) ((m + 1) + m)
      (sixVertexFourierPhysicalDensityFamily ha) z₀ < outer := by
    change sixVertexWeightedFiniteDensityGauge (ha.trans_le hc₀Icc.1)
      (sixVertexFourWidth (2 * s + 1) k) ((m + 1) + m)
      (sixVertexFixedOddChargeBetheRoots (ha.trans_le hc₀Icc.1) s k)
      (sixVertexContinuumDensityAt (sixVertexFourierPhysicalDensityFamily ha)
        ⟨c₀, hc₀Icc⟩) < outer
    rw [sixVertexWeightedFiniteDensityGauge_fixedOddCharge_eq]
    exact hc₀Gauge b hc₀Icc
  obtain ⟨roots, hroots₀, hrootsData, hrootsAnalytic, hrootsGauge⟩ :=
    exists_sixVertexAnalyticOddSymmetricBetheBranch_of_fixedChargeDensityGauge
      ha (by dsimp [b]; linarith) hc₀Icc hm
      (sixVertexFourWidth_pos (2 * s + 1) k) hcharge
      (sixVertexFourierPhysicalDensityFamily ha)
      (sixVertexFourierPhysicalDensityFamily_continuumEquation ha)
      (intervalIntegral_sixVertexFourierPhysicalDensityFamily ha)
      hrhoLower (fun t x => by
        simpa only [sixVertexContinuumDensityAt, ContinuousMap.comp_apply,
          sixVertexFourierPhysicalDensityFamily_apply] using
            hrho t.1 t.2.1 x)
      hio (fun t => houter t.1 t.2.1)
      (fun t => (hkMargins t.1 t.2.1).1)
      (fun t => (hkMargins t.1 t.2.1).2)
      z₀ hz₀g
      (sixVertexFixedOddChargeBetheContinuationPoint_projection
        ha hc₀Icc s k)
  have hbaseValue : sixVertexZeroPhaseBetheEigenvalueValue c₀
      (sixVertexFourWidth (2 * s + 1) k) (roots c₀)
      (sixVertexOddCentralIndex m) =
      sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s + 1) k)
        ((m + 1) + m) (by unfold sixVertexFourWidth; dsimp [m]; omega) c₀ := by
    rw [hroots₀]
    change sixVertexZeroPhaseBetheEigenvalueValue c₀
      (sixVertexFourWidth (2 * s + 1) k)
      (sixVertexFixedOddChargeBetheRoots (ha.trans hc₀Ioo.1) s k)
      (sixVertexOddCentralIndex (s + k + 1)) = _
    have hvalueCast := sixVertexZeroPhaseBetheEigenvalueValue_finCast
      (N := sixVertexFourWidth (2 * s + 1) k)
      (sixVertexFixedOddChargeBetheParticleCount_eq s k) c₀
      (sixVertexFixedChargeBetheRoots (ha.trans hc₀Ioo.1)
        (2 * s + 1) k)
      (sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k)
    rw [sixVertexFixedOddChargeCentralIndex_cast] at hvalueCast
    unfold sixVertexFixedOddChargeBetheRoots
    rw [hvalueCast]
    exact sixVertexSectorTopEigenvalue_oddFinCast
      (sixVertexFixedOddChargeBetheParticleCount_eq s k)
      (by
        have := sixVertexFixedChargeBetheParticleCount_twice_le
          (2 * s + 1) k
        omega)
      (by unfold sixVertexFourWidth; omega)
      c₀ (sixVertexFixedOddChargeBetheEigenvalueValue
        (ha.trans hc₀Ioo.1) (2 * s + 1) k)
      (hc₀Perron (ha.trans hc₀Ioo.1))
  have hperron := sixVertexAnalyticOddSymmetricBetheCandidate_eqOn_top
    (N := sixVertexFourWidth (2 * s + 1) k) (m := m) hm
    (by unfold sixVertexFourWidth; dsimp [m]; omega)
    isPreconnected_Ioo isOpen_Ioo
    (fun t ht => by change 2 < t; linarith [ht.1]) roots
    (fun t ht => (hrootsData t ⟨ht.1.le, ht.2.le⟩).1)
    (fun t ht => (hrootsData t ⟨ht.1.le, ht.2.le⟩).2)
    hrootsAnalytic hc₀Ioo
    (by
      rw [hroots₀]
      apply sixVertexCoordinateBetheWave_oddFinCast_ne_zero
        (sixVertexFixedOddChargeBetheParticleCount_eq s k)
      exact hc₀Wave (ha.trans hc₀Ioo.1))
    hbaseValue
  obtain ⟨z, hzg, hzparam, hzroots⟩ := hrootsGauge c hcIcc
  have hzg' : sixVertexWeightedFiniteDensityGauge
      (ha.trans_le z.2.1.1) (sixVertexFourWidth (2 * s + 1) k)
      ((m + 1) + m) z.1.2
      (sixVertexFourierPhysicalDensityMap (ha.trans_le z.2.1.1)) ≤ inner := by
    simpa only [sixVertexContinuationWeightedFiniteDensityGauge,
      sixVertexContinuumDensitySection, sixVertexContinuumDensityAt,
      ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      sixVertexFourierPhysicalDensityFamily_apply,
      sixVertexFourierPhysicalDensityMap] using hzg
  rw [sixVertexWeightedFiniteDensityGauge_fourier_congr_fixedCharge
    (ha.trans_le z.2.1.1) hc hzparam hzroots] at hzg'
  have hdensity : ∀ x, rhoLower / 2 ≤
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
        ((m + 1) + m) (roots c) x :=
    sixVertexFiniteRootDensity_lower_half_of_weightedGauge hc
      (sixVertexFourierPhysicalDensityMap hc)
      (fun x => hrho c hac.le x) (houter c hac.le)
      (hzg'.trans hio.le)
  refine ⟨roots c,
    ⟨(hrootsData c hcIcc).1, (hrootsData c hcIcc).2, hperron hcIoo⟩, ?_⟩
  simpa [m] using hdensity

theorem eventually_exists_sixVertexFixedOddChargeBethePerronBranch
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      ∃ p, SixVertexFixedOddChargePerronBranchWitness c s k p := by
  obtain ⟨_lower, _hlower, h⟩ :=
    eventually_exists_sixVertexFixedOddChargeBethePerronBranch_with_densityFloor
      hc s
  filter_upwards [h] with k hk
  exact ⟨hk.choose, hk.choose_spec.1⟩

noncomputable def sixVertexCanonicalFixedOddChargePerronBetheRoots
    {c : Real} (hc : 2 < c) (s k : Nat) :
    Fin (((s + k + 1) + 1) + (s + k + 1)) → Real := by
  classical
  exact if h : ∃ p, SixVertexFixedOddChargePerronBranchWitness c s k p then
      Classical.choose h
    else
      sixVertexFixedOddChargeBetheRoots hc s k

theorem eventually_sixVertexCanonicalFixedOddChargePerronBetheRoots_witness
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      SixVertexFixedOddChargePerronBranchWitness c s k
        (sixVertexCanonicalFixedOddChargePerronBetheRoots hc s k) := by
  filter_upwards
    [eventually_exists_sixVertexFixedOddChargeBethePerronBranch hc s]
      with k hk
  have h : ∃ p, SixVertexFixedOddChargePerronBranchWitness c s k p := hk
  rw [sixVertexCanonicalFixedOddChargePerronBetheRoots, dif_pos h]
  exact Classical.choose_spec h

def sixVertexCanonicalFixedOddChargeBetheEigenvalueValue
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  sixVertexZeroPhaseBetheEigenvalueValue c
    (sixVertexFourWidth (2 * s + 1) k)
    (sixVertexCanonicalFixedOddChargePerronBetheRoots hc s k)
    (sixVertexOddCentralIndex (s + k + 1))

theorem eventually_sixVertexCanonicalFixedOddChargeBetheEigenvalueValue_eq_top
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      sixVertexCanonicalFixedOddChargeBetheEigenvalueValue hc s k =
        sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s + 1) k)
          (((s + k + 1) + 1) + (s + k + 1)) (by
            unfold sixVertexFourWidth
            omega) c := by
  filter_upwards
    [eventually_sixVertexCanonicalFixedOddChargePerronBetheRoots_witness hc s]
      with k hk
  exact hk.2.2

end

end StatMech.FrontierD
