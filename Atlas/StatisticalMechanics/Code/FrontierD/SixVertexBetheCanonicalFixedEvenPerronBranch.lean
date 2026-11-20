/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheFixedChargeContinuationPoint








open Filter Topology

namespace StatMech.FrontierD

noncomputable section



theorem exists_uniform_sixVertexFixedChargeDensityGaugeNumericalMargins_Ici
    {a rhoLower : Real} (ha : 2 < a) (hrhoLower : 0 < rhoLower) (r : Nat) :
    ∃ inner outer : Real,
      0 < outer ∧ inner < outer ∧
      (∀ c, a ≤ c → outer ≤ rhoLower *
        ((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c) / 2) ∧
      ∀ᶠ N : Nat in atTop, ∀ c, a ≤ c →
        sixVertexRootDensityContractionRate c * outer +
            sixVertexFixedChargeDensityStabilityErrorOfLower
              c N r (rhoLower / 2) ≤ inner ∧
          sixVertexSymmetricScatteringBoundaryBound c +
              2 * sixVertexSymmetricJacobianTotalErrorOfLower
                c N (rhoLower / 2) < 2 * Real.pi := by
  obtain ⟨inner₀, outer, houterPos, hinner₀Outer, houter, hmargins⟩ :=
    exists_uniform_sixVertexDensityGaugeNumericalMargins_Ici ha hrhoLower
  let inner := (inner₀ + outer) / 2
  have hinner₀Inner : inner₀ < inner := by
    dsimp [inner]
    linarith
  have hinnerOuter : inner < outer := by
    dsimp [inner]
    linarith
  obtain ⟨B, hB, hBbound⟩ :=
    exists_uniformBound_sixVertexFixedChargeDensityStabilityError_Ici
      ha (by positivity : 0 < rhoLower / 2) r
  have hrate (c : Real) (hc : a ≤ c) :
      sixVertexRootDensityContractionRate c * outer ≤ inner₀ := by
    obtain ⟨N, hNmargin, hNpos⟩ :=
      (hmargins.and (eventually_gt_atTop 0)).exists
    have herror : 0 ≤
        sixVertexFiniteDensityContinuumErrorOfLower
          c N (rhoLower / 2) := by
      unfold sixVertexFiniteDensityContinuumErrorOfLower
      have hc2 : 2 < c := ha.trans_le hc
      have hNreal : (0 : Real) < N := by exact_mod_cast hNpos
      have hL : 0 ≤ sixVertexRootDensityKernelLipschitzBound c :=
        (sixVertexRootDensityKernelLipschitzBound_pos hc2).le
      have hU : 0 ≤ sixVertexFiniteRootDensityUniformBound c := by
        unfold sixVertexFiniteRootDensityUniformBound
        have hd := one_lt_sixVertexAnisotropyMagnitude hc2
        have hratio : 0 ≤ sixVertexAnisotropyMagnitude c /
            (sixVertexAnisotropyMagnitude c - 1) := by positivity
        exact div_nonneg (by linarith) (by positivity)
      positivity
    exact le_trans (by linarith) (hNmargin c hc).1
  have hBzero : Tendsto (fun N : Nat => B / (N : Real)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat B
  have hBsmall : ∀ᶠ N : Nat in atTop,
      B / (N : Real) < inner - inner₀ :=
    hBzero.eventually (Iio_mem_nhds (sub_pos.mpr hinner₀Inner))
  refine ⟨inner, outer, houterPos, hinnerOuter, houter, ?_⟩
  filter_upwards [hmargins, hBsmall, eventually_gt_atTop 0] with
      N hNmargin hBN hNpos
  intro c hc
  have hfixed := hBbound hNpos c hc
  constructor
  · have := hrate c hc
    linarith
  · exact (hNmargin c hc).2

private theorem sixVertexFixedEvenChargeRoots_mem_open_canonical
    {c : Real} (hc : 2 < c) (s k : Nat) :
    SixVertexOpenRootSimplex (sixVertexFixedEvenChargeBetheRoots hc s k) := by
  let e : Fin ((s + k + 1) + (s + k + 1)) ≃
      Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k) :=
    (Fin.castOrderIso
      (sixVertexFixedEvenChargeBetheParticleCount_eq s k).symm).toEquiv
  have h := sixVertexFixedChargeBetheRoots_mem_open hc (2 * s) k
  refine ⟨?_, sixVertexFixedEvenChargeBetheRoots_symmetric hc s k, ?_⟩
  · intro i j hij
    exact h.1 (by simpa [e] using hij)
  · intro i
    exact h.2.2 (e i)

private theorem sixVertexFixedEvenChargeRoots_is_solution_canonical
    {c : Real} (hc : 2 < c) (s k : Nat) :
    SixVertexSatisfiesBetheEquations c (sixVertexFourWidth (2 * s) k)
      ((s + k + 1) + (s + k + 1))
      (sixVertexFixedEvenChargeBetheRoots hc s k) := by
  let e : Fin ((s + k + 1) + (s + k + 1)) ≃
      Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k) :=
    (Fin.castOrderIso
      (sixVertexFixedEvenChargeBetheParticleCount_eq s k).symm).toEquiv
  intro j
  have hj := sixVertexFixedChargeBetheRoots_is_solution hc (2 * s) k (e j)
  have hquantum : sixVertexCentralQuantumNumber (e j) =
      sixVertexCentralQuantumNumber j := by
    rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq]
    simp [e]
    ring
  let f : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k) → Real :=
    fun l => sixVertexTheta c
      (sixVertexFixedChargeBetheRoots hc (2 * s) k (e j))
      (sixVertexFixedChargeBetheRoots hc (2 * s) k l)
  have hsum : (∑ l, f l) = ∑ l, f (e l) := by
    simpa using (Equiv.sum_comp e f).symm
  rw [hquantum] at hj
  rw [show (∑ l, sixVertexTheta c
      (sixVertexFixedChargeBetheRoots hc (2 * s) k (e j))
      (sixVertexFixedChargeBetheRoots hc (2 * s) k l)) =
        ∑ l, f l by rfl, hsum] at hj
  simpa [sixVertexFixedEvenChargeBetheRoots, e, f] using hj


def sixVertexCanonicalFixedEvenChargeContinuationPoint
    {a b c : Real} (ha : 2 < a) (hc : c ∈ Set.Icc a b)
    (s k : Nat) : SixVertexBetheContinuationSpace a b
      (sixVertexFourWidth (2 * s) k) ((s + k + 1) + (s + k + 1)) := by
  let hc2 : 2 < c := ha.trans_le hc.1
  let p := sixVertexFixedEvenChargeBetheRoots hc2 s k
  refine ⟨(c, p), hc, ?_, ?_⟩
  · exact (sixVertexFixedEvenChargeRoots_mem_open_canonical hc2 s k).toClosed
  · exact (sixVertexBetheUpdate_eq_self_iff
      (sixVertexFourWidth_pos (2 * s) k) p).mpr
      (sixVertexFixedEvenChargeRoots_is_solution_canonical hc2 s k)

@[simp] theorem sixVertexCanonicalFixedEvenChargeContinuationPoint_projection
    {a b c : Real} (ha : 2 < a) (hc : c ∈ Set.Icc a b) (s k : Nat) :
    sixVertexBetheContinuationProjection
      (sixVertexCanonicalFixedEvenChargeContinuationPoint ha hc s k) =
        ⟨c, hc⟩ := rfl

private theorem sixVertexFiniteRootDensity_fixedEvenCharge_canonical
    {c : Real} (hc : 2 < c) (s k : Nat) (x : Real) :
    sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
        ((s + k + 1) + (s + k + 1))
        (sixVertexFixedEvenChargeBetheRoots hc s k) x =
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
        (sixVertexFixedChargeBetheParticleCount (2 * s) k)
        (sixVertexFixedChargeBetheRoots hc (2 * s) k) x := by
  let e : Fin ((s + k + 1) + (s + k + 1)) ≃
      Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k) :=
    (Fin.castOrderIso
      (sixVertexFixedEvenChargeBetheParticleCount_eq s k).symm).toEquiv
  let f : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k) → Real :=
    fun j => 4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c
        (sixVertexFixedChargeBetheRoots hc (2 * s) k j) /
      sixVertexThetaDerivativeDenominator c x
        (sixVertexFixedChargeBetheRoots hc (2 * s) k j)
  have hsum : (∑ j, f j) = ∑ j, f (e j) := by
    simpa using (Equiv.sum_comp e f).symm
  unfold sixVertexFiniteRootDensity
  rw [show (∑ j, 4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c
      (sixVertexFixedEvenChargeBetheRoots hc s k j) /
        sixVertexThetaDerivativeDenominator c x
          (sixVertexFixedEvenChargeBetheRoots hc s k j)) = ∑ j, f j by
    simpa [sixVertexFixedEvenChargeBetheRoots, e, f] using hsum.symm]

private theorem sixVertexWeightedFiniteDensityGauge_fixedEvenCharge_canonical
    {c : Real} (hc : 2 < c) (s k : Nat) (rho : C(Real, Real)) :
    sixVertexWeightedFiniteDensityGauge hc (sixVertexFourWidth (2 * s) k)
        ((s + k + 1) + (s + k + 1))
        (sixVertexFixedEvenChargeBetheRoots hc s k) rho =
      sixVertexWeightedFiniteDensityGauge hc (sixVertexFourWidth (2 * s) k)
        (sixVertexFixedChargeBetheParticleCount (2 * s) k)
        (sixVertexFixedChargeBetheRoots hc (2 * s) k) rho := by
  unfold sixVertexWeightedFiniteDensityGauge
  congr 1
  apply ContinuousMap.ext
  intro x
  simp only [sixVertexWeightedFiniteDensityDifference, ContinuousMap.coe_mk]
  rw [sixVertexFiniteRootDensity_fixedEvenCharge_canonical hc s k x]

private theorem sixVertexCoordinateBetheWave_finCast_ne_zero
    {N n m : Nat} (h : n = m) (c : Real) (p : Fin n → Real)
    (hwave : sixVertexCoordinateBetheWave (N := N) c p ≠ 0) :
    sixVertexCoordinateBetheWave (N := N) c
        (fun i : Fin m => p (Fin.cast h.symm i)) ≠ 0 := by
  subst m
  simpa using hwave

private theorem sixVertexSectorTopEigenvalue_eq_of_finCast
    {N n m : Nat} (h : n = m) (hn : n ≤ N) (hm : m ≤ N)
    (c value : Real)
    (hv : value = sixVertexSectorTopEigenvalue N n hn c) :
    value = sixVertexSectorTopEigenvalue N m hm c := by
  subst m
  simpa using hv



def SixVertexFixedEvenChargePerronBranchWitness
    (c : Real) (s k : Nat)
    (p : Fin ((s + k + 1) + (s + k + 1)) → Real) : Prop :=
  SixVertexOpenRootSimplex p ∧
    SixVertexSatisfiesBetheEquations c (sixVertexFourWidth (2 * s) k)
      ((s + k + 1) + (s + k + 1)) p ∧
    sixVertexSymmetricBetheEigenvalueKernel c
        (sixVertexEvenPositiveHalfProjection (s + k + 1) p) =
      sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s) k)
        ((s + k + 1) + (s + k + 1)) (by
          unfold sixVertexFourWidth
          omega) c



theorem eventually_exists_sixVertexFixedEvenChargeBethePerronBranch_with_densityFloor
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∃ lower : Real, 0 < lower ∧ ∀ᶠ k : Nat in atTop,
      ∃ p, SixVertexFixedEvenChargePerronBranchWitness c s k p ∧
        ∀ x, lower ≤ sixVertexFiniteRootDensity c
          (sixVertexFourWidth (2 * s) k)
          ((s + k + 1) + (s + k + 1)) p x := by
  let a := (2 + c) / 2
  have ha : 2 < a := by dsimp [a]; linarith
  have hac : a < c := by dsimp [a]; linarith
  obtain ⟨rhoLower, hrhoLower, hrho⟩ :=
    exists_uniformLower_sixVertexFourierPhysicalDensity_Ici ha
  refine ⟨rhoLower / 2, by positivity, ?_⟩
  obtain ⟨inner, outer, houterPos, hio, houter, hmargins⟩ :=
    exists_uniform_sixVertexFixedChargeDensityGaugeNumericalMargins_Ici
      ha hrhoLower (2 * s)
  have hwidth : Tendsto (sixVertexFourWidth (2 * s)) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro N
    refine ⟨N, ?_⟩
    intro k hk
    unfold sixVertexFourWidth
    omega
  have hmarginsK : ∀ᶠ k : Nat in atTop, ∀ t, a ≤ t →
      sixVertexRootDensityContractionRate t * outer +
          sixVertexFixedChargeDensityStabilityErrorOfLower t
            (sixVertexFourWidth (2 * s) k) (2 * s) (rhoLower / 2) ≤ inner ∧
        sixVertexSymmetricScatteringBoundaryBound t +
            2 * sixVertexSymmetricJacobianTotalErrorOfLower t
              (sixVertexFourWidth (2 * s) k) (rhoLower / 2) < 2 * Real.pi :=
    hwidth.eventually hmargins
  have hchargeRatio : Tendsto (fun k : Nat =>
      ((2 * s : Nat) : Real) / sixVertexFourWidth (2 * s) k)
      atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp hwidth)
  have hchargeSmall : ∀ᶠ k : Nat in atTop,
      ((2 * s : Nat) : Real) / sixVertexFourWidth (2 * s) k <
        outer * (2 * Real.pi) :=
    hchargeRatio.eventually (Iio_mem_nhds (mul_pos houterPos (by positivity)))
  filter_upwards [hmarginsK, hchargeSmall] with k hkMargins hkCharge
  have hbaseGauge := eventually_sixVertexFixedChargeContinuationGauge_lt
    ha (2 * s) k hkCharge
  have hbasePerron :=
    eventually_sixVertexFixedEvenChargeBetheCandidate_eq_top s k
  have hbaseWave :=
    eventually_sixVertexFixedChargeCoordinateBetheWave_ne_zero (2 * s) k
  obtain ⟨c₀, hc₀Gauge, hc₀Perron, hc₀Wave, hc₀large⟩ :=
    (hbaseGauge.and
      (hbasePerron.and (hbaseWave.and (eventually_ge_atTop (c + 1))))).exists
  let b := c₀ + 1
  have hc₀a : a < c₀ := by linarith
  have hc₀Ioo : c₀ ∈ Set.Ioo a b := by
    dsimp [b]
    exact ⟨hc₀a, by linarith⟩
  have hc₀Icc : c₀ ∈ Set.Icc a b := ⟨hc₀Ioo.1.le, hc₀Ioo.2.le⟩
  have hcIoo : c ∈ Set.Ioo a b := by
    dsimp [b]
    exact ⟨hac, by linarith⟩
  have hcIcc : c ∈ Set.Icc a b := ⟨hcIoo.1.le, hcIoo.2.le⟩
  let m := s + k + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hcharge : sixVertexFourWidth (2 * s) k =
      2 * (m + m) + 2 * (2 * s) := by
    dsimp [m]
    unfold sixVertexFourWidth
    omega
  let z₀ := sixVertexCanonicalFixedEvenChargeContinuationPoint
    ha hc₀Icc s k
  have hz₀g : sixVertexContinuationWeightedFiniteDensityGauge ha
      (sixVertexFourWidth (2 * s) k) (m + m)
      (sixVertexFourierPhysicalDensityFamily ha) z₀ < outer := by
    change sixVertexWeightedFiniteDensityGauge (ha.trans_le hc₀Icc.1)
      (sixVertexFourWidth (2 * s) k) (m + m)
      (sixVertexFixedEvenChargeBetheRoots (ha.trans_le hc₀Icc.1) s k)
      (sixVertexContinuumDensityAt (sixVertexFourierPhysicalDensityFamily ha)
        ⟨c₀, hc₀Icc⟩) < outer
    rw [sixVertexWeightedFiniteDensityGauge_fixedEvenCharge_canonical]
    exact hc₀Gauge b hc₀Icc
  obtain ⟨roots, hroots₀, hrootsData, hrootsAnalytic, hrootsGauge⟩ :=
    exists_sixVertexAnalyticEvenSymmetricBetheBranch_of_fixedChargeDensityGauge
      ha (by dsimp [b]; linarith) hc₀Icc hm
      (sixVertexFourWidth_pos (2 * s) k) hcharge
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
      (sixVertexCanonicalFixedEvenChargeContinuationPoint_projection
        ha hc₀Icc s k)
  have hperron := sixVertexAnalyticEvenSymmetricBetheCandidate_eqOn_top
    (N := sixVertexFourWidth (2 * s) k) (m := m) hm
    (by dsimp [m]; unfold sixVertexFourWidth; omega)
    isPreconnected_Ioo isOpen_Ioo
    (fun t ht => by change 2 < t; linarith [ht.1]) roots
    (fun t ht => (hrootsData t ⟨ht.1.le, ht.2.le⟩).1)
    (fun t ht => (hrootsData t ⟨ht.1.le, ht.2.le⟩).2)
    hrootsAnalytic hc₀Ioo
    (by
      rw [hroots₀]
      apply sixVertexCoordinateBetheWave_finCast_ne_zero
        (sixVertexFixedEvenChargeBetheParticleCount_eq s k)
      exact hc₀Wave (ha.trans hc₀Ioo.1))
    (by
      rw [hroots₀]
      have hvalue := sixVertexSectorTopEigenvalue_eq_of_finCast
        (sixVertexFixedEvenChargeBetheParticleCount_eq s k)
        (by
          have h := sixVertexFixedChargeBetheParticleCount_twice_le (2 * s) k
          omega)
        (by unfold sixVertexFourWidth; omega)
        c₀ (sixVertexFixedEvenChargeBetheEigenvalueValue
          (ha.trans hc₀Ioo.1) s k)
        (hc₀Perron (ha.trans hc₀Ioo.1))
      have hpositive (j : Fin m) :
          sixVertexFixedEvenPositiveBetheRoots
              (ha.trans hc₀Ioo.1) s k j ∈ Set.Ioo 0 Real.pi := by
        have hopen := sixVertexFixedEvenChargeRoots_mem_open_canonical
          (ha.trans hc₀Ioo.1) s k
        have hpos := sixVertexEvenSymmetricLift_positive_mem_Ioo
          (q := sixVertexEvenPositiveHalfProjection m
            (sixVertexFixedEvenChargeBetheRoots
              (ha.trans hc₀Ioo.1) s k))
          (by
            rw [sixVertexEvenSymmetricLift_projection m hopen.2.1]
            exact hopen) j
        exact hpos
      change sixVertexSymmetricBetheEigenvalueKernel c₀
          (sixVertexFixedEvenPositiveBetheRoots
            (ha.trans hc₀Ioo.1) s k) = _
      rw [sixVertexSymmetricBetheEigenvalueKernel_eq_value c₀ _ hpositive]
      exact hvalue)
  obtain ⟨z, hzg, hzparam, hzroots⟩ := hrootsGauge c hcIcc
  have hzg' : sixVertexWeightedFiniteDensityGauge
      (ha.trans_le z.2.1.1) (sixVertexFourWidth (2 * s) k) (m + m)
      z.1.2 (sixVertexFourierPhysicalDensityMap
        (ha.trans_le z.2.1.1)) ≤ inner := by
    simpa only [sixVertexContinuationWeightedFiniteDensityGauge,
      sixVertexContinuumDensitySection, sixVertexContinuumDensityAt,
      ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      sixVertexFourierPhysicalDensityFamily_apply,
      sixVertexFourierPhysicalDensityMap] using hzg
  rw [sixVertexWeightedFiniteDensityGauge_fourier_congr_fixedCharge
    (ha.trans_le z.2.1.1) hc hzparam hzroots] at hzg'
  have hdensity : ∀ x, rhoLower / 2 ≤
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
        (m + m) (roots c) x :=
    sixVertexFiniteRootDensity_lower_half_of_weightedGauge hc
      (sixVertexFourierPhysicalDensityMap hc)
      (fun x => hrho c hac.le x) (houter c hac.le)
      (hzg'.trans hio.le)
  refine ⟨roots c,
    ⟨(hrootsData c hcIcc).1, (hrootsData c hcIcc).2, hperron hcIoo⟩, ?_⟩
  simpa [m] using hdensity



theorem eventually_exists_sixVertexFixedEvenChargeBethePerronBranch
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      ∃ p, SixVertexFixedEvenChargePerronBranchWitness c s k p := by
  obtain ⟨_lower, _hlower, h⟩ :=
    eventually_exists_sixVertexFixedEvenChargeBethePerronBranch_with_densityFloor
      hc s
  filter_upwards [h] with k hk
  exact ⟨hk.choose, hk.choose_spec.1⟩



noncomputable def sixVertexCanonicalFixedEvenChargePerronBetheRoots
    {c : Real} (hc : 2 < c) (s k : Nat) :
    Fin ((s + k + 1) + (s + k + 1)) → Real := by
  classical
  exact if h : ∃ p, SixVertexFixedEvenChargePerronBranchWitness c s k p then
      Classical.choose h
    else
      sixVertexFixedEvenChargeBetheRoots hc s k

theorem eventually_sixVertexCanonicalFixedEvenChargePerronBetheRoots_witness
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      SixVertexFixedEvenChargePerronBranchWitness c s k
        (sixVertexCanonicalFixedEvenChargePerronBetheRoots hc s k) := by
  filter_upwards [eventually_exists_sixVertexFixedEvenChargeBethePerronBranch
    hc s] with k hk
  have h : ∃ p, SixVertexFixedEvenChargePerronBranchWitness c s k p := hk
  rw [sixVertexCanonicalFixedEvenChargePerronBetheRoots, dif_pos h]
  exact Classical.choose_spec h


def sixVertexCanonicalFixedEvenChargeBetheEigenvalueValue
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  sixVertexSymmetricBetheEigenvalueValue c
    (sixVertexEvenPositiveHalfProjection (s + k + 1)
      (sixVertexCanonicalFixedEvenChargePerronBetheRoots hc s k))

theorem eventually_sixVertexCanonicalFixedEvenChargeBetheEigenvalueValue_eq_top
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      sixVertexCanonicalFixedEvenChargeBetheEigenvalueValue hc s k =
        sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s) k)
          ((s + k + 1) + (s + k + 1)) (by
            unfold sixVertexFourWidth
            omega) c := by
  filter_upwards
    [eventually_sixVertexCanonicalFixedEvenChargePerronBetheRoots_witness hc s]
      with k hk
  have hlift : sixVertexEvenSymmetricLift (s + k + 1)
      (sixVertexEvenPositiveHalfProjection (s + k + 1)
        (sixVertexCanonicalFixedEvenChargePerronBetheRoots hc s k)) =
      sixVertexCanonicalFixedEvenChargePerronBetheRoots hc s k :=
    sixVertexEvenSymmetricLift_projection (s + k + 1) hk.1.2.1
  have hpositive (j : Fin (s + k + 1)) :
      sixVertexEvenPositiveHalfProjection (s + k + 1)
          (sixVertexCanonicalFixedEvenChargePerronBetheRoots hc s k) j ∈
        Set.Ioo 0 Real.pi := by
    apply sixVertexEvenSymmetricLift_positive_mem_Ioo
    rw [hlift]
    exact hk.1
  unfold sixVertexCanonicalFixedEvenChargeBetheEigenvalueValue
  rw [← sixVertexSymmetricBetheEigenvalueKernel_eq_value c _ hpositive]
  exact hk.2.2

end

end StatMech.FrontierD
