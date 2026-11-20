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

private theorem sixVertexSectorTopEigenvalue_eq_of_count_eq
    {N n q : Nat} (h : n = q) (hn : n ≤ N) (hq : q ≤ N) (c : Real) :
    sixVertexSectorTopEigenvalue N n hn c =
      sixVertexSectorTopEigenvalue N q hq c := by
  subst q
  rfl

private theorem sixVertexCoordinateBetheWave_cast_ne_zero
    {N n q : Nat} {c : Real} (h : n = q) (p : Fin n → Real)
    (hp : sixVertexCoordinateBetheWave (N := N) c p ≠ 0) :
    sixVertexCoordinateBetheWave (N := N) c
      (fun i : Fin q => p (Fin.cast h.symm i)) ≠ 0 := by
  subst q
  simpa using hp

private theorem sixVertexFixedEvenChargeBetheRoots_mem_open
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

private theorem sixVertexFixedEvenChargeBetheRoots_is_solution
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

private theorem sixVertexFixedEvenPositiveBetheRoots_mem_Ioo
    {c : Real} (hc : 2 < c) (s k : Nat) (j : Fin (s + k + 1)) :
    sixVertexFixedEvenPositiveBetheRoots hc s k j ∈ Set.Ioo 0 Real.pi := by
  let m := s + k + 1
  let p := sixVertexFixedEvenChargeBetheRoots hc s k
  let i : Fin (m + m) := Fin.natAdd m j
  let ir : Fin (m + m) := Fin.castAdd m j.rev
  have hopen := sixVertexFixedEvenChargeBetheRoots_mem_open hc s k
  have hir : ir < i := by
    rw [Fin.lt_def]
    simp [ir, i, Fin.castAdd, m]
    omega
  have hneg : p ir = -p i := by
    have hs := (sixVertexFixedEvenChargeBetheRoots_symmetric hc s k) i
    have hrev : i.rev = ir := by
      apply Fin.ext
      simp [i, ir, Fin.rev, Fin.castAdd, m]
      omega
    simpa [hrev] using hs
  have hpos : 0 < p i := by
    have hlt := hopen.1 hir
    change p ir < p i at hlt
    rw [hneg] at hlt
    linarith
  exact ⟨hpos, hopen.2.2 i |>.2⟩



def sixVertexFixedEvenChargeBetheContinuationPoint
    {a b c : Real} (ha : 2 < a) (hc : c ∈ Set.Icc a b)
    (s k : Nat) : SixVertexBetheContinuationSpace a b
      (sixVertexFourWidth (2 * s) k) ((s + k + 1) + (s + k + 1)) := by
  let hc2 : 2 < c := ha.trans_le hc.1
  let p := sixVertexFixedEvenChargeBetheRoots hc2 s k
  refine ⟨(c, p), hc, ?_, ?_⟩
  · exact (sixVertexFixedEvenChargeBetheRoots_mem_open hc2 s k).toClosed
  · exact (sixVertexBetheUpdate_eq_self_iff
      (sixVertexFourWidth_pos (2 * s) k) p).mpr
      (sixVertexFixedEvenChargeBetheRoots_is_solution hc2 s k)

@[simp] theorem sixVertexFixedEvenChargeBetheContinuationPoint_parameter
    {a b c : Real} (ha : 2 < a) (hc : c ∈ Set.Icc a b) (s k : Nat) :
    (sixVertexFixedEvenChargeBetheContinuationPoint ha hc s k).1.1 = c := rfl

theorem sixVertexFixedEvenChargeBetheContinuationPoint_roots
    {a b c : Real} (ha : 2 < a) (hc : c ∈ Set.Icc a b) (s k : Nat) :
    (sixVertexFixedEvenChargeBetheContinuationPoint ha hc s k).1.2 =
      sixVertexFixedEvenChargeBetheRoots (ha.trans_le hc.1) s k := rfl

@[simp] theorem sixVertexFixedEvenChargeBetheContinuationPoint_projection
    {a b c : Real} (ha : 2 < a) (hc : c ∈ Set.Icc a b) (s k : Nat) :
    sixVertexBetheContinuationProjection
      (sixVertexFixedEvenChargeBetheContinuationPoint ha hc s k) = ⟨c, hc⟩ := rfl

private theorem sixVertexFiniteRootDensity_fixedEvenCharge_eq
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
  have heqsum : (∑ j, 4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c
      (sixVertexFixedEvenChargeBetheRoots hc s k j) /
        sixVertexThetaDerivativeDenominator c x
          (sixVertexFixedEvenChargeBetheRoots hc s k j)) =
      ∑ j, 4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c
        (sixVertexFixedChargeBetheRoots hc (2 * s) k j) /
          sixVertexThetaDerivativeDenominator c x
            (sixVertexFixedChargeBetheRoots hc (2 * s) k j) := by
    simpa [sixVertexFixedEvenChargeBetheRoots, e, f] using hsum.symm
  unfold sixVertexFiniteRootDensity
  rw [heqsum]

private theorem sixVertexWeightedFiniteDensityGauge_fixedEvenCharge_eq
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
  rw [sixVertexFiniteRootDensity_fixedEvenCharge_eq hc s k x]

theorem tendsto_sixVertexFixedEvenChargeContinuationGauge_tail
    {a b c : Real} (ha : 2 < a) (hc : c ∈ Set.Icc a b)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (s : Nat) :
    Tendsto (fun k : Nat =>
      sixVertexContinuationWeightedFiniteDensityGauge ha
        (sixVertexFourWidth (2 * s) k) ((s + k + 1) + (s + k + 1))
        (sixVertexFourierPhysicalDensityFamily ha)
        (sixVertexFixedEvenChargeBetheContinuationPoint ha hc s k))
      atTop (nhds 0) := by
  have h := tendsto_sixVertexFixedChargeWeightedFiniteDensityGauge_tail
    (ha.trans_le hc.1) htail (2 * s)
  apply h.congr'
  filter_upwards with k
  symm
  change sixVertexWeightedFiniteDensityGauge (ha.trans_le hc.1)
      (sixVertexFourWidth (2 * s) k) ((s + k + 1) + (s + k + 1))
      (sixVertexFixedEvenChargeBetheRoots (ha.trans_le hc.1) s k)
      (sixVertexContinuumDensityAt (sixVertexFourierPhysicalDensityFamily ha)
        ⟨c, hc⟩) = _
  rw [sixVertexWeightedFiniteDensityGauge_fixedEvenCharge_eq]
  congr 2



theorem sixVertexEventuallyEvenChargeBethePerronIdentification_of_densityTail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      sixVertexFixedEvenChargeBetheEigenvalueValue hc s k =
        sixVertexLambdaAlongFour c (2 * s) k := by
  let a := (2 + c) / 2
  have ha : 2 < a := by dsimp [a]; linarith
  have hac : a < c := by dsimp [a]; linarith
  obtain ⟨rhoLower, hrhoLower, hrho⟩ :=
    exists_uniformLower_sixVertexFourierPhysicalDensity_Ici ha
  obtain ⟨_inner₀, outer, houterPos, _hio₀, houter, hmargins₀⟩ :=
    exists_uniform_sixVertexDensityGaugeNumericalMargins_Ici ha hrhoLower
  obtain ⟨_kernelB, _thetaB, ratioB, _boundaryB, _hkernelB, _hthetaB,
      hratioB, _hboundaryB, hcoeff⟩ :=
    exists_uniform_sixVertexCoefficientBounds_Ici ha
  let gap := 1 / (10 * ratioB ^ 3)
  let inner := (1 - gap / 2) * outer
  have hgap : 0 < gap := by dsimp [gap]; positivity
  have hio : inner < outer := by
    dsimp [inner]
    nlinarith [mul_pos hgap houterPos]
  obtain ⟨B, hB, hfixedError⟩ :=
    exists_uniformBound_sixVertexFixedChargeDensityStabilityError_Ici
      ha (by positivity : 0 < rhoLower / 2) (2 * s)
  have hwidthNat : Tendsto (sixVertexFourWidth (2 * s)) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidthReal : Tendsto
      (fun k : Nat => (sixVertexFourWidth (2 * s) k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwidthNat
  have herrorZero : Tendsto
      (fun k : Nat => B / (sixVertexFourWidth (2 * s) k : Real))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hwidthReal
  have herrorSmall : ∀ᶠ k : Nat in atTop,
      B / (sixVertexFourWidth (2 * s) k : Real) < gap / 2 * outer :=
    herrorZero.eventually (Iio_mem_nhds (mul_pos (half_pos hgap) houterPos))
  have hjacobianMargins : ∀ᶠ k : Nat in atTop, ∀ t, a ≤ t →
      sixVertexSymmetricScatteringBoundaryBound t +
        2 * sixVertexSymmetricJacobianTotalErrorOfLower t
          (sixVertexFourWidth (2 * s) k) (rhoLower / 2) < 2 * Real.pi := by
    filter_upwards [hwidthNat.eventually hmargins₀] with k hk
    intro t ht
    exact (hk t ht).2
  let btarget := c + 1
  have hctarget : c ∈ Set.Icc a btarget := by
    dsimp [btarget]
    exact ⟨hac.le, by linarith⟩
  have htargetGauge : ∀ᶠ k : Nat in atTop,
      sixVertexContinuationWeightedFiniteDensityGauge ha
          (sixVertexFourWidth (2 * s) k) ((s + k + 1) + (s + k + 1))
          (sixVertexFourierPhysicalDensityFamily ha)
          (sixVertexFixedEvenChargeBetheContinuationPoint
            ha hctarget s k) < outer :=
    (tendsto_sixVertexFixedEvenChargeContinuationGauge_tail
      ha hctarget htail s).eventually (Iio_mem_nhds houterPos)
  have hchargeZero : Tendsto (fun k : Nat =>
      ((2 * s : Nat) : Real) / sixVertexFourWidth (2 * s) k)
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hwidthReal
  have hchargeSmall : ∀ᶠ k : Nat in atTop,
      ((2 * s : Nat) : Real) / sixVertexFourWidth (2 * s) k <
        outer * (2 * Real.pi) :=
    hchargeZero.eventually (Iio_mem_nhds (mul_pos houterPos (by positivity)))
  filter_upwards [herrorSmall, hjacobianMargins, htargetGauge,
      hchargeSmall] with k hkError hkJacobian hkTarget hkCharge
  let m := s + k + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hinner : ∀ t : Real, a ≤ t →
      sixVertexRootDensityContractionRate t * outer +
          sixVertexFixedChargeDensityStabilityErrorOfLower t
            (sixVertexFourWidth (2 * s) k) (2 * s) (rhoLower / 2) ≤ inner := by
    intro t ht
    have hrate := sixVertexRootDensityContractionRate_le_of_ratio_le
      (ha.trans_le ht) hratioB (hcoeff t ht).2.2.1
    have herr := hfixedError (sixVertexFourWidth_pos (2 * s) k)
      t ht
    have herr' : sixVertexFixedChargeDensityStabilityErrorOfLower t
        (sixVertexFourWidth (2 * s) k) (2 * s) (rhoLower / 2) <
          gap / 2 * outer := herr.trans_lt hkError
    dsimp [inner, gap] at hrate ⊢
    nlinarith
  have hmargin : ∀ t : Real, a ≤ t →
      sixVertexSymmetricScatteringBoundaryBound t +
        2 * sixVertexSymmetricJacobianTotalErrorOfLower t
          (sixVertexFourWidth (2 * s) k) (rhoLower / 2) < 2 * Real.pi :=
    hkJacobian
  have hbaseGauge := eventually_sixVertexFixedChargeContinuationGauge_lt
    ha (2 * s) k hkCharge
  have hcand := eventually_sixVertexFixedEvenChargeBetheCandidate_eq_top s k
  have hwave := eventually_sixVertexFixedChargeCoordinateBetheWave_ne_zero
    (2 * s) k
  obtain ⟨c₀, hc₀Gauge, hc₀Cand, hc₀Wave, hc₀large⟩ :=
    (hbaseGauge.and (hcand.and (hwave.and
      (eventually_ge_atTop
        (max (c + 1) (2 * (((m + m : Nat) : Real)) + 5)))))).exists
  let b := c₀ + 1
  have hc₀c : c + 1 ≤ c₀ :=
    (le_max_left (c + 1) _).trans hc₀large
  have hc₀a : a < c₀ := by linarith
  have hc₀Ioo : c₀ ∈ Set.Ioo a b := by
    dsimp [b]
    exact ⟨hc₀a, by linarith⟩
  have hc₀Icc : c₀ ∈ Set.Icc a b := ⟨hc₀Ioo.1.le, hc₀Ioo.2.le⟩
  have hcIoo : c ∈ Set.Ioo a b := by
    dsimp [b]
    exact ⟨hac, by linarith⟩
  have hcIcc : c ∈ Set.Icc a b := ⟨hcIoo.1.le, hcIoo.2.le⟩
  let z₀ := sixVertexFixedEvenChargeBetheContinuationPoint ha hc₀Icc s k
  let z₁ := sixVertexFixedEvenChargeBetheContinuationPoint ha hcIcc s k
  have hz₀g : sixVertexContinuationWeightedFiniteDensityGauge ha
      (sixVertexFourWidth (2 * s) k) (m + m)
      (sixVertexFourierPhysicalDensityFamily ha) z₀ < outer := by
    change sixVertexWeightedFiniteDensityGauge (ha.trans_le hc₀Icc.1)
      (sixVertexFourWidth (2 * s) k) (m + m)
      (sixVertexFixedEvenChargeBetheRoots (ha.trans_le hc₀Icc.1) s k)
      (sixVertexContinuumDensityAt (sixVertexFourierPhysicalDensityFamily ha)
        ⟨c₀, hc₀Icc⟩) < outer
    rw [sixVertexWeightedFiniteDensityGauge_fixedEvenCharge_eq]
    exact hc₀Gauge b hc₀Icc
  have hz₁g : sixVertexContinuationWeightedFiniteDensityGauge ha
      (sixVertexFourWidth (2 * s) k) (m + m)
      (sixVertexFourierPhysicalDensityFamily ha) z₁ < outer := by
    change sixVertexWeightedFiniteDensityGauge (ha.trans_le hcIcc.1)
      (sixVertexFourWidth (2 * s) k) (m + m)
      (sixVertexFixedEvenChargeBetheRoots (ha.trans_le hcIcc.1) s k)
      (sixVertexContinuumDensityAt (sixVertexFourierPhysicalDensityFamily ha)
        ⟨c, hcIcc⟩) < outer
    have htarget := hkTarget
    change sixVertexWeightedFiniteDensityGauge (ha.trans_le hctarget.1)
      (sixVertexFourWidth (2 * s) k) (m + m)
      (sixVertexFixedEvenChargeBetheRoots (ha.trans_le hctarget.1) s k)
      (sixVertexContinuumDensityAt (sixVertexFourierPhysicalDensityFamily ha)
        ⟨c, hctarget⟩) < outer at htarget
    simpa using htarget
  have htailBase : (((m + m : Nat) : Real)) <
      sixVertexAnisotropyMagnitude c₀ := by
    have hlarge := (le_max_right (c + 1)
      (2 * (((m + m : Nat) : Real)) + 5)).trans hc₀large
    unfold sixVertexAnisotropyMagnitude sixVertexDelta
    nlinarith [sq_nonneg (c₀ - (2 * (((m + m : Nat) : Real)) + 5))]
  have hbaseKernel : sixVertexSymmetricBetheEigenvalueKernel c₀
      (sixVertexEvenPositiveHalfProjection m z₀.1.2) =
      sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s) k) (m + m)
        (by unfold sixVertexFourWidth m; omega) c₀ := by
    have hq : sixVertexEvenPositiveHalfProjection m z₀.1.2 =
        sixVertexFixedEvenPositiveBetheRoots (ha.trans hc₀Ioo.1) s k := by rfl
    rw [hq, sixVertexSymmetricBetheEigenvalueKernel_eq_value]
    · have hh := hc₀Cand (ha.trans hc₀Ioo.1)
      unfold sixVertexFixedEvenChargeBetheEigenvalueValue at hh
      have hcount : sixVertexFixedChargeBetheParticleCount (2 * s) k =
          m + m := by
        rw [sixVertexFixedChargeBetheParticleCount_eq]
        dsimp [m]
        omega
      exact hh.trans (sixVertexSectorTopEigenvalue_eq_of_count_eq hcount
        (by have := sixVertexFixedChargeBetheParticleCount_twice_le (2 * s) k
            omega)
        (by unfold sixVertexFourWidth m; omega) c₀)
    · exact sixVertexFixedEvenPositiveBetheRoots_mem_Ioo
        (ha.trans hc₀Ioo.1) s k
  have hwaveBase : sixVertexCoordinateBetheWave
      (N := sixVertexFourWidth (2 * s) k) c₀ z₀.1.2 ≠ 0 := by
    have hw := hc₀Wave (ha.trans hc₀Ioo.1)
    have hcount : sixVertexFixedChargeBetheParticleCount (2 * s) k =
        m + m := by
      exact sixVertexFixedEvenChargeBetheParticleCount_eq s k
    have hw' := sixVertexCoordinateBetheWave_cast_ne_zero hcount
      (sixVertexFixedChargeBetheRoots (ha.trans hc₀Ioo.1) (2 * s) k) hw
    simpa [z₀, sixVertexFixedEvenChargeBetheContinuationPoint,
      sixVertexFixedEvenChargeBetheRoots, m] using hw'
  have htargetKernel :=
    sixVertexEvenSymmetricCandidate_eq_top_of_uniqueTailFixedChargeDensityGauge
      ha (by dsimp [b]; linarith) hc₀Icc hcIcc hc₀Ioo hcIoo
      (N := sixVertexFourWidth (2 * s) k) (m := m) (charge := 2 * s)
      hm (sixVertexFourWidth_pos (2 * s) k) (by
        dsimp [m]
        unfold sixVertexFourWidth
        omega)
      (sixVertexFourierPhysicalDensityFamily ha)
      (sixVertexFourierPhysicalDensityFamily_continuumEquation ha)
      (intervalIntegral_sixVertexFourierPhysicalDensityFamily ha)
      hrhoLower (fun t x => by
        simpa only [sixVertexContinuumDensityAt, ContinuousMap.comp_apply,
          sixVertexFourierPhysicalDensityFamily_apply] using
            hrho t.1 t.2.1 x)
      hio (fun t => houter t.1 t.2.1)
      (fun t => hinner t.1 t.2.1) (fun t => hmargin t.1 t.2.1)
      z₀ z₁ hz₀g hz₁g
      (sixVertexFixedEvenChargeBetheContinuationPoint_projection ha hc₀Icc s k)
      (sixVertexFixedEvenChargeBetheContinuationPoint_projection ha hcIcc s k)
      htailBase hbaseKernel hwaveBase
  have hvalue : sixVertexFixedEvenChargeBetheEigenvalueValue hc s k =
      sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s) k) (m + m)
        (by unfold sixVertexFourWidth m; omega) c := by
    have hq : sixVertexEvenPositiveHalfProjection m z₁.1.2 =
        sixVertexFixedEvenPositiveBetheRoots hc s k := by rfl
    unfold sixVertexFixedEvenChargeBetheEigenvalueValue
    rw [← hq, ← sixVertexSymmetricBetheEigenvalueKernel_eq_value]
    · exact htargetKernel
    · intro j
      rw [hq]
      exact sixVertexFixedEvenPositiveBetheRoots_mem_Ioo hc s k j
  unfold sixVertexLambdaAlongFour sixVertexLambda
  have hparticle : sixVertexFourWidth (2 * s) k / 2 - 2 * s = m + m := by
    dsimp [m]
    unfold sixVertexFourWidth
    omega
  exact hvalue.trans (sixVertexSectorTopEigenvalue_eq_of_count_eq
    hparticle.symm (by unfold sixVertexFourWidth m; omega)
    (by have := sixVertexFourWidth_charge_le (2 * s) k; omega) c)

end

end StatMech.FrontierD
