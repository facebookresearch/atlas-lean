/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOddUniqueStabilitySheet
import Code.FrontierD.SixVertexBetheFixedOddChargeContinuation
import Code.FrontierD.SixVertexBetheFixedChargeEventualPerron
import Code.FrontierD.SixVertexBetheFixedEvenChargePerronClosed





open Filter Topology

namespace StatMech.FrontierD

noncomputable section

private theorem oddSectorTopEigenvalue_eq_of_count_eq
    {N n q : Nat} (h : n = q) (hn : n ≤ N) (hq : q ≤ N) (c : Real) :
    sixVertexSectorTopEigenvalue N n hn c =
      sixVertexSectorTopEigenvalue N q hq c := by
  subst q
  rfl

private theorem oddCoordinateBetheWave_cast_ne_zero
    {N n q : Nat} {c : Real} (h : n = q) (p : Fin n -> Real)
    (hp : sixVertexCoordinateBetheWave (N := N) c p ≠ 0) :
    sixVertexCoordinateBetheWave (N := N) c
      (fun i : Fin q => p (Fin.cast h.symm i)) ≠ 0 := by
  subst q
  simpa using hp

private theorem sixVertexZeroPhaseBetheEigenvalueValue_finCast
    {N n q : Nat} {c : Real} (h : n = q) (p : Fin n -> Real)
    (ell : Fin n) :
    sixVertexZeroPhaseBetheEigenvalueValue c N
        (fun i : Fin q => p (Fin.cast h.symm i)) (Fin.cast h ell) =
      sixVertexZeroPhaseBetheEigenvalueValue c N p ell := by
  subst q
  rfl

theorem sixVertexFixedOddChargeBetheEigenvalueValue_reindex
    {c : Real} (hc : 2 < c) (s k : Nat) :
    sixVertexZeroPhaseBetheEigenvalueValue c
        (sixVertexFourWidth (2 * s + 1) k)
        (sixVertexFixedOddChargeBetheRoots hc s k)
        (sixVertexOddCentralIndex (s + k + 1)) =
      sixVertexFixedOddChargeBetheEigenvalueValue hc (2 * s + 1) k := by
  let h := sixVertexFixedOddChargeBetheParticleCount_eq s k
  have hcentral : Fin.cast h
      (sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k) =
        sixVertexOddCentralIndex (s + k + 1) := by
    apply Fin.ext
    simp [sixVertexFixedChargeBetheCentralIndex,
      sixVertexOddCentralIndex]
    omega
  rw [← hcentral]
  unfold sixVertexFixedOddChargeBetheRoots
    sixVertexFixedOddChargeBetheEigenvalueValue
  exact sixVertexZeroPhaseBetheEigenvalueValue_finCast h _ _



theorem sixVertexEventuallyOddChargeBethePerronIdentification_of_densityTail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      sixVertexFixedOddChargeBetheEigenvalueValue hc (2 * s + 1) k =
        sixVertexLambdaAlongFour c (2 * s + 1) k := by
  let a := (2 + c) / 2
  have ha : 2 < a := by dsimp [a]; linarith
  have hac : a < c := by dsimp [a]; linarith
  obtain ⟨rhoLower, hrhoLower, hrho⟩ :=
    exists_uniformLower_sixVertexFourierPhysicalDensity_Ici ha
  obtain ⟨_inner0, outer, houterPos, _hio0, houter, hmargins0⟩ :=
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
      ha (by positivity : 0 < rhoLower / 2) (2 * s + 1)
  have hwidthNat : Tendsto (sixVertexFourWidth (2 * s + 1)) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidthReal : Tendsto
      (fun k : Nat => (sixVertexFourWidth (2 * s + 1) k : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hwidthNat
  have herrorZero : Tendsto
      (fun k : Nat => B / (sixVertexFourWidth (2 * s + 1) k : Real))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hwidthReal
  have herrorSmall : ∀ᶠ k : Nat in atTop,
      B / (sixVertexFourWidth (2 * s + 1) k : Real) < gap / 2 * outer :=
    herrorZero.eventually (Iio_mem_nhds (mul_pos (half_pos hgap) houterPos))
  have hjacobianMargins : ∀ᶠ k : Nat in atTop, ∀ t, a ≤ t ->
      sixVertexSymmetricScatteringBoundaryBound t +
        2 * sixVertexSymmetricJacobianTotalErrorOfLower t
          (sixVertexFourWidth (2 * s + 1) k) (rhoLower / 2) <
            2 * Real.pi := by
    filter_upwards [hwidthNat.eventually hmargins0] with k hk
    intro t ht
    exact (hk t ht).2
  let btarget := c + 1
  have hctarget : c ∈ Set.Icc a btarget := by
    dsimp [btarget]
    exact ⟨hac.le, by linarith⟩
  have htargetGauge : ∀ᶠ k : Nat in atTop,
      sixVertexContinuationWeightedFiniteDensityGauge ha
          (sixVertexFourWidth (2 * s + 1) k)
          (((s + k + 1) + 1) + (s + k + 1))
          (sixVertexFourierPhysicalDensityFamily ha)
          (sixVertexFixedOddChargeBetheContinuationPoint
            ha hctarget s k) < outer :=
    (tendsto_sixVertexFixedOddChargeContinuationGauge_tail
      ha hctarget htail s).eventually (Iio_mem_nhds houterPos)
  have hchargeZero : Tendsto (fun k : Nat =>
      (((2 * s + 1 : Nat) : Real) /
        sixVertexFourWidth (2 * s + 1) k)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hwidthReal
  have hchargeSmall : ∀ᶠ k : Nat in atTop,
      ((2 * s + 1 : Nat) : Real) / sixVertexFourWidth (2 * s + 1) k <
        outer * (2 * Real.pi) :=
    hchargeZero.eventually (Iio_mem_nhds (mul_pos houterPos (by positivity)))
  filter_upwards [herrorSmall, hjacobianMargins, htargetGauge,
      hchargeSmall] with k hkError hkJacobian hkTarget hkCharge
  let m := s + k + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hinner : ∀ t : Real, a ≤ t ->
      sixVertexRootDensityContractionRate t * outer +
          sixVertexFixedChargeDensityStabilityErrorOfLower t
            (sixVertexFourWidth (2 * s + 1) k) (2 * s + 1)
              (rhoLower / 2) ≤ inner := by
    intro t ht
    have hrate := sixVertexRootDensityContractionRate_le_of_ratio_le
      (ha.trans_le ht) hratioB (hcoeff t ht).2.2.1
    have herr := hfixedError (sixVertexFourWidth_pos (2 * s + 1) k) t ht
    have herr' : sixVertexFixedChargeDensityStabilityErrorOfLower t
        (sixVertexFourWidth (2 * s + 1) k) (2 * s + 1) (rhoLower / 2) <
          gap / 2 * outer := herr.trans_lt hkError
    dsimp [inner, gap] at hrate ⊢
    nlinarith
  have hmargin : ∀ t : Real, a ≤ t ->
      sixVertexSymmetricScatteringBoundaryBound t +
        2 * sixVertexSymmetricJacobianTotalErrorOfLower t
          (sixVertexFourWidth (2 * s + 1) k) (rhoLower / 2) <
            2 * Real.pi := hkJacobian
  have hbaseGauge := eventually_sixVertexFixedChargeContinuationGauge_lt
    ha (2 * s + 1) k hkCharge
  have hcand := eventually_sixVertexFixedOddChargeBetheCandidate_eq_top s k
  have hwave := eventually_sixVertexFixedChargeCoordinateBetheWave_ne_zero
    (2 * s + 1) k
  obtain ⟨c0, hc0Gauge, hc0Cand, hc0Wave, hc0large⟩ :=
    (hbaseGauge.and (hcand.and (hwave.and
      (eventually_ge_atTop
        (max (c + 1)
          (2 * (((((m + 1) + m : Nat) : Real))) + 5)))))).exists
  let b := c0 + 1
  have hc0c : c + 1 ≤ c0 :=
    (le_max_left (c + 1) _).trans hc0large
  have hc0a : a < c0 := by linarith
  have hc0Ioo : c0 ∈ Set.Ioo a b := by
    dsimp [b]
    exact ⟨hc0a, by linarith⟩
  have hc0Icc : c0 ∈ Set.Icc a b := ⟨hc0Ioo.1.le, hc0Ioo.2.le⟩
  have hcIoo : c ∈ Set.Ioo a b := by
    dsimp [b]
    exact ⟨hac, by linarith⟩
  have hcIcc : c ∈ Set.Icc a b := ⟨hcIoo.1.le, hcIoo.2.le⟩
  let z0 := sixVertexFixedOddChargeBetheContinuationPoint ha hc0Icc s k
  let z1 := sixVertexFixedOddChargeBetheContinuationPoint ha hcIcc s k
  have hz0g : sixVertexContinuationWeightedFiniteDensityGauge ha
      (sixVertexFourWidth (2 * s + 1) k) ((m + 1) + m)
      (sixVertexFourierPhysicalDensityFamily ha) z0 < outer := by
    change sixVertexWeightedFiniteDensityGauge (ha.trans_le hc0Icc.1)
      (sixVertexFourWidth (2 * s + 1) k) ((m + 1) + m)
      (sixVertexFixedOddChargeBetheRoots (ha.trans_le hc0Icc.1) s k)
      (sixVertexContinuumDensityAt (sixVertexFourierPhysicalDensityFamily ha)
        ⟨c0, hc0Icc⟩) < outer
    rw [sixVertexWeightedFiniteDensityGauge_fixedOddCharge_eq]
    exact hc0Gauge b hc0Icc
  have hz1g : sixVertexContinuationWeightedFiniteDensityGauge ha
      (sixVertexFourWidth (2 * s + 1) k) ((m + 1) + m)
      (sixVertexFourierPhysicalDensityFamily ha) z1 < outer := by
    change sixVertexWeightedFiniteDensityGauge (ha.trans_le hcIcc.1)
      (sixVertexFourWidth (2 * s + 1) k) ((m + 1) + m)
      (sixVertexFixedOddChargeBetheRoots (ha.trans_le hcIcc.1) s k)
      (sixVertexContinuumDensityAt (sixVertexFourierPhysicalDensityFamily ha)
        ⟨c, hcIcc⟩) < outer
    have htarget := hkTarget
    change sixVertexWeightedFiniteDensityGauge (ha.trans_le hctarget.1)
      (sixVertexFourWidth (2 * s + 1) k) ((m + 1) + m)
      (sixVertexFixedOddChargeBetheRoots (ha.trans_le hctarget.1) s k)
      (sixVertexContinuumDensityAt (sixVertexFourierPhysicalDensityFamily ha)
        ⟨c, hctarget⟩) < outer at htarget
    simpa using htarget
  have htailBase : (((m + 1) + m : Nat) : Real) <
      sixVertexAnisotropyMagnitude c0 := by
    have hlarge := (le_max_right (c + 1)
      (2 * (((((m + 1) + m : Nat) : Real))) + 5)).trans hc0large
    unfold sixVertexAnisotropyMagnitude sixVertexDelta
    nlinarith [sq_nonneg
      (c0 - (2 * (((((m + 1) + m : Nat) : Real))) + 5))]
  have hbaseValue : sixVertexZeroPhaseBetheEigenvalueValue c0
      (sixVertexFourWidth (2 * s + 1) k) z0.1.2
        (sixVertexOddCentralIndex m) =
      sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s + 1) k)
        ((m + 1) + m) (by unfold sixVertexFourWidth m; omega) c0 := by
    change sixVertexZeroPhaseBetheEigenvalueValue c0
      (sixVertexFourWidth (2 * s + 1) k)
      (sixVertexFixedOddChargeBetheRoots (ha.trans hc0Ioo.1) s k)
      (sixVertexOddCentralIndex m) = _
    rw [sixVertexFixedOddChargeBetheEigenvalueValue_reindex]
    have hh := hc0Cand (ha.trans hc0Ioo.1)
    have hcount : sixVertexFixedChargeBetheParticleCount (2 * s + 1) k =
        (m + 1) + m := by
      rw [sixVertexFixedChargeBetheParticleCount_eq]
      dsimp [m]
      omega
    exact hh.trans (oddSectorTopEigenvalue_eq_of_count_eq
      (N := sixVertexFourWidth (2 * s + 1) k) hcount
      (by
        have htwice := sixVertexFixedChargeBetheParticleCount_twice_le
          (2 * s + 1) k
        omega)
      (by unfold sixVertexFourWidth m; omega) c0)
  have hwaveBase : sixVertexCoordinateBetheWave
      (N := sixVertexFourWidth (2 * s + 1) k) c0 z0.1.2 ≠ 0 := by
    have hw := hc0Wave (ha.trans hc0Ioo.1)
    have hcount : sixVertexFixedChargeBetheParticleCount (2 * s + 1) k =
        (m + 1) + m := by
      exact sixVertexFixedOddChargeBetheParticleCount_eq s k
    have hw' := oddCoordinateBetheWave_cast_ne_zero hcount
      (sixVertexFixedChargeBetheRoots (ha.trans hc0Ioo.1) (2 * s + 1) k) hw
    simpa [z0, sixVertexFixedOddChargeBetheContinuationPoint,
      sixVertexFixedOddChargeBetheRoots, m] using hw'
  have htargetValue :=
    sixVertexOddSymmetricCandidate_eq_top_of_uniqueTailFixedChargeDensityGauge
      ha (by dsimp [b]; linarith) hc0Icc hcIcc hc0Ioo hcIoo
      (N := sixVertexFourWidth (2 * s + 1) k) (m := m)
      (charge := 2 * s + 1) hm
      (sixVertexFourWidth_pos (2 * s + 1) k) (by
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
      z0 z1 hz0g hz1g
      (sixVertexFixedOddChargeBetheContinuationPoint_projection
        ha hc0Icc s k)
      (sixVertexFixedOddChargeBetheContinuationPoint_projection
        ha hcIcc s k)
      htailBase hbaseValue hwaveBase
  have hvalue : sixVertexFixedOddChargeBetheEigenvalueValue hc
      (2 * s + 1) k =
      sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s + 1) k)
        ((m + 1) + m) (by unfold sixVertexFourWidth m; omega) c := by
    rw [← sixVertexFixedOddChargeBetheEigenvalueValue_reindex hc s k]
    exact htargetValue
  unfold sixVertexLambdaAlongFour sixVertexLambda
  have hparticle : sixVertexFourWidth (2 * s + 1) k / 2 - (2 * s + 1) =
      (m + 1) + m := by
    dsimp [m]
    unfold sixVertexFourWidth
    omega
  exact hvalue.trans (oddSectorTopEigenvalue_eq_of_count_eq
    (N := sixVertexFourWidth (2 * s + 1) k)
    hparticle.symm (by unfold sixVertexFourWidth m; omega)
    (by have := sixVertexFourWidth_charge_le (2 * s + 1) k; omega) c)



def sixVertexSelectedFixedChargeBetheEigenvalueValue
    {c : Real} (hc : 2 < c) (r k : Nat) : Real :=
  if _hr : Even r then
    sixVertexFixedEvenChargeBetheEigenvalueValue hc (r / 2) k
  else
    sixVertexFixedOddChargeBetheEigenvalueValue hc r k



theorem sixVertexEventuallySelectedFixedChargeBethePerronIdentification_of_densityTail
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c) (r : Nat) :
    ∀ᶠ k : Nat in atTop,
      sixVertexSelectedFixedChargeBetheEigenvalueValue hc r k =
        sixVertexLambdaAlongFour c r k := by
  rcases Nat.even_or_odd r with hr | hr
  · obtain ⟨s, rfl⟩ := hr
    filter_upwards
      [sixVertexEventuallyEvenChargeBethePerronIdentification_of_densityTail
        hc htail s] with k hk
    unfold sixVertexSelectedFixedChargeBetheEigenvalueValue
    rw [dif_pos ⟨s, by omega⟩]
    have hadd : s + s = 2 * s := by omega
    have hhalf : (2 * s) / 2 = s := by omega
    simpa only [hadd, hhalf] using hk
  · obtain ⟨s, rfl⟩ := hr
    filter_upwards
      [sixVertexEventuallyOddChargeBethePerronIdentification_of_densityTail
        hc htail s] with k hk
    unfold sixVertexSelectedFixedChargeBetheEigenvalueValue
    rw [dif_neg (Nat.not_even_iff_odd.mpr ⟨s, rfl⟩)]
    simpa using hk

end

end StatMech.FrontierD
