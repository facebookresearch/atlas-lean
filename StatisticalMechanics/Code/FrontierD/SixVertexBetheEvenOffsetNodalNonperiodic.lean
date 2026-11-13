/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheEvenOffsetNodalConvergence
import Code.FrontierD.SixVertexBetheOddOffsetNodalLimit
import Code.FrontierD.SixVertexBetheFixedChargeNonperiodicQuadrature





namespace StatMech.FrontierD

open Finset Filter Topology

noncomputable section

def sixVertexEvenOffsetNodalErrorOfTest
    (c : Real) (s N : Nat) (testError : Real) : Real :=
  sixVertexEvenOffsetResidualError c s N +
    sixVertexEvenOffsetBoundaryError c s N +
    sixVertexEvenOffsetSourceMoveError c s N +
    (2 * s : Real) * testError

theorem abs_evenChargeDensityOffset_sub_continuous_le_tail_of_quadrature
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    (s k : Nat) {tau : Real -> Real} (htauOdd : Function.Odd tau)
    (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
    {testError : Real}
    (hquad : forall i : Fin
        (sixVertexFixedChargeBetheParticleCount (2 * s) k),
      |(∑ l, sixVertexContinuousOffsetKernel c
            (sixVertexFixedChargeBetheRoots hc (2 * s) k i)
            (sixVertexFixedChargeBetheRoots hc (2 * s) k l) *
            tau (sixVertexFixedChargeBetheRoots hc (2 * s) k l) /
            sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
              (sixVertexFixedChargeBetheParticleCount (2 * s) k)
              (sixVertexFixedChargeBetheRoots hc (2 * s) k)
              (sixVertexFixedChargeBetheRoots hc (2 * s) k l)) /
          sixVertexFourWidth (2 * s) k -
        ∫ y in -Real.pi..Real.pi,
          sixVertexContinuousOffsetKernel c
            (sixVertexFixedChargeBetheRoots hc (2 * s) k i) y * tau y| <=
        testError)
    (hmargin : 0 < sixVertexFixedChargeOffsetNetMargin c
      (sixVertexFourWidth (2 * s) k) (2 * s))
    (i : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) :
    |sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s) k)
          (sixVertexFixedChargeBetheRoots hc (2 * s) k)
          (sixVertexFixedChargeBetheRoots hc (2 * s) k i) *
        sixVertexEvenChargeBetheOffset hc s k i -
      (2 * s : Real) *
        tau (sixVertexFixedChargeBetheRoots hc (2 * s) k i)| <=
      sixVertexEvenOffsetNodalErrorOfTest c s
          (sixVertexFourWidth (2 * s) k) testError /
        sixVertexFixedChargeOffsetNetMargin c
          (sixVertexFourWidth (2 * s) k) (2 * s) := by
  let r := 2 * s
  let N := sixVertexFourWidth r k
  let n := sixVertexFixedChargeBetheParticleCount r k
  let p := sixVertexFixedChargeBetheRoots hc r k
  let rhoF := sixVertexFiniteRootDensity c N n p
  let rho : Fin n -> Real := fun l => rhoF (p l)
  let eps := sixVertexEvenChargeBetheOffset hc s k
  let aligned := sixVertexEvenChargeAlignedHalfRoots hc s k
  let a : Real := r
  let lower := sixVertexTailFiniteDensityFloor c
  let reciprocalMass := sixVertexRootDensityScale c /
    (4 * (sixVertexAnisotropyMagnitude c + 1) *
      sixVertexFiniteRootDensityUniformBound c)
  let rowError := sixVertexFixedChargeOffsetRowError c N r lower
  let rowBound := 2 * Real.pi + rowError
  let residualError := sixVertexEvenOffsetResidualError c s N
  let boundaryError := sixVertexEvenOffsetBoundaryError c s N
  let sourceMoveError := sixVertexEvenOffsetSourceMoveError c s N
  have hN : 0 < N := sixVertexFourWidth_pos r k
  have hn : 0 < n := sixVertexFixedChargeBetheParticleCount_pos r k
  have hlower : 0 < lower := sixVertexTailFiniteDensityFloor_pos hc htail
  have hdensity : forall y, lower <= rhoF y := by
    intro y
    exact sixVertexTailFiniteDensityFloor_le hc hN
      (sixVertexFixedChargeBetheParticleCount_twice_le r k) p y
  have hrho (l : Fin n) : 0 < rho l := hlower.trans_le (hdensity _)
  have hpIcc (l : Fin n) : p l ∈ Set.Icc (-Real.pi) Real.pi :=
    ⟨((sixVertexFixedChargeBetheRoots_mem_open hc r k).2.2 l).1.le,
      ((sixVertexFixedChargeBetheRoots_mem_open hc r k).2.2 l).2.le⟩
  have hmass : (1 / (N : Real)) * ∑ l,
      (rho l * eps l - a * tau (p l)) /
        (sixVertexRootDensityWeight c (p l) * rho l) = 0 := by
    have hzero := sum_evenChargeWeightedOffsetError_div_weight_density_eq_zero
      hc s k htauOdd a
    change ∑ l, (rho l * eps l - a * tau (p l)) /
      (sixVertexRootDensityWeight c (p l) * rho l) = 0 at hzero
    rw [hzero, mul_zero]
  have hrow (l : Fin n) : (1 / (N : Real)) * ∑ j,
      sixVertexContinuousOffsetKernel c (p l) (p j) / rho j <= rowBound :=
    empiricalContinuousOffsetKernel_fixedCharge_le hc htail r k l
  have hreciprocal : reciprocalMass <= (1 / (N : Real)) * ∑ l,
      1 / (sixVertexRootDensityWeight c (p l) * rho l) :=
    reciprocalWeightDensityMass_fixedCharge_le hc htail r k
  have hlinear (l : Fin n) :
      2 * Real.pi * (rho l * eps l) + (1 / (N : Real)) * ∑ j,
          sixVertexContinuousOffsetKernel c (p l) (p j) * eps j =
        sixVertexEvenChargeOffsetNodalResidual hc s k l +
          sixVertexEvenChargeOffsetBoundarySource hc s k l := by
    have hres := sixVertexEvenChargeOffsetNodalResidual_eq_weightedConvolution
      hc s k l
    change sixVertexEvenChargeOffsetNodalResidual hc s k l =
      2 * Real.pi * (rho l * eps l) -
        sixVertexEvenChargeOffsetBoundarySource hc s k l +
        (1 / (N : Real)) * ∑ j,
          sixVertexContinuousOffsetKernel c (p l) (p j) * eps j at hres
    linarith
  have hB : 0 <= sixVertexEvenOffsetUniformBound c s := by
    unfold sixVertexEvenOffsetUniformBound
    have hE0 := sixVertexFixedChargeDensityInvWidthConstant_nonneg_tail
      hc htail 0
    have hEr := sixVertexFixedChargeDensityInvWidthConstant_nonneg_tail
      hc htail r
    have hwmin : 0 < (sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c := div_pos
      (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc)
    positivity
  have hoffset (l : Fin n) : |eps l| <= sixVertexEvenOffsetUniformBound c s :=
    abs_sixVertexEvenChargeBetheOffset_le_tail hc htail s k l
  have hresidual (l : Fin n) :
      |sixVertexEvenChargeOffsetNodalResidual hc s k l| <= residualError :=
    abs_sixVertexEvenChargeOffsetNodalResidual_le hc s k hB hoffset l
  have hhalfDensity : forall y,
      lower <= sixVertexFiniteRootDensity c
        (sixVertexFourWidth 0 (r + k))
        ((r + k + 1) + (r + k + 1))
        (sixVertexHalfFilledBetheRoots hc (r + k)) y := by
    intro y
    apply sixVertexTailFiniteDensityFloor_le hc
      (sixVertexFourWidth_pos 0 (r + k))
    · unfold sixVertexFourWidth
      omega
  have hboundary (l : Fin n) :
      |sixVertexEvenChargeOffsetBoundarySource hc s k l -
        a * sixVertexContinuousOffsetSource c (aligned l)| <= boundaryError := by
    have h := abs_sixVertexEvenChargeOffsetBoundarySource_sub_continuous_le
      hc s k hlower hhalfDensity l
    have hwidth : sixVertexFourWidth 0 (r + k) = N := by
      dsimp [N, r]
      unfold sixVertexFourWidth
      omega
    rw [hwidth] at h
    simpa [a, r, aligned, boundaryError,
      sixVertexEvenOffsetBoundaryError, lower] using h
  have hsourceMove (l : Fin n) :
      |a * (sixVertexContinuousOffsetSource c (aligned l) -
        sixVertexContinuousOffsetSource c (p l))| <= sourceMoveError := by
    have haligned : aligned l = p l - eps l / N := by
      dsimp [aligned, eps]
      unfold sixVertexEvenChargeBetheOffset
      have hN0 : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
      change _ = p l - ((N : Real) * (p l - _)) / N
      field_simp [hN0]
      ring
      rfl
    have hlip := (lipschitzWith_sixVertexContinuousOffsetSource hc).dist_le_mul
      (aligned l) (p l)
    rw [Real.dist_eq, Real.dist_eq, haligned, sub_sub_cancel_left,
      abs_neg, abs_div, abs_of_pos (by exact_mod_cast hN : (0 : Real) < N)] at hlip
    rw [abs_mul, abs_of_nonneg (by positivity : 0 <= a)]
    have hNreal : 0 < (N : Real) := by exact_mod_cast hN
    have hcore : |sixVertexContinuousOffsetSource c (aligned l) -
        sixVertexContinuousOffsetSource c (p l)| <=
      (sixVertexThetaRightLipschitzNNReal c : Real) *
        (sixVertexEvenOffsetUniformBound c s / N) := by
      simpa [haligned] using hlip.trans (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (hoffset l) hNreal.le)
        (NNReal.coe_nonneg _))
    have hscaled := mul_le_mul_of_nonneg_left hcore (by positivity : 0 <= a)
    simpa [sourceMoveError, sixVertexEvenOffsetSourceMoveError,
      a, r, mul_assoc] using hscaled
  have hmargin' : 0 < 2 * Real.pi -
      (rowBound - sixVertexRootDensityKernelFloor c * reciprocalMass) := by
    have heq : 2 * Real.pi -
        (rowBound - sixVertexRootDensityKernelFloor c * reciprocalMass) =
          sixVertexFixedChargeOffsetNetMargin c N r := by
      dsimp [rowBound, rowError, reciprocalMass,
        sixVertexFixedChargeOffsetNetMargin]
      ring
    rw [heq]
    exact hmargin
  have h := abs_densityOffset_sub_continuous_le_of_data hc hN hn
    (p := p) (rho := rho) (eps := eps) (a := a) (tau := tau)
    (aligned := aligned)
    (boundary := sixVertexEvenChargeOffsetBoundarySource hc s k)
    (residual := sixVertexEvenChargeOffsetNodalResidual hc s k)
    (rowBound := rowBound) (reciprocalMass := reciprocalMass)
    (residualError := residualError) (boundaryError := boundaryError)
    (sourceMoveError := sourceMoveError) (testError := testError)
    (by positivity) hrho hpIcc hmass hrow hreciprocal hlinear hresidual
    hboundary hsourceMove hquad htauEq hmargin' i
  have hmarginEq : 2 * Real.pi -
      (rowBound - sixVertexRootDensityKernelFloor c * reciprocalMass) =
        sixVertexFixedChargeOffsetNetMargin c N r := by
    dsimp [rowBound, rowError, reciprocalMass,
      sixVertexFixedChargeOffsetNetMargin]
    ring
  rw [hmarginEq] at h
  simpa [rho, rhoF, eps, p, a, r, N,
    sixVertexEvenOffsetNodalErrorOfTest, residualError, boundaryError,
    sourceMoveError] using h

theorem tendsto_sixVertexEvenOffsetNodalError_nonperiodic
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    (s : Nat) (G : Real) (D : NNReal) :
    Tendsto (fun k => sixVertexEvenOffsetNodalErrorOfTest c s
      (sixVertexFourWidth (2 * s) k)
      (sixVertexFixedChargeNonperiodicOffsetTestError c
        (sixVertexFourWidth (2 * s) k) (2 * s)
        (sixVertexTailFiniteDensityFloor c) G D)) atTop (nhds 0) := by
  have hlower := sixVertexTailFiniteDensityFloor_pos hc htail
  have htest0 := tendsto_sixVertexFixedChargeOffsetTestError c
    (2 * s) hlower 0 0
  have htest0Scaled := htest0.const_mul (2 * s : Real)
  have hbase0 := tendsto_sixVertexEvenOffsetNodalError hc htail s 0 0
  have hbase := hbase0.sub htest0Scaled
  have htest := tendsto_sixVertexFixedChargeNonperiodicOffsetTestError c
    (2 * s) hlower G D
  have htestScaled := htest.const_mul (2 * s : Real)
  convert hbase.add htestScaled using 1
  · funext k
    simp only [sixVertexEvenOffsetNodalErrorOfTest,
      sixVertexEvenOffsetNodalError]
    ring
  · ring

theorem eventually_uniform_evenChargeDensityOffset_nonperiodic
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    (s : Nat) {tau : Real -> Real} {D : NNReal} {G : Real}
    (htauLip : LipschitzWith D tau)
    (htauBound : forall y, |tau y| <= G)
    (htauOdd : Function.Odd tau)
    (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∀ᶠ k : Nat in atTop,
      ∀ i : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k),
        |sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
              (sixVertexFixedChargeBetheParticleCount (2 * s) k)
              (sixVertexFixedChargeBetheRoots hc (2 * s) k)
              (sixVertexFixedChargeBetheRoots hc (2 * s) k i) *
            sixVertexEvenChargeBetheOffset hc s k i -
          (2 * s : Real) * tau
            (sixVertexFixedChargeBetheRoots hc (2 * s) k i)| < epsilon := by
  have herror := tendsto_sixVertexEvenOffsetNodalError_nonperiodic
    hc htail s G D
  have hmargin := tendsto_sixVertexFixedChargeOffsetNetMargin hc htail (2 * s)
  have hquot' := herror.div hmargin
    (sixVertexFixedChargeOffsetContractionMargin_pos hc).ne'
  have hquot : Tendsto (fun k =>
      sixVertexEvenOffsetNodalErrorOfTest c s
          (sixVertexFourWidth (2 * s) k)
          (sixVertexFixedChargeNonperiodicOffsetTestError c
            (sixVertexFourWidth (2 * s) k) (2 * s)
            (sixVertexTailFiniteDensityFloor c) G D) /
        sixVertexFixedChargeOffsetNetMargin c
          (sixVertexFourWidth (2 * s) k) (2 * s)) atTop (nhds 0) := by
    simpa using hquot'
  have hsmall := hquot.eventually (Iio_mem_nhds hepsilon)
  filter_upwards
    [eventually_sixVertexFixedChargeOffsetNetMargin_pos hc htail (2 * s),
      hsmall] with k hkmargin hksmall
  intro i
  have hN := sixVertexFourWidth_pos (2 * s) k
  have hn := sixVertexFixedChargeBetheParticleCount_pos (2 * s) k
  have hcharge : sixVertexFourWidth (2 * s) k =
      2 * sixVertexFixedChargeBetheParticleCount (2 * s) k + 2 * (2 * s) := by
    rw [sixVertexFixedChargeBetheParticleCount_eq]
    unfold sixVertexFourWidth
    omega
  have hlower := sixVertexTailFiniteDensityFloor_pos hc htail
  have hdensity : forall y,
      sixVertexTailFiniteDensityFloor c <=
        sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s) k)
          (sixVertexFixedChargeBetheRoots hc (2 * s) k) y := by
    intro y
    exact sixVertexTailFiniteDensityFloor_le hc hN
      (sixVertexFixedChargeBetheParticleCount_twice_le (2 * s) k) _ y
  have hquad (l : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) :=
    abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_pos_of_lipschitz_nonperiodic
      hc hN hn hcharge (sixVertexFixedChargeBetheRoots_mem_open hc (2 * s) k)
      (sixVertexFixedChargeBetheRoots_is_solution hc (2 * s) k)
      hlower hdensity (sixVertexFixedChargeBetheRoots hc (2 * s) k l)
      htauLip htauBound
  exact (abs_evenChargeDensityOffset_sub_continuous_le_tail_of_quadrature
    hc htail s k htauOdd htauEq hquad hkmargin i).trans_lt hksmall

end

end StatMech.FrontierD
