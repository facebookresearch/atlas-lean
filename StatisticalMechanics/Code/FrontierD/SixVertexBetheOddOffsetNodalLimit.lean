/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOddOffsetBoundaryEstimate
import Code.FrontierD.SixVertexBetheOddRootOffsetBound
import Code.FrontierD.SixVertexBetheEvenOffsetNodalLimit
import Code.FrontierD.SixVertexBetheOffsetNodalAbstract
import Code.FrontierD.SixVertexBetheOffsetRowContraction
import Code.FrontierD.SixVertexBetheOffsetSymmetry
import Code.FrontierD.SixVertexBetheOffsetWeightedResidual









namespace StatMech.FrontierD

open Finset

noncomputable section

def sixVertexOddOffsetUniformBound (c : Real) (s : Nat) : Real :=
  ((1 / 2 : Real) + Real.pi *
      (sixVertexFixedChargeDensityInvWidthConstant c 0 +
        sixVertexFixedChargeDensityInvWidthConstant c (2 * s + 1)) /
      ((sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c)) /
    sixVertexTailFiniteDensityFloor c

def sixVertexOddOffsetResidualError (c : Real) (s N : Nat) : Real :=
  4 * sixVertexThetaTaylorBound c *
    sixVertexOddOffsetUniformBound c s ^ 2 / N

def sixVertexOddOffsetBoundaryError (c : Real) (s N n : Nat) : Real :=
  (2 * s + 1 : Real) *
      (sixVertexThetaRightLipschitzNNReal c : Real) * (s + 2 : Real) /
        ((N : Real) * sixVertexTailFiniteDensityFloor c) +
    (n : Real) * sixVertexThetaTaylorBound c /
      (((N : Real) * sixVertexTailFiniteDensityFloor c) ^ 2)

def sixVertexOddOffsetSourceMoveError (c : Real) (s N : Nat) : Real :=
  (2 * s + 1 : Real) *
    (sixVertexThetaRightLipschitzNNReal c : Real) *
      (sixVertexOddOffsetUniformBound c s / N)

def sixVertexOddOffsetNodalError
    (c : Real) (s N n : Nat) (testError : Real) : Real :=
  sixVertexOddOffsetResidualError c s N +
    sixVertexOddOffsetBoundaryError c s N n +
    sixVertexOddOffsetSourceMoveError c s N +
    (2 * s + 1 : Real) * testError

theorem lipschitzWith_sixVertexContinuousOffsetSource
    {c : Real} (hc : 2 < c) :
    LipschitzWith (sixVertexThetaRightLipschitzNNReal c)
      (sixVertexContinuousOffsetSource c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  unfold sixVertexContinuousOffsetSource
  rw [Real.dist_eq, Real.dist_eq]
  have hleft := (lipschitzWith_sixVertexTheta_right hc (-Real.pi)).dist_le_mul x z
  have hright := (lipschitzWith_sixVertexTheta_right hc Real.pi).dist_le_mul x z
  rw [Real.dist_eq, Real.dist_eq] at hleft hright
  have hleft' :
      |sixVertexTheta c x (-Real.pi) - sixVertexTheta c z (-Real.pi)| <=
        (sixVertexThetaRightLipschitzNNReal c : Real) * |x - z| := by
    calc
      |sixVertexTheta c x (-Real.pi) - sixVertexTheta c z (-Real.pi)| =
          |-(sixVertexTheta c x (-Real.pi) -
            sixVertexTheta c z (-Real.pi))| := (abs_neg _).symm
      _ = |sixVertexTheta c (-Real.pi) x -
          sixVertexTheta c (-Real.pi) z| := by
            congr 1
            rw [neg_sub, sixVertexTheta_antisymm c x (-Real.pi),
              sixVertexTheta_antisymm c z (-Real.pi)]
            ring
      _ <= _ := hleft
  have hright' :
      |sixVertexTheta c x Real.pi - sixVertexTheta c z Real.pi| <=
        (sixVertexThetaRightLipschitzNNReal c : Real) * |x - z| := by
    calc
      |sixVertexTheta c x Real.pi - sixVertexTheta c z Real.pi| =
          |-(sixVertexTheta c x Real.pi -
            sixVertexTheta c z Real.pi)| := (abs_neg _).symm
      _ = |sixVertexTheta c Real.pi x - sixVertexTheta c Real.pi z| := by
            congr 1
            rw [neg_sub, sixVertexTheta_antisymm c x Real.pi,
              sixVertexTheta_antisymm c z Real.pi]
            ring
      _ <= _ := hright
  calc
    |(sixVertexTheta c x (-Real.pi) + sixVertexTheta c x Real.pi) / 2 -
        (sixVertexTheta c z (-Real.pi) + sixVertexTheta c z Real.pi) / 2| <=
        (|sixVertexTheta c x (-Real.pi) - sixVertexTheta c z (-Real.pi)| +
          |sixVertexTheta c x Real.pi - sixVertexTheta c z Real.pi|) / 2 := by
      rw [show (sixVertexTheta c x (-Real.pi) + sixVertexTheta c x Real.pi) / 2 -
          (sixVertexTheta c z (-Real.pi) + sixVertexTheta c z Real.pi) / 2 =
        ((sixVertexTheta c x (-Real.pi) - sixVertexTheta c z (-Real.pi)) +
          (sixVertexTheta c x Real.pi - sixVertexTheta c z Real.pi)) / 2 by ring,
        abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
      exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
    _ <= (((sixVertexThetaRightLipschitzNNReal c : Real) * |x - z|) +
        (sixVertexThetaRightLipschitzNNReal c : Real) * |x - z|) / 2 := by
      gcongr
    _ = (sixVertexThetaRightLipschitzNNReal c : Real) * |x - z| := by ring



theorem abs_oddChargeDensityOffset_sub_continuous_le_tail_of_quadrature
    {c : Real} (hc : 2 < c)
    (htail : 2 < sixVertexAnisotropyMagnitude c)
    (s k : Nat) {tau : Real -> Real} (htauOdd : Function.Odd tau)
    (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
    {testError : Real}
    (hquad : forall i : Fin
        (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k),
      |(∑ l, sixVertexContinuousOffsetKernel c
            (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k i)
            (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k l) *
            tau (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k l) /
            sixVertexFiniteRootDensity c
              (sixVertexFourWidth (2 * s + 1) k)
              (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)
              (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k)
              (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k l)) /
          sixVertexFourWidth (2 * s + 1) k -
        ∫ y in -Real.pi..Real.pi,
          sixVertexContinuousOffsetKernel c
            (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k i) y * tau y| <=
        testError)
    (hmargin : 0 < sixVertexFixedChargeOffsetNetMargin c
      (sixVertexFourWidth (2 * s + 1) k) (2 * s + 1))
    (i : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) :
    |sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)
          (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k)
          (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k i) *
        sixVertexOddChargeBetheOffset hc s k i -
      (2 * s + 1 : Real) *
        tau (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k i)| <=
      sixVertexOddOffsetNodalError c s
          (sixVertexFourWidth (2 * s + 1) k)
          (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) testError /
        sixVertexFixedChargeOffsetNetMargin c
          (sixVertexFourWidth (2 * s + 1) k) (2 * s + 1) := by
  let r := 2 * s + 1
  let N := sixVertexFourWidth r k
  let n := sixVertexFixedChargeBetheParticleCount r k
  let p := sixVertexFixedChargeBetheRoots hc r k
  let rhoF := sixVertexFiniteRootDensity c N n p
  let rho : Fin n -> Real := fun l => rhoF (p l)
  let eps := sixVertexOddChargeBetheOffset hc s k
  let aligned := sixVertexOddChargeAlignedHalfRoots hc s k
  let a : Real := r
  let lower := sixVertexTailFiniteDensityFloor c
  let reciprocalMass := sixVertexRootDensityScale c /
    (4 * (sixVertexAnisotropyMagnitude c + 1) *
      sixVertexFiniteRootDensityUniformBound c)
  let rowError := sixVertexFixedChargeOffsetRowError c N r lower
  let rowBound := 2 * Real.pi + rowError
  let residualError := sixVertexOddOffsetResidualError c s N
  let boundaryError := sixVertexOddOffsetBoundaryError c s N n
  let sourceMoveError := sixVertexOddOffsetSourceMoveError c s N
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
    have hzero := sum_oddChargeWeightedOffsetError_div_weight_density_eq_zero
      hc s k htauOdd a
    change ∑ l, (rho l * eps l - a * tau (p l)) /
      (sixVertexRootDensityWeight c (p l) * rho l) = 0 at hzero
    rw [hzero, mul_zero]
  have hrow (l : Fin n) : (1 / (N : Real)) * ∑ j,
      sixVertexContinuousOffsetKernel c (p l) (p j) / rho j <= rowBound := by
    exact empiricalContinuousOffsetKernel_fixedCharge_le hc htail r k l
  have hreciprocal : reciprocalMass <= (1 / (N : Real)) * ∑ l,
      1 / (sixVertexRootDensityWeight c (p l) * rho l) := by
    exact reciprocalWeightDensityMass_fixedCharge_le hc htail r k
  have hlinear (l : Fin n) :
      2 * Real.pi * (rho l * eps l) + (1 / (N : Real)) * ∑ j,
          sixVertexContinuousOffsetKernel c (p l) (p j) * eps j =
        sixVertexOddChargeOffsetNodalResidual hc s k l +
          sixVertexOddChargeOffsetBoundarySource hc s k l := by
    have hres := sixVertexOddChargeOffsetNodalResidual_eq_weightedConvolution
      hc s k l
    change sixVertexOddChargeOffsetNodalResidual hc s k l =
      2 * Real.pi * (rho l * eps l) -
        sixVertexOddChargeOffsetBoundarySource hc s k l +
        (1 / (N : Real)) * ∑ j,
          sixVertexContinuousOffsetKernel c (p l) (p j) * eps j at hres
    linarith
  have hB : 0 <= sixVertexOddOffsetUniformBound c s := by
    unfold sixVertexOddOffsetUniformBound
    have hE0 := sixVertexFixedChargeDensityInvWidthConstant_nonneg_tail
      hc htail 0
    have hEr := sixVertexFixedChargeDensityInvWidthConstant_nonneg_tail
      hc htail r
    have hwmin : 0 < (sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c := div_pos
      (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc)
    positivity
  have hoffset (l : Fin n) : |eps l| <= sixVertexOddOffsetUniformBound c s := by
    exact abs_sixVertexOddChargeBetheOffset_le_tail hc htail s k l
  have hresidual (l : Fin n) :
      |sixVertexOddChargeOffsetNodalResidual hc s k l| <= residualError := by
    exact abs_sixVertexOddChargeOffsetNodalResidual_le hc s k hB hoffset l
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
      |sixVertexOddChargeOffsetBoundarySource hc s k l -
        a * sixVertexContinuousOffsetSource c (aligned l)| <= boundaryError := by
    have h := abs_sixVertexOddChargeOffsetBoundarySource_sub_continuous_le
      hc s k hlower hhalfDensity l
    have hwidth : sixVertexFourWidth 0 (r + k) = N := by
      dsimp [N, r]
      unfold sixVertexFourWidth
      omega
    rw [hwidth] at h
    simpa [a, r, n, aligned, boundaryError,
      sixVertexOddOffsetBoundaryError, lower] using h
  have hsourceMove (l : Fin n) :
      |a * (sixVertexContinuousOffsetSource c (aligned l) -
        sixVertexContinuousOffsetSource c (p l))| <= sourceMoveError := by
    have haligned : aligned l = p l - eps l / N := by
      dsimp [aligned, eps]
      unfold sixVertexOddChargeBetheOffset sixVertexOddChargeAlignedHalfRoots
      have hN0 : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
      change _ = p l - ((N : Real) * (p l - _)) / N
      field_simp [hN0]
      ring
    have hlip := (lipschitzWith_sixVertexContinuousOffsetSource hc).dist_le_mul
      (aligned l) (p l)
    rw [Real.dist_eq, Real.dist_eq, haligned, sub_sub_cancel_left,
      abs_neg, abs_div, abs_of_pos (by exact_mod_cast hN : (0 : Real) < N)] at hlip
    rw [abs_mul, abs_of_nonneg (by positivity : 0 <= a)]
    have hNreal : 0 < (N : Real) := by exact_mod_cast hN
    have hcore : |sixVertexContinuousOffsetSource c (aligned l) -
        sixVertexContinuousOffsetSource c (p l)| <=
      (sixVertexThetaRightLipschitzNNReal c : Real) *
        (sixVertexOddOffsetUniformBound c s / N) := by
      simpa [haligned] using hlip.trans (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (hoffset l) hNreal.le)
        (NNReal.coe_nonneg _))
    have hscaled := mul_le_mul_of_nonneg_left hcore (by positivity : 0 <= a)
    simpa [sourceMoveError, sixVertexOddOffsetSourceMoveError,
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
    (boundary := sixVertexOddChargeOffsetBoundarySource hc s k)
    (residual := sixVertexOddChargeOffsetNodalResidual hc s k)
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
  simpa [rho, rhoF, eps, p, a, r, N, n,
    sixVertexOddOffsetNodalError, residualError, boundaryError,
    sourceMoveError] using h

end

end StatMech.FrontierD
