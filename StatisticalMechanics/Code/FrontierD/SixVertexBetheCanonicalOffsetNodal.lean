/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalOffsetBoundary
import Code.FrontierD.SixVertexBetheCanonicalFixedOffsetBound
import Code.FrontierD.SixVertexBetheOffsetNodalAbstract
import Code.FrontierD.SixVertexBetheOffsetRowContraction
import Code.FrontierD.SixVertexBetheOddOffsetNodalLimit
import Code.FrontierD.SixVertexBetheFixedChargeNonperiodicQuadrature
import Code.FrontierD.SixVertexBetheContinuousOffsetEquation
import Code.FrontierD.SixVertexBetheOffsetProfileRegularity





namespace StatMech.FrontierD

open Finset Filter Topology

noncomputable section

theorem sixVertexCanonicalEvenOffsetNodalResidual_eq_weightedConvolution
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin ((s + k + 1) + (s + k + 1))) :
    sixVertexCanonicalEvenOffsetNodalResidual hc s k j =
      2 * Real.pi *
          (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
            ((s + k + 1) + (s + k + 1))
            (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k)
            (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) *
          sixVertexCanonicalEvenChargeOffset hc s k j) -
        sixVertexCanonicalEvenOffsetBoundarySource hc s k j +
        (1 / (sixVertexFourWidth (2 * s) k : Real)) *
          ∑ l, sixVertexContinuousOffsetKernel c
              (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j)
              (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k l) *
            sixVertexCanonicalEvenChargeOffset hc s k l := by
  let N := sixVertexFourWidth (2 * s) k
  let n := (s + k + 1) + (s + k + 1)
  let q := sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k
  let eps := sixVertexCanonicalEvenChargeOffset hc s k
  have hN : (N : Real) ≠ 0 := by
    exact_mod_cast (sixVertexFourWidth_pos (2 * s) k).ne'
  unfold sixVertexCanonicalEvenOffsetNodalResidual
  change eps j - sixVertexCanonicalEvenOffsetBoundarySource hc s k j +
      (1 / (N : Real)) * ∑ l,
        ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps j +
          (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps l) =
    2 * Real.pi * (sixVertexFiniteRootDensity c N n q (q j) * eps j) -
      sixVertexCanonicalEvenOffsetBoundarySource hc s k j +
      (1 / (N : Real)) * ∑ l,
        sixVertexContinuousOffsetKernel c (q j) (q l) * eps l
  unfold sixVertexContinuousOffsetKernel
  simp_rw [sixVertexRootDensityKernel_div_weight hc]
  unfold sixVertexFiniteRootDensity
  rw [Finset.sum_add_distrib, <- Finset.sum_mul]
  field_simp [hN, Real.pi_ne_zero]
  ring

theorem sixVertexCanonicalOddOffsetNodalResidual_eq_weightedConvolution
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (((s + k + 1) + 1) + (s + k + 1))) :
    sixVertexCanonicalOddOffsetNodalResidual hc s k j =
      2 * Real.pi *
          (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
            (((s + k + 1) + 1) + (s + k + 1))
            (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
            (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) *
          sixVertexCanonicalOddChargeOffset hc s k j) -
        sixVertexCanonicalOddOffsetBoundarySource hc s k j +
        (1 / (sixVertexFourWidth (2 * s + 1) k : Real)) *
          ∑ l, sixVertexContinuousOffsetKernel c
              (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j)
              (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k l) *
            sixVertexCanonicalOddChargeOffset hc s k l := by
  let N := sixVertexFourWidth (2 * s + 1) k
  let n := ((s + k + 1) + 1) + (s + k + 1)
  let q := sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k
  let eps := sixVertexCanonicalOddChargeOffset hc s k
  have hN : (N : Real) ≠ 0 := by
    exact_mod_cast (sixVertexFourWidth_pos (2 * s + 1) k).ne'
  unfold sixVertexCanonicalOddOffsetNodalResidual
  change eps j - sixVertexCanonicalOddOffsetBoundarySource hc s k j +
      (1 / (N : Real)) * ∑ l,
        ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps j +
          (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps l) =
    2 * Real.pi * (sixVertexFiniteRootDensity c N n q (q j) * eps j) -
      sixVertexCanonicalOddOffsetBoundarySource hc s k j +
      (1 / (N : Real)) * ∑ l,
        sixVertexContinuousOffsetKernel c (q j) (q l) * eps l
  unfold sixVertexContinuousOffsetKernel
  simp_rw [sixVertexRootDensityKernel_div_weight hc]
  unfold sixVertexFiniteRootDensity
  rw [Finset.sum_add_distrib, <- Finset.sum_mul]
  field_simp [hN, Real.pi_ne_zero]
  ring

theorem empiricalContinuousOffsetKernel_le_of_lower
    {c : Real} (hc : 2 < c) {N n r : Nat}
    (hN : 0 < N) (hn : 0 < n) (hcharge : N = 2 * n + 2 * r)
    {p : Fin n -> Real} (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N n p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : forall y, lower <= sixVertexFiniteRootDensity c N n p y)
    (i : Fin n) :
    (1 / (N : Real)) * ∑ j,
        sixVertexContinuousOffsetKernel c (p i) (p j) /
          sixVertexFiniteRootDensity c N n p (p j) <=
      2 * Real.pi + sixVertexFixedChargeOffsetRowError c N r lower := by
  have hquad := abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_pos
    hc hN hn hcharge hopen hsol hlower hdensity (p i)
  have hint : (∫ y in -Real.pi..Real.pi,
      sixVertexContinuousOffsetKernel c (p i) y) = 2 * Real.pi := by
    unfold sixVertexContinuousOffsetKernel
    exact intervalIntegral_sixVertexRootDensityKernel_div_weight hc (p i)
  rw [hint] at hquad
  have hle := (le_abs_self
    ((∑ j, sixVertexContinuousOffsetKernel c (p i) (p j) /
      sixVertexFiniteRootDensity c N n p (p j)) / N - 2 * Real.pi)).trans hquad
  rw [show (1 / (N : Real)) * ∑ j,
      sixVertexContinuousOffsetKernel c (p i) (p j) /
        sixVertexFiniteRootDensity c N n p (p j) =
      (∑ j, sixVertexContinuousOffsetKernel c (p i) (p j) /
        sixVertexFiniteRootDensity c N n p (p j)) / N by ring]
  linarith

theorem tendsto_sixVertexFixedChargeOffsetRowError_of_lower
    {c lower : Real} (hlower : 0 < lower) (r : Nat) :
    Tendsto (fun k => sixVertexFixedChargeOffsetRowError c
      (sixVertexFourWidth r k) r lower) atTop (nhds 0) := by
  let C := (sixVertexOffsetQuotientLipschitzNNReal c lower 1 0 : Real) *
      sixVertexFiniteRootDensityUniformBound c *
        ((2 * (r : Real) + 1) / lower) * (2 * Real.pi) +
    2 * (r : Real) *
      ((sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1)) / lower)
  have hwidthNat : Tendsto (sixVertexFourWidth r) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto (fun k : Nat => (sixVertexFourWidth r k : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hwidthNat
  have hzero : Tendsto (fun k : Nat => C / (sixVertexFourWidth r k : Real))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hwidth
  convert hzero using 1
  funext k
  dsimp [C]
  unfold sixVertexFixedChargeOffsetRowError
  field_simp [hlower.ne']

def sixVertexCanonicalOffsetNetMargin
    (c : Real) (N r : Nat) (lower : Real) : Real :=
  sixVertexFixedChargeOffsetContractionMargin c -
    sixVertexFixedChargeOffsetRowError c N r lower

theorem tendsto_sixVertexCanonicalOffsetNetMargin
    {c lower : Real} (hlower : 0 < lower) (r : Nat) :
    Tendsto (fun k => sixVertexCanonicalOffsetNetMargin c
      (sixVertexFourWidth r k) r lower) atTop
      (nhds (sixVertexFixedChargeOffsetContractionMargin c)) := by
  simpa [sixVertexCanonicalOffsetNetMargin] using
    tendsto_const_nhds.sub
      (tendsto_sixVertexFixedChargeOffsetRowError_of_lower hlower r)

theorem eventually_sixVertexCanonicalOffsetNetMargin_pos
    {c lower : Real} (hc : 2 < c) (hlower : 0 < lower) (r : Nat) :
    ∀ᶠ k : Nat in atTop,
      0 < sixVertexCanonicalOffsetNetMargin c
        (sixVertexFourWidth r k) r lower := by
  exact (tendsto_sixVertexCanonicalOffsetNetMargin hlower r).eventually
    (Ioi_mem_nhds (sixVertexFixedChargeOffsetContractionMargin_pos hc))

def sixVertexCanonicalEvenOffsetNodalError
    (c : Real) (hc : 2 < c) (s N : Nat) (testError : Real) : Real :=
  4 * sixVertexThetaTaylorBound c *
      sixVertexCanonicalEvenOffsetUniformBound c hc s ^ 2 / N +
    2 * (s : Real) ^ 2 *
        (sixVertexThetaRightLipschitzNNReal c : Real) /
      ((N : Real) * sixVertexCanonicalHalfDensityFloor hc) +
    (2 * s : Real) * (sixVertexThetaRightLipschitzNNReal c : Real) *
      (sixVertexCanonicalEvenOffsetUniformBound c hc s / N) +
    (2 * s : Real) * testError

def sixVertexCanonicalOddOffsetNodalError
    (c : Real) (hc : 2 < c) (s N n : Nat) (testError : Real) : Real :=
  4 * sixVertexThetaTaylorBound c *
      sixVertexCanonicalOddOffsetUniformBound c hc s ^ 2 / N +
    ((2 * s + 1 : Real) *
          (sixVertexThetaRightLipschitzNNReal c : Real) * (s + 2 : Real) /
        ((N : Real) * sixVertexCanonicalHalfDensityFloor hc) +
      (n : Real) * sixVertexThetaTaylorBound c /
        (((N : Real) * sixVertexCanonicalHalfDensityFloor hc) ^ 2)) +
    (2 * s + 1 : Real) * (sixVertexThetaRightLipschitzNNReal c : Real) *
      (sixVertexCanonicalOddOffsetUniformBound c hc s / N) +
    (2 * s + 1 : Real) * testError

theorem abs_sixVertexCanonicalEvenDensityOffset_sub_continuous_le
    {c : Real} (hc : 2 < c) (s k : Nat)
    (hfixed : SixVertexCanonicalFixedEvenDensityWitness hc s k
      (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k))
    (hhalf : forall y, sixVertexCanonicalHalfDensityFloor hc <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth 0 (2 * s + k))
        ((2 * s + k + 1) + (2 * s + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + k)) y)
    {tau : Real -> Real} (htauOdd : Function.Odd tau)
    (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
    {testError : Real}
    (hquad : forall i : Fin ((s + k + 1) + (s + k + 1)),
      |(∑ l, sixVertexContinuousOffsetKernel c
            (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k i)
            (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k l) *
            tau (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k l) /
            sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
              ((s + k + 1) + (s + k + 1))
              (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k)
              (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k l)) /
          sixVertexFourWidth (2 * s) k -
        ∫ y in -Real.pi..Real.pi,
          sixVertexContinuousOffsetKernel c
            (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k i) y *
            tau y| <= testError)
    (hoffset : forall j,
      |sixVertexCanonicalEvenChargeOffset hc s k j| <=
        sixVertexCanonicalEvenOffsetUniformBound c hc s)
    (hmargin : 0 < sixVertexCanonicalOffsetNetMargin c
      (sixVertexFourWidth (2 * s) k) (2 * s)
      (sixVertexCanonicalFixedEvenDensityFloor hc s))
    (i : Fin ((s + k + 1) + (s + k + 1))) :
    |sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
          ((s + k + 1) + (s + k + 1))
          (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k)
          (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k i) *
        sixVertexCanonicalEvenChargeOffset hc s k i -
      (2 * s : Real) * tau
        (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k i)| <=
      sixVertexCanonicalEvenOffsetNodalError c hc s
          (sixVertexFourWidth (2 * s) k) testError /
        sixVertexCanonicalOffsetNetMargin c
          (sixVertexFourWidth (2 * s) k) (2 * s)
          (sixVertexCanonicalFixedEvenDensityFloor hc s) := by
  let r := 2 * s
  let N := sixVertexFourWidth r k
  let n := (s + k + 1) + (s + k + 1)
  let p := sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k
  let rhoF := sixVertexFiniteRootDensity c N n p
  let rho : Fin n -> Real := fun l => rhoF (p l)
  let eps := sixVertexCanonicalEvenChargeOffset hc s k
  let aligned := sixVertexCanonicalEvenAlignedHalfRoots hc s k
  let a : Real := r
  let lower := sixVertexCanonicalFixedEvenDensityFloor hc s
  let halfLower := sixVertexCanonicalHalfDensityFloor hc
  let B := sixVertexCanonicalEvenOffsetUniformBound c hc s
  let rowError := sixVertexFixedChargeOffsetRowError c N r lower
  let rowBound := 2 * Real.pi + rowError
  let residualError := 4 * sixVertexThetaTaylorBound c * B ^ 2 / N
  let boundaryError := 2 * (s : Real) ^ 2 *
    (sixVertexThetaRightLipschitzNNReal c : Real) /
      ((N : Real) * halfLower)
  let sourceMoveError := (r : Real) *
    (sixVertexThetaRightLipschitzNNReal c : Real) * (B / N)
  let reciprocalMass := sixVertexRootDensityScale c /
    (4 * (sixVertexAnisotropyMagnitude c + 1) *
      sixVertexFiniteRootDensityUniformBound c)
  have hN : 0 < N := sixVertexFourWidth_pos r k
  have hn : 0 < n := by dsimp [n]; omega
  have hcharge : N = 2 * n + 2 * r := by
    dsimp [N, n, r]
    unfold sixVertexFourWidth
    omega
  have hlower : 0 < lower := sixVertexCanonicalFixedEvenDensityFloor_pos hc s
  have hhalfLower : 0 < halfLower := sixVertexCanonicalHalfDensityFloor_pos hc
  have hrho (l : Fin n) : 0 < rho l :=
    hlower.trans_le (hfixed.2 (p l))
  have hpIcc (l : Fin n) : p l ∈ Set.Icc (-Real.pi) Real.pi :=
    ⟨(hfixed.1.1.2.2 l).1.le, (hfixed.1.1.2.2 l).2.le⟩
  have hmass : (1 / (N : Real)) * ∑ l,
      (rho l * eps l - a * tau (p l)) /
        (sixVertexRootDensityWeight c (p l) * rho l) = 0 := by
    have hzero := sum_sixVertexCanonicalEvenWeightedOffsetError_eq_zero
      hc s k hfixed.1 htauOdd a
    change ∑ l, (rho l * eps l - a * tau (p l)) /
      (sixVertexRootDensityWeight c (p l) * rho l) = 0 at hzero
    rw [hzero, mul_zero]
  have hrow (l : Fin n) : (1 / (N : Real)) * ∑ j,
      sixVertexContinuousOffsetKernel c (p l) (p j) / rho j <= rowBound := by
    exact empiricalContinuousOffsetKernel_le_of_lower hc hN hn hcharge
      hfixed.1.1 hfixed.1.2.1 hlower hfixed.2 l
  have hreciprocal : reciprocalMass <= (1 / (N : Real)) * ∑ l,
      1 / (sixVertexRootDensityWeight c (p l) * rho l) := by
    apply reciprocalWeightDensityMass_le_of_lower hc hN
      (by dsimp [n, N, r]; unfold sixVertexFourWidth; omega)
      (by dsimp [n, N, r]; unfold sixVertexFourWidth; omega)
      hlower hfixed.2
  have hlinear (l : Fin n) :
      2 * Real.pi * (rho l * eps l) + (1 / (N : Real)) * ∑ j,
          sixVertexContinuousOffsetKernel c (p l) (p j) * eps j =
        sixVertexCanonicalEvenOffsetNodalResidual hc s k l +
          sixVertexCanonicalEvenOffsetBoundarySource hc s k l := by
    have hres := sixVertexCanonicalEvenOffsetNodalResidual_eq_weightedConvolution
      hc s k l
    change sixVertexCanonicalEvenOffsetNodalResidual hc s k l =
      2 * Real.pi * (rho l * eps l) -
        sixVertexCanonicalEvenOffsetBoundarySource hc s k l +
        (1 / (N : Real)) * ∑ j,
          sixVertexContinuousOffsetKernel c (p l) (p j) * eps j at hres
    linarith
  have hB : 0 <= B := sixVertexCanonicalEvenOffsetUniformBound_nonneg hc s
  have hresidual (l : Fin n) :
      |sixVertexCanonicalEvenOffsetNodalResidual hc s k l| <= residualError :=
    abs_sixVertexCanonicalEvenOffsetNodalResidual_le hc s k hfixed.1
      hB hoffset l
  have hboundary (l : Fin n) :
      |sixVertexCanonicalEvenOffsetBoundarySource hc s k l -
        a * sixVertexContinuousOffsetSource c (aligned l)| <= boundaryError := by
    have h := abs_sixVertexCanonicalEvenOffsetBoundarySource_sub_continuous_le
      hc s k hhalfLower hhalf l
    have hwidth : sixVertexFourWidth 0 (r + k) = N := by
      dsimp [N, r]
      unfold sixVertexFourWidth
      omega
    rw [hwidth] at h
    simpa [a, r, n, aligned, boundaryError, halfLower] using h
  have hsourceMove (l : Fin n) :
      |a * (sixVertexContinuousOffsetSource c (aligned l) -
        sixVertexContinuousOffsetSource c (p l))| <= sourceMoveError := by
    have haligned : aligned l = p l - eps l / N := by
      dsimp [aligned, eps]
      unfold sixVertexCanonicalEvenChargeOffset
      have hN0 : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
      change _ = p l - ((N : Real) * (p l - _)) / N
      field_simp [hN0]
      ring
    have hlip := (lipschitzWith_sixVertexContinuousOffsetSource hc).dist_le_mul
      (aligned l) (p l)
    rw [Real.dist_eq, Real.dist_eq, haligned, sub_sub_cancel_left,
      abs_neg, abs_div, abs_of_pos (by exact_mod_cast hN : (0 : Real) < N)] at hlip
    rw [abs_mul, abs_of_nonneg (by positivity : 0 <= a)]
    have hcore := hlip.trans (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (hoffset l)
        (by exact_mod_cast hN.le : (0 : Real) <= N))
      (NNReal.coe_nonneg _))
    have hscaled := mul_le_mul_of_nonneg_left hcore (by positivity : 0 <= a)
    simpa [sourceMoveError, a, r, B, mul_assoc, haligned] using hscaled
  have hmargin' : 0 < 2 * Real.pi -
      (rowBound - sixVertexRootDensityKernelFloor c * reciprocalMass) := by
    have heq : 2 * Real.pi -
        (rowBound - sixVertexRootDensityKernelFloor c * reciprocalMass) =
          sixVertexCanonicalOffsetNetMargin c N r lower := by
      dsimp [rowBound, rowError, reciprocalMass]
      unfold sixVertexCanonicalOffsetNetMargin
        sixVertexFixedChargeOffsetContractionMargin
      ring
    rw [heq]
    exact hmargin
  have h := abs_densityOffset_sub_continuous_le_of_data hc hN hn
    (p := p) (rho := rho) (eps := eps) (a := a) (tau := tau)
    (aligned := aligned)
    (boundary := sixVertexCanonicalEvenOffsetBoundarySource hc s k)
    (residual := sixVertexCanonicalEvenOffsetNodalResidual hc s k)
    (rowBound := rowBound) (reciprocalMass := reciprocalMass)
    (residualError := residualError) (boundaryError := boundaryError)
    (sourceMoveError := sourceMoveError) (testError := testError)
    (by positivity) hrho hpIcc hmass hrow hreciprocal hlinear hresidual
    hboundary hsourceMove hquad htauEq hmargin' i
  have hmarginEq : 2 * Real.pi -
      (rowBound - sixVertexRootDensityKernelFloor c * reciprocalMass) =
        sixVertexCanonicalOffsetNetMargin c N r lower := by
    dsimp [rowBound, rowError, reciprocalMass]
    unfold sixVertexCanonicalOffsetNetMargin
      sixVertexFixedChargeOffsetContractionMargin
    ring
  rw [hmarginEq] at h
  simpa [sixVertexCanonicalEvenOffsetNodalError, rho, rhoF, eps, p,
    a, r, N, B, lower, halfLower, residualError, boundaryError,
    sourceMoveError] using h

theorem abs_sixVertexCanonicalOddDensityOffset_sub_continuous_le
    {c : Real} (hc : 2 < c) (s k : Nat)
    (hfixed : SixVertexCanonicalFixedOddDensityWitness hc s k
      (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k))
    (hhalf : forall y, sixVertexCanonicalHalfDensityFloor hc <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth 0 (2 * s + 1 + k))
        ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))
        (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) y)
    {tau : Real -> Real} (htauOdd : Function.Odd tau)
    (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
    {testError : Real}
    (hquad : forall i : Fin (((s + k + 1) + 1) + (s + k + 1)),
      |(∑ l, sixVertexContinuousOffsetKernel c
            (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k i)
            (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k l) *
            tau (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k l) /
            sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
              (((s + k + 1) + 1) + (s + k + 1))
              (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
              (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k l)) /
          sixVertexFourWidth (2 * s + 1) k -
        ∫ y in -Real.pi..Real.pi,
          sixVertexContinuousOffsetKernel c
            (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k i) y *
            tau y| <= testError)
    (hoffset : forall j,
      |sixVertexCanonicalOddChargeOffset hc s k j| <=
        sixVertexCanonicalOddOffsetUniformBound c hc s)
    (hmargin : 0 < sixVertexCanonicalOffsetNetMargin c
      (sixVertexFourWidth (2 * s + 1) k) (2 * s + 1)
      (sixVertexCanonicalFixedOddDensityFloor hc s))
    (i : Fin (((s + k + 1) + 1) + (s + k + 1))) :
    |sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
          (((s + k + 1) + 1) + (s + k + 1))
          (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
          (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k i) *
        sixVertexCanonicalOddChargeOffset hc s k i -
      (2 * s + 1 : Real) * tau
        (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k i)| <=
      sixVertexCanonicalOddOffsetNodalError c hc s
          (sixVertexFourWidth (2 * s + 1) k)
          (((s + k + 1) + 1) + (s + k + 1)) testError /
        sixVertexCanonicalOffsetNetMargin c
          (sixVertexFourWidth (2 * s + 1) k) (2 * s + 1)
          (sixVertexCanonicalFixedOddDensityFloor hc s) := by
  let r := 2 * s + 1
  let N := sixVertexFourWidth r k
  let n := ((s + k + 1) + 1) + (s + k + 1)
  let p := sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k
  let rhoF := sixVertexFiniteRootDensity c N n p
  let rho : Fin n -> Real := fun l => rhoF (p l)
  let eps := sixVertexCanonicalOddChargeOffset hc s k
  let aligned := sixVertexCanonicalOddAlignedHalfRoots hc s k
  let a : Real := r
  let lower := sixVertexCanonicalFixedOddDensityFloor hc s
  let halfLower := sixVertexCanonicalHalfDensityFloor hc
  let B := sixVertexCanonicalOddOffsetUniformBound c hc s
  let rowError := sixVertexFixedChargeOffsetRowError c N r lower
  let rowBound := 2 * Real.pi + rowError
  let residualError := 4 * sixVertexThetaTaylorBound c * B ^ 2 / N
  let boundaryError := (r : Real) *
      (sixVertexThetaRightLipschitzNNReal c : Real) * (s + 2 : Real) /
        ((N : Real) * halfLower) +
    (n : Real) * sixVertexThetaTaylorBound c /
      (((N : Real) * halfLower) ^ 2)
  let sourceMoveError := (r : Real) *
    (sixVertexThetaRightLipschitzNNReal c : Real) * (B / N)
  let reciprocalMass := sixVertexRootDensityScale c /
    (4 * (sixVertexAnisotropyMagnitude c + 1) *
      sixVertexFiniteRootDensityUniformBound c)
  have hN : 0 < N := sixVertexFourWidth_pos r k
  have hn : 0 < n := by dsimp [n]; omega
  have hcharge : N = 2 * n + 2 * r := by
    dsimp [N, n, r]
    unfold sixVertexFourWidth
    omega
  have hlower : 0 < lower := sixVertexCanonicalFixedOddDensityFloor_pos hc s
  have hhalfLower : 0 < halfLower := sixVertexCanonicalHalfDensityFloor_pos hc
  have hrho (l : Fin n) : 0 < rho l :=
    hlower.trans_le (hfixed.2 (p l))
  have hpIcc (l : Fin n) : p l ∈ Set.Icc (-Real.pi) Real.pi :=
    ⟨(hfixed.1.1.2.2 l).1.le, (hfixed.1.1.2.2 l).2.le⟩
  have hmass : (1 / (N : Real)) * ∑ l,
      (rho l * eps l - a * tau (p l)) /
        (sixVertexRootDensityWeight c (p l) * rho l) = 0 := by
    have hzero := sum_sixVertexCanonicalOddWeightedOffsetError_eq_zero
      hc s k hfixed.1 htauOdd a
    change ∑ l, (rho l * eps l - a * tau (p l)) /
      (sixVertexRootDensityWeight c (p l) * rho l) = 0 at hzero
    rw [hzero, mul_zero]
  have hrow (l : Fin n) : (1 / (N : Real)) * ∑ j,
      sixVertexContinuousOffsetKernel c (p l) (p j) / rho j <= rowBound := by
    exact empiricalContinuousOffsetKernel_le_of_lower hc hN hn hcharge
      hfixed.1.1 hfixed.1.2.1 hlower hfixed.2 l
  have hreciprocal : reciprocalMass <= (1 / (N : Real)) * ∑ l,
      1 / (sixVertexRootDensityWeight c (p l) * rho l) := by
    apply reciprocalWeightDensityMass_le_of_lower hc hN
      (by dsimp [n, N, r]; unfold sixVertexFourWidth; omega)
      (by dsimp [n, N, r]; unfold sixVertexFourWidth; omega)
      hlower hfixed.2
  have hlinear (l : Fin n) :
      2 * Real.pi * (rho l * eps l) + (1 / (N : Real)) * ∑ j,
          sixVertexContinuousOffsetKernel c (p l) (p j) * eps j =
        sixVertexCanonicalOddOffsetNodalResidual hc s k l +
          sixVertexCanonicalOddOffsetBoundarySource hc s k l := by
    have hres := sixVertexCanonicalOddOffsetNodalResidual_eq_weightedConvolution
      hc s k l
    change sixVertexCanonicalOddOffsetNodalResidual hc s k l =
      2 * Real.pi * (rho l * eps l) -
        sixVertexCanonicalOddOffsetBoundarySource hc s k l +
        (1 / (N : Real)) * ∑ j,
          sixVertexContinuousOffsetKernel c (p l) (p j) * eps j at hres
    linarith
  have hB : 0 <= B := sixVertexCanonicalOddOffsetUniformBound_nonneg hc s
  have hresidual (l : Fin n) :
      |sixVertexCanonicalOddOffsetNodalResidual hc s k l| <= residualError :=
    abs_sixVertexCanonicalOddOffsetNodalResidual_le hc s k hfixed.1
      hB hoffset l
  have hboundary (l : Fin n) :
      |sixVertexCanonicalOddOffsetBoundarySource hc s k l -
        a * sixVertexContinuousOffsetSource c (aligned l)| <= boundaryError := by
    have h := abs_sixVertexCanonicalOddOffsetBoundarySource_sub_continuous_le
      hc s k hhalfLower hhalf l
    have hwidth : sixVertexFourWidth 0 (r + k) = N := by
      dsimp [N, r]
      unfold sixVertexFourWidth
      omega
    rw [hwidth] at h
    simpa [a, r, n, aligned, boundaryError, halfLower] using h
  have hsourceMove (l : Fin n) :
      |a * (sixVertexContinuousOffsetSource c (aligned l) -
        sixVertexContinuousOffsetSource c (p l))| <= sourceMoveError := by
    have haligned : aligned l = p l - eps l / N := by
      dsimp [aligned, eps]
      unfold sixVertexCanonicalOddChargeOffset
      have hN0 : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
      change _ = p l - ((N : Real) * (p l - _)) / N
      field_simp [hN0]
      ring
    have hlip := (lipschitzWith_sixVertexContinuousOffsetSource hc).dist_le_mul
      (aligned l) (p l)
    rw [Real.dist_eq, Real.dist_eq, haligned, sub_sub_cancel_left,
      abs_neg, abs_div, abs_of_pos (by exact_mod_cast hN : (0 : Real) < N)] at hlip
    rw [abs_mul, abs_of_nonneg (by positivity : 0 <= a)]
    have hcore := hlip.trans (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (hoffset l)
        (by exact_mod_cast hN.le : (0 : Real) <= N))
      (NNReal.coe_nonneg _))
    have hscaled := mul_le_mul_of_nonneg_left hcore (by positivity : 0 <= a)
    simpa [sourceMoveError, a, r, B, mul_assoc, haligned] using hscaled
  have hmargin' : 0 < 2 * Real.pi -
      (rowBound - sixVertexRootDensityKernelFloor c * reciprocalMass) := by
    have heq : 2 * Real.pi -
        (rowBound - sixVertexRootDensityKernelFloor c * reciprocalMass) =
          sixVertexCanonicalOffsetNetMargin c N r lower := by
      dsimp [rowBound, rowError, reciprocalMass]
      unfold sixVertexCanonicalOffsetNetMargin
        sixVertexFixedChargeOffsetContractionMargin
      ring
    rw [heq]
    exact hmargin
  have h := abs_densityOffset_sub_continuous_le_of_data hc hN hn
    (p := p) (rho := rho) (eps := eps) (a := a) (tau := tau)
    (aligned := aligned)
    (boundary := sixVertexCanonicalOddOffsetBoundarySource hc s k)
    (residual := sixVertexCanonicalOddOffsetNodalResidual hc s k)
    (rowBound := rowBound) (reciprocalMass := reciprocalMass)
    (residualError := residualError) (boundaryError := boundaryError)
    (sourceMoveError := sourceMoveError) (testError := testError)
    (by positivity) hrho hpIcc hmass hrow hreciprocal hlinear hresidual
    hboundary hsourceMove hquad htauEq hmargin' i
  have hmarginEq : 2 * Real.pi -
      (rowBound - sixVertexRootDensityKernelFloor c * reciprocalMass) =
        sixVertexCanonicalOffsetNetMargin c N r lower := by
    dsimp [rowBound, rowError, reciprocalMass]
    unfold sixVertexCanonicalOffsetNetMargin
      sixVertexFixedChargeOffsetContractionMargin
    ring
  rw [hmarginEq] at h
  simpa [sixVertexCanonicalOddOffsetNodalError, rho, rhoF, eps, p, n,
    a, r, N, B, lower, halfLower, residualError, boundaryError,
    sourceMoveError] using h

theorem tendsto_sixVertexCanonicalEvenOffsetNodalError
    {c : Real} (hc : 2 < c) (s : Nat) (G : Real) (D : NNReal) :
    Tendsto (fun k => sixVertexCanonicalEvenOffsetNodalError c hc s
      (sixVertexFourWidth (2 * s) k)
      (sixVertexFixedChargeNonperiodicOffsetTestError c
        (sixVertexFourWidth (2 * s) k) (2 * s)
        (sixVertexCanonicalFixedEvenDensityFloor hc s) G D))
      atTop (nhds 0) := by
  let r := 2 * s
  let lower := sixVertexCanonicalFixedEvenDensityFloor hc s
  let halfLower := sixVertexCanonicalHalfDensityFloor hc
  let B := sixVertexCanonicalEvenOffsetUniformBound c hc s
  have hlower : 0 < lower := sixVertexCanonicalFixedEvenDensityFloor_pos hc s
  have hhalfLower : 0 < halfLower := sixVertexCanonicalHalfDensityFloor_pos hc
  have hwidthNat : Tendsto (sixVertexFourWidth r) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto (fun k : Nat => (sixVertexFourWidth r k : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hwidthNat
  have hdiv (C : Real) : Tendsto
      (fun k => C / (sixVertexFourWidth r k : Real)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hwidth
  have hresidual := hdiv (4 * sixVertexThetaTaylorBound c * B ^ 2)
  have hboundary : Tendsto (fun k =>
      2 * (s : Real) ^ 2 * (sixVertexThetaRightLipschitzNNReal c : Real) /
        ((sixVertexFourWidth r k : Real) * halfLower)) atTop (nhds 0) := by
    convert hdiv (2 * (s : Real) ^ 2 *
      (sixVertexThetaRightLipschitzNNReal c : Real) / halfLower) using 1
    funext k
    field_simp [hhalfLower.ne']
  have hsource := hdiv ((r : Real) *
    (sixVertexThetaRightLipschitzNNReal c : Real) * B)
  have htest := tendsto_sixVertexFixedChargeNonperiodicOffsetTestError
    c r hlower G D
  have htestScaled := htest.const_mul (r : Real)
  simpa [sixVertexCanonicalEvenOffsetNodalError, r, lower, halfLower, B,
    div_eq_mul_inv, mul_assoc] using
      (((hresidual.add hboundary).add hsource).add htestScaled)

theorem tendsto_sixVertexCanonicalOddOffsetNodalError
    {c : Real} (hc : 2 < c) (s : Nat) (G : Real) (D : NNReal) :
    Tendsto (fun k => sixVertexCanonicalOddOffsetNodalError c hc s
      (sixVertexFourWidth (2 * s + 1) k)
      (((s + k + 1) + 1) + (s + k + 1))
      (sixVertexFixedChargeNonperiodicOffsetTestError c
        (sixVertexFourWidth (2 * s + 1) k) (2 * s + 1)
        (sixVertexCanonicalFixedOddDensityFloor hc s) G D))
      atTop (nhds 0) := by
  let r := 2 * s + 1
  let lower := sixVertexCanonicalFixedOddDensityFloor hc s
  let halfLower := sixVertexCanonicalHalfDensityFloor hc
  let B := sixVertexCanonicalOddOffsetUniformBound c hc s
  let T := sixVertexThetaTaylorBound c
  have hlower : 0 < lower := sixVertexCanonicalFixedOddDensityFloor_pos hc s
  have hhalfLower : 0 < halfLower := sixVertexCanonicalHalfDensityFloor_pos hc
  have hT : 0 <= T := by
    dsimp [T, sixVertexThetaTaylorBound, sixVertexThetaCrossLipschitzBound]
    exact add_nonneg (sixVertexThetaLeftKernelLipschitzBound_pos hc).le
      (div_nonneg (sixVertexRootDensityKernelLipschitzBound_pos hc).le
        (div_nonneg
          (sub_nonneg.mpr (one_lt_sixVertexAnisotropyMagnitude hc).le)
          (sixVertexRootDensityScale_pos hc).le))
  have hwidthNat : Tendsto (sixVertexFourWidth r) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto (fun k : Nat => (sixVertexFourWidth r k : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hwidthNat
  have hdiv (C : Real) : Tendsto
      (fun k => C / (sixVertexFourWidth r k : Real)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hwidth
  have hresidual := hdiv (4 * T * B ^ 2)
  have hboundaryFirst : Tendsto (fun k =>
      (r : Real) * (sixVertexThetaRightLipschitzNNReal c : Real) *
          (s + 2 : Real) /
        ((sixVertexFourWidth r k : Real) * halfLower)) atTop (nhds 0) := by
    convert hdiv ((r : Real) *
      (sixVertexThetaRightLipschitzNNReal c : Real) *
        (s + 2 : Real) / halfLower) using 1
    funext k
    field_simp [hhalfLower.ne']
  have hmidUpper := hdiv (T / halfLower ^ 2)
  have hboundaryMid : Tendsto (fun k =>
      ((((s + k + 1) + 1) + (s + k + 1) : Nat) : Real) * T /
        (((sixVertexFourWidth r k : Real) * halfLower) ^ 2))
      atTop (nhds 0) := by
    apply squeeze_zero' (g := fun k =>
      (T / halfLower ^ 2) / (sixVertexFourWidth r k : Real))
    · filter_upwards [] with k
      positivity
    · filter_upwards [] with k
      let N := sixVertexFourWidth r k
      let n := ((s + k + 1) + 1) + (s + k + 1)
      have hN : 0 < N := sixVertexFourWidth_pos r k
      have hNreal : 0 < (N : Real) := by exact_mod_cast hN
      have hnle : n <= N := by
        dsimp [n, N, r]
        unfold sixVertexFourWidth
        omega
      have hnleReal : (n : Real) <= N := by exact_mod_cast hnle
      calc
        (n : Real) * T / (((N : Real) * halfLower) ^ 2) <=
            (N : Real) * T / (((N : Real) * halfLower) ^ 2) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hnleReal hT) (sq_nonneg _)
        _ = (T / halfLower ^ 2) / N := by
          field_simp [hNreal.ne', hhalfLower.ne']
    · exact hmidUpper
  have hsource := hdiv ((r : Real) *
    (sixVertexThetaRightLipschitzNNReal c : Real) * B)
  have htest := tendsto_sixVertexFixedChargeNonperiodicOffsetTestError
    c r hlower G D
  have htestScaled := htest.const_mul (r : Real)
  simpa [sixVertexCanonicalOddOffsetNodalError, r, lower, halfLower, B, T,
    div_eq_mul_inv, mul_assoc] using
      ((((hresidual.add (hboundaryFirst.add hboundaryMid)).add hsource).add
        htestScaled))

theorem eventually_uniform_sixVertexCanonicalEvenDensityOffset
    {c : Real} (hc : 2 < c) (s : Nat)
    {tau : Real -> Real} {D : NNReal} {G : Real}
    (htauLip : LipschitzWith D tau)
    (htauBound : forall y, |tau y| <= G)
    (htauOdd : Function.Odd tau)
    (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∀ᶠ k : Nat in atTop,
      forall i : Fin ((s + k + 1) + (s + k + 1)),
        |sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
              ((s + k + 1) + (s + k + 1))
              (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k)
              (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k i) *
            sixVertexCanonicalEvenChargeOffset hc s k i -
          (2 * s : Real) * tau
            (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k i)| <
          epsilon := by
  let r := 2 * s
  let lower := sixVertexCanonicalFixedEvenDensityFloor hc s
  have hlower : 0 < lower := sixVertexCanonicalFixedEvenDensityFloor_pos hc s
  have herror := tendsto_sixVertexCanonicalEvenOffsetNodalError hc s G D
  have hmargin := tendsto_sixVertexCanonicalOffsetNetMargin (c := c) hlower r
  have hquot : Tendsto (fun k =>
      sixVertexCanonicalEvenOffsetNodalError c hc s
          (sixVertexFourWidth r k)
          (sixVertexFixedChargeNonperiodicOffsetTestError c
            (sixVertexFourWidth r k) r lower G D) /
        sixVertexCanonicalOffsetNetMargin c
          (sixVertexFourWidth r k) r lower) atTop (nhds 0) := by
    simpa [r, lower] using herror.div hmargin
      (sixVertexFixedChargeOffsetContractionMargin_pos hc).ne'
  have hsmall := hquot.eventually (Iio_mem_nhds hepsilon)
  have hshift : Tendsto (fun k : Nat => r + k) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by omega)).tendsto_atTop
  filter_upwards
    [eventually_sixVertexCanonicalFixedEvenDensityPerronBetheRoots_witness hc s,
      eventually_abs_sixVertexCanonicalEvenChargeOffset_le hc s,
      hshift.eventually (eventually_sixVertexCanonicalHalfDensityFloor_le hc),
      eventually_sixVertexCanonicalOffsetNetMargin_pos hc hlower r,
      hsmall] with k hfixed hoffset hhalf hmarginPos hsmallK
  intro i
  have hN : 0 < sixVertexFourWidth r k := sixVertexFourWidth_pos r k
  have hn : 0 < (s + k + 1) + (s + k + 1) := by omega
  have hcharge : sixVertexFourWidth r k =
      2 * ((s + k + 1) + (s + k + 1)) + 2 * r := by
    dsimp [r]
    unfold sixVertexFourWidth
    omega
  have hquad (l : Fin ((s + k + 1) + (s + k + 1))) :=
    abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_pos_of_lipschitz_nonperiodic
      hc hN hn hcharge hfixed.1.1 hfixed.1.2.1 hlower hfixed.2
      (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k l)
      htauLip htauBound
  exact (abs_sixVertexCanonicalEvenDensityOffset_sub_continuous_le
    hc s k hfixed (by simpa [r] using hhalf) htauOdd htauEq hquad hoffset
      hmarginPos i).trans_lt hsmallK

theorem eventually_uniform_sixVertexCanonicalOddDensityOffset
    {c : Real} (hc : 2 < c) (s : Nat)
    {tau : Real -> Real} {D : NNReal} {G : Real}
    (htauLip : LipschitzWith D tau)
    (htauBound : forall y, |tau y| <= G)
    (htauOdd : Function.Odd tau)
    (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∀ᶠ k : Nat in atTop,
      forall i : Fin (((s + k + 1) + 1) + (s + k + 1)),
        |sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
              (((s + k + 1) + 1) + (s + k + 1))
              (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
              (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k i) *
            sixVertexCanonicalOddChargeOffset hc s k i -
          (2 * s + 1 : Real) * tau
            (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k i)| <
          epsilon := by
  let r := 2 * s + 1
  let lower := sixVertexCanonicalFixedOddDensityFloor hc s
  have hlower : 0 < lower := sixVertexCanonicalFixedOddDensityFloor_pos hc s
  have herror := tendsto_sixVertexCanonicalOddOffsetNodalError hc s G D
  have hmargin := tendsto_sixVertexCanonicalOffsetNetMargin (c := c) hlower r
  have hquot : Tendsto (fun k =>
      sixVertexCanonicalOddOffsetNodalError c hc s
          (sixVertexFourWidth r k)
          (((s + k + 1) + 1) + (s + k + 1))
          (sixVertexFixedChargeNonperiodicOffsetTestError c
            (sixVertexFourWidth r k) r lower G D) /
        sixVertexCanonicalOffsetNetMargin c
          (sixVertexFourWidth r k) r lower) atTop (nhds 0) := by
    simpa [r, lower] using herror.div hmargin
      (sixVertexFixedChargeOffsetContractionMargin_pos hc).ne'
  have hsmall := hquot.eventually (Iio_mem_nhds hepsilon)
  have hshift : Tendsto (fun k : Nat => r + k) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by omega)).tendsto_atTop
  filter_upwards
    [eventually_sixVertexCanonicalFixedOddDensityPerronBetheRoots_witness hc s,
      eventually_abs_sixVertexCanonicalOddChargeOffset_le hc s,
      hshift.eventually (eventually_sixVertexCanonicalHalfDensityFloor_le hc),
      eventually_sixVertexCanonicalOffsetNetMargin_pos hc hlower r,
      hsmall] with k hfixed hoffset hhalf hmarginPos hsmallK
  intro i
  have hN : 0 < sixVertexFourWidth r k := sixVertexFourWidth_pos r k
  have hn : 0 < ((s + k + 1) + 1) + (s + k + 1) := by omega
  have hcharge : sixVertexFourWidth r k =
      2 * (((s + k + 1) + 1) + (s + k + 1)) + 2 * r := by
    dsimp [r]
    unfold sixVertexFourWidth
    omega
  have hquad (l : Fin (((s + k + 1) + 1) + (s + k + 1))) :=
    abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_pos_of_lipschitz_nonperiodic
      hc hN hn hcharge hfixed.1.1 hfixed.1.2.1 hlower hfixed.2
      (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k l)
      htauLip htauBound
  exact (abs_sixVertexCanonicalOddDensityOffset_sub_continuous_le
    hc s k hfixed (by simpa [r] using hhalf) htauOdd htauEq hquad hoffset
      hmarginPos i).trans_lt hsmallK

end

end StatMech.FrontierD
