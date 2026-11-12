/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheOffsetBoundarySource
import Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate
import Code.FrontierD.SixVertexBetheContinuousOffset










namespace StatMech.FrontierD

open Finset

noncomputable section



def sixVertexThetaRightLipschitzNNReal (c : Real) : NNReal :=
  Real.toNNReal (sixVertexAnisotropyMagnitude c /
    (sixVertexAnisotropyMagnitude c - 1))

theorem coe_sixVertexThetaRightLipschitzNNReal
    {c : Real} (hc : 2 < c) :
    (sixVertexThetaRightLipschitzNNReal c : Real) =
      sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1) := by
  apply Real.coe_toNNReal
  exact div_nonneg
    (le_trans (by norm_num) (one_lt_sixVertexAnisotropyMagnitude hc).le)
    (sub_nonneg.mpr (one_lt_sixVertexAnisotropyMagnitude hc).le)

theorem lipschitzWith_sixVertexTheta_right
    {c : Real} (hc : 2 < c) (x : Real) :
    LipschitzWith (sixVertexThetaRightLipschitzNNReal c)
      (fun y => sixVertexTheta c x y) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro y
    exact (hasDerivAt_sixVertexTheta_right hc x y).differentiableAt
  · intro y
    rw [(hasDerivAt_sixVertexTheta_right hc x y).deriv]
    apply NNReal.coe_le_coe.mp
    rw [coe_sixVertexThetaRightLipschitzNNReal hc, coe_nnnorm]
    exact norm_sixVertexTheta_rightDerivative_le hc x y



theorem sixVertexBetheSolution_sub_first_le_of_finiteDensityLower
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    {p : Fin (n + 1) -> Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : forall x, lower <=
      sixVertexFiniteRootDensity c N (n + 1) p x)
    (i : Fin (n + 1)) :
    p i - p 0 <= (i.val : Real) / ((N : Real) * lower) := by
  have horder : p 0 <= p i := hopen.1.monotone (Fin.zero_le i)
  have hmono := intervalIntegral.integral_mono_on horder
    (continuous_const.intervalIntegrable
      (μ := MeasureTheory.volume) _ _)
    ((continuous_sixVertexFiniteRootDensity hc N (n + 1) p).intervalIntegrable _ _)
    (fun x _ => hdensity x)
  rw [intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul] at hmono
  rw [intervalIntegral_sixVertexFiniteRootDensity_eq_counting_sub
    hc hN p (p 0) (p i),
    sixVertexBetheCountingFunction_at_root hN hsol i,
    sixVertexBetheCountingFunction_at_root hN hsol 0] at hmono
  have hquantum :
      sixVertexCentralQuantumNumber i -
          sixVertexCentralQuantumNumber (0 : Fin (n + 1)) = i.val := by
    rw [sixVertexCentralQuantumNumber_eq,
      sixVertexCentralQuantumNumber_eq]
    simp
  have hright :
      sixVertexCentralQuantumNumber i / (N : Real) -
          sixVertexCentralQuantumNumber (0 : Fin (n + 1)) / N =
        (i.val : Real) / N := by
    rw [<- sub_div, hquantum]
  rw [hright] at hmono
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  calc
    p i - p 0 <= ((i.val : Real) / N) / lower := by
      rw [le_div_iff₀ hlower]
      simpa [mul_comm] using hmono
    _ = (i.val : Real) / ((N : Real) * lower) := by ring



theorem sixVertexBetheSolution_first_endpoint_le_of_finiteDensityLower
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hhalf : N = 2 * (n + 1)) {p : Fin (n + 1) -> Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : forall x, lower <=
      sixVertexFiniteRootDensity c N (n + 1) p x)
    (i : Fin (n + 1)) :
    p i - (-Real.pi) <=
      ((i.val : Real) + 1) / ((N : Real) * lower) := by
  have hboundary :=
    sixVertexBetheSolution_boundarySpacing_upper_of_finiteDensityLower
      hc hN hhalf hopen hsol hlower hdensity
  have hsymm := hopen.2.1 (0 : Fin (n + 1))
  have hboundary' :
      p 0 - (p (0 : Fin (n + 1)).rev - 2 * Real.pi) <=
        1 / ((N : Real) * lower) := by
    simpa [Fin.rev] using hboundary
  rw [hsymm] at hboundary'
  have hden : 0 < (N : Real) * lower :=
    mul_pos (by exact_mod_cast hN) hlower
  have hedge : p 0 + Real.pi <= 1 / ((N : Real) * lower) := by
    have hinv : 0 <= 1 / ((N : Real) * lower) := (one_div_pos.mpr hden).le
    nlinarith
  have hinside :=
    sixVertexBetheSolution_sub_first_le_of_finiteDensityLower
      hc hN hopen hsol hlower hdensity i
  calc
    p i - (-Real.pi) = (p i - p 0) + (p 0 + Real.pi) := by ring
    _ <= (i.val : Real) / ((N : Real) * lower) +
        1 / ((N : Real) * lower) := add_le_add hinside hedge
    _ = ((i.val : Real) + 1) / ((N : Real) * lower) := by ring


theorem sixVertexBetheSolution_last_endpoint_le_of_finiteDensityLower
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hhalf : N = 2 * (n + 1)) {p : Fin (n + 1) -> Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : forall x, lower <=
      sixVertexFiniteRootDensity c N (n + 1) p x)
    (i : Fin (n + 1)) :
    Real.pi - p i <=
      ((i.rev.val : Real) + 1) / ((N : Real) * lower) := by
  have hfirst :=
    sixVertexBetheSolution_first_endpoint_le_of_finiteDensityLower
      hc hN hhalf hopen hsol hlower hdensity i.rev
  rw [hopen.2.1 i] at hfirst
  linarith



theorem abs_sixVertexEvenChargeOffsetBoundarySource_sub_continuous_le
    {c : Real} (hc : 2 < c) (s k : Nat)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : forall y, lower <=
      sixVertexFiniteRootDensity c (sixVertexFourWidth 0 (2 * s + k))
        ((2 * s + k + 1) + (2 * s + k + 1))
        (sixVertexHalfFilledBetheRoots hc (2 * s + k)) y)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) :
    |sixVertexEvenChargeOffsetBoundarySource hc s k j -
        (2 * s : Real) * sixVertexContinuousOffsetSource c
          (sixVertexEvenChargeAlignedHalfRoots hc s k j)| <=
      2 * (s : Real) ^ 2 *
          (sixVertexThetaRightLipschitzNNReal c : Real) /
        ((sixVertexFourWidth 0 (2 * s + k) : Real) * lower) := by
  let t := 2 * s + k
  let N := sixVertexFourWidth 0 t
  let p := sixVertexHalfFilledBetheRoots hc t
  let x := sixVertexEvenChargeAlignedHalfRoots hc s k j
  let A := (sixVertexThetaRightLipschitzNNReal c : Real)
  let D := (N : Real) * lower
  have hN : 0 < N := sixVertexFourWidth_pos 0 t
  have hhalf : N = 2 * ((t + 1) + (t + 1)) := by
    dsimp [N, t]
    unfold sixVertexFourWidth
    omega
  have hopen : SixVertexOpenRootSimplex p := by
    exact sixVertexHalfFilledBetheRoots_mem_open hc t
  have hsol : SixVertexSatisfiesBetheEquations c N
      ((t + 1) + (t + 1)) p := by
    exact sixVertexHalfFilledBetheRoots_is_solution hc t
  have hD : 0 < D := mul_pos (by exact_mod_cast hN) hlower
  have hA : 0 <= A := NNReal.coe_nonneg _
  have hlip := lipschitzWith_sixVertexTheta_right hc x
  have hleftRoot (i : Fin s) :
      p (sixVertexEvenChargeLeftBoundaryIndex s k i) - (-Real.pi) <=
        (s : Real) / D := by
    have h := sixVertexBetheSolution_first_endpoint_le_of_finiteDensityLower
      hc hN hhalf hopen hsol hlower hdensity
        (sixVertexEvenChargeLeftBoundaryIndex s k i)
    have hindex :
        (((sixVertexEvenChargeLeftBoundaryIndex s k i).val : Real) + 1) <= s := by
      dsimp [sixVertexEvenChargeLeftBoundaryIndex]
      exact_mod_cast i.isLt
    exact h.trans (div_le_div_of_nonneg_right hindex hD.le)
  have hrightRoot (i : Fin s) :
      Real.pi - p (sixVertexEvenChargeRightBoundaryIndex s k i) <=
        (s : Real) / D := by
    have h := sixVertexBetheSolution_last_endpoint_le_of_finiteDensityLower
      hc hN hhalf hopen hsol hlower hdensity
        (sixVertexEvenChargeRightBoundaryIndex s k i)
    have hindex :
        ((((sixVertexEvenChargeRightBoundaryIndex s k i).rev.val : Nat) : Real) + 1) <=
          s := by
      have hindexNat :
          (sixVertexEvenChargeRightBoundaryIndex s k i).rev.val + 1 <= s := by
        simp only [Fin.rev, sixVertexEvenChargeRightBoundaryIndex, Fin.val_mk,
          sixVertexFixedChargeBetheParticleCount_eq]
        omega
      exact_mod_cast hindexNat
    exact h.trans (div_le_div_of_nonneg_right hindex hD.le)
  have hleftPoint (i : Fin s) :
      |sixVertexTheta c x
            (p (sixVertexEvenChargeLeftBoundaryIndex s k i)) -
          sixVertexTheta c x (-Real.pi)| <= A * ((s : Real) / D) := by
    have hdist := hlip.dist_le_mul
      (p (sixVertexEvenChargeLeftBoundaryIndex s k i)) (-Real.pi)
    rw [Real.dist_eq, Real.dist_eq] at hdist
    have hroot :
        |p (sixVertexEvenChargeLeftBoundaryIndex s k i) - (-Real.pi)| <=
          (s : Real) / D := by
      rw [abs_of_nonneg]
      · exact hleftRoot i
      · exact sub_nonneg.mpr
          (hopen.2.2 (sixVertexEvenChargeLeftBoundaryIndex s k i)).1.le
    exact hdist.trans (mul_le_mul_of_nonneg_left hroot hA)
  have hrightPoint (i : Fin s) :
      |sixVertexTheta c x
            (p (sixVertexEvenChargeRightBoundaryIndex s k i)) -
          sixVertexTheta c x Real.pi| <= A * ((s : Real) / D) := by
    have hdist := hlip.dist_le_mul
      (p (sixVertexEvenChargeRightBoundaryIndex s k i)) Real.pi
    rw [Real.dist_eq, Real.dist_eq] at hdist
    have hroot :
        |p (sixVertexEvenChargeRightBoundaryIndex s k i) - Real.pi| <=
          (s : Real) / D := by
      rw [abs_of_nonpos]
      · simpa only [neg_sub] using hrightRoot i
      · exact sub_nonpos.mpr
          (hopen.2.2 (sixVertexEvenChargeRightBoundaryIndex s k i)).2.le
    exact hdist.trans (mul_le_mul_of_nonneg_left hroot hA)
  have hleftSum :
      |(∑ i : Fin s,
          sixVertexTheta c x
            (p (sixVertexEvenChargeLeftBoundaryIndex s k i))) -
        (s : Real) * sixVertexTheta c x (-Real.pi)| <=
          (s : Real) * (A * ((s : Real) / D)) := by
    have hconst :
        (s : Real) * sixVertexTheta c x (-Real.pi) =
          ∑ _i : Fin s, sixVertexTheta c x (-Real.pi) := by simp
    rw [hconst, <- sum_sub_distrib]
    calc
      |∑ i : Fin s,
          (sixVertexTheta c x
              (p (sixVertexEvenChargeLeftBoundaryIndex s k i)) -
            sixVertexTheta c x (-Real.pi))| <=
          ∑ i : Fin s,
            |sixVertexTheta c x
                (p (sixVertexEvenChargeLeftBoundaryIndex s k i)) -
              sixVertexTheta c x (-Real.pi)| := abs_sum_le_sum_abs _ _
      _ <= ∑ _i : Fin s, A * ((s : Real) / D) :=
        sum_le_sum fun i _ => hleftPoint i
      _ = (s : Real) * (A * ((s : Real) / D)) := by simp
  have hrightSum :
      |(∑ i : Fin s,
          sixVertexTheta c x
            (p (sixVertexEvenChargeRightBoundaryIndex s k i))) -
        (s : Real) * sixVertexTheta c x Real.pi| <=
          (s : Real) * (A * ((s : Real) / D)) := by
    have hconst :
        (s : Real) * sixVertexTheta c x Real.pi =
          ∑ _i : Fin s, sixVertexTheta c x Real.pi := by simp
    rw [hconst, <- sum_sub_distrib]
    calc
      |∑ i : Fin s,
          (sixVertexTheta c x
              (p (sixVertexEvenChargeRightBoundaryIndex s k i)) -
            sixVertexTheta c x Real.pi)| <=
          ∑ i : Fin s,
            |sixVertexTheta c x
                (p (sixVertexEvenChargeRightBoundaryIndex s k i)) -
              sixVertexTheta c x Real.pi| := abs_sum_le_sum_abs _ _
      _ <= ∑ _i : Fin s, A * ((s : Real) / D) :=
        sum_le_sum fun i _ => hrightPoint i
      _ = (s : Real) * (A * ((s : Real) / D)) := by simp
  rw [sixVertexEvenChargeOffsetBoundarySource_eq_boundarySums hc s k j]
  change |((∑ i : Fin s,
      sixVertexTheta c x
        (p (sixVertexEvenChargeLeftBoundaryIndex s k i))) +
      (∑ i : Fin s,
        sixVertexTheta c x
          (p (sixVertexEvenChargeRightBoundaryIndex s k i)))) -
      (2 * s : Real) * sixVertexContinuousOffsetSource c x| <= _
  unfold sixVertexContinuousOffsetSource
  have hrearrange :
      ((∑ i : Fin s,
          sixVertexTheta c x
            (p (sixVertexEvenChargeLeftBoundaryIndex s k i))) +
        (∑ i : Fin s,
          sixVertexTheta c x
            (p (sixVertexEvenChargeRightBoundaryIndex s k i)))) -
          (2 * s : Real) *
            ((sixVertexTheta c x (-Real.pi) +
              sixVertexTheta c x Real.pi) / 2) =
        ((∑ i : Fin s,
            sixVertexTheta c x
              (p (sixVertexEvenChargeLeftBoundaryIndex s k i))) -
          (s : Real) * sixVertexTheta c x (-Real.pi)) +
        ((∑ i : Fin s,
            sixVertexTheta c x
              (p (sixVertexEvenChargeRightBoundaryIndex s k i))) -
          (s : Real) * sixVertexTheta c x Real.pi) := by
    ring
  rw [hrearrange]
  calc
    |_ + _| <=
        |(∑ i : Fin s,
            sixVertexTheta c x
              (p (sixVertexEvenChargeLeftBoundaryIndex s k i))) -
          (s : Real) * sixVertexTheta c x (-Real.pi)| +
        |(∑ i : Fin s,
            sixVertexTheta c x
              (p (sixVertexEvenChargeRightBoundaryIndex s k i))) -
          (s : Real) * sixVertexTheta c x Real.pi| := abs_add_le _ _
    _ <= (s : Real) * (A * ((s : Real) / D)) +
        (s : Real) * (A * ((s : Real) / D)) := add_le_add hleftSum hrightSum
    _ = 2 * (s : Real) ^ 2 * A / D := by ring

end

end StatMech.FrontierD
