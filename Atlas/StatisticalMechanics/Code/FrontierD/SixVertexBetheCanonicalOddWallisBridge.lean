/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalOddWallisCore





namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

theorem tendsto_sixVertexOddWallisReferenceProduct_bridge (s : Nat) :
    Tendsto (fun k =>
      (sixVertexFourWidth (2 * s + 1) k : Real) *
        sixVertexOddWallisHalfProduct (s + k + 1) ^ 2)
      atTop (nhds (4 / Real.pi)) :=
  tendsto_sixVertexOddWallisReferenceProduct s

def sixVertexCanonicalOddActualHalfProduct
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  ∏ j : Fin (s + k + 1),
    ‖sixVertexBetheM c (sixVertexBethePhase
        (sixVertexCanonicalOddMidpointHalfRoot hc s k j))‖ /
      ‖sixVertexBetheM c (sixVertexBethePhase
        (sixVertexCanonicalOddLeftHalfRoot hc s k j))‖

theorem sixVertexCanonicalOddActualHalfProduct_pos
    {c : Real} (hc : 2 < c) (s k : Nat) :
    0 < sixVertexCanonicalOddActualHalfProduct hc s k := by
  unfold sixVertexCanonicalOddActualHalfProduct
  exact Finset.prod_pos fun j hj => div_pos
    (norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc _))
    (norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc _))

theorem sixVertexCanonicalOddZeroModeWallisCorrection_eq_log_product
    {c : Real} (hc : 2 < c) (s k : Nat)
    (hfixed : SixVertexCanonicalFixedOddDensityWitness hc s k
      (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)) :
    sixVertexCanonicalOddZeroModeWallisCorrection hc s k =
      Real.log
        ((sixVertexZeroPhaseBethePrefactor c
            (sixVertexFourWidth (2 * s + 1) k)
            (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
            (sixVertexOddCentralIndex (s + k + 1)) / 2) *
          sixVertexCanonicalOddActualHalfProduct hc s k ^ 2) := by
  let P := sixVertexZeroPhaseBethePrefactor c
    (sixVertexFourWidth (2 * s + 1) k)
    (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
    (sixVertexOddCentralIndex (s + k + 1))
  have hcentral :=
    sixVertexCanonicalFixedOddDensityPerronBetheRoots_central_eq_zero
      hc s k hfixed
  have hP : 0 < P := sixVertexZeroPhaseBethePrefactor_pos hc
    (by unfold sixVertexFourWidth; omega)
    _ _ hcentral
  have hterm (j : Fin (s + k + 1)) :
      0 < ‖sixVertexBetheM c (sixVertexBethePhase
        (sixVertexCanonicalOddMidpointHalfRoot hc s k j))‖ /
      ‖sixVertexBetheM c (sixVertexBethePhase
        (sixVertexCanonicalOddLeftHalfRoot hc s k j))‖ :=
    div_pos (norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc _))
      (norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc _))
  have hlogProd : Real.log (sixVertexCanonicalOddActualHalfProduct hc s k) =
      ∑ j : Fin (s + k + 1),
        Real.log (‖sixVertexBetheM c (sixVertexBethePhase
            (sixVertexCanonicalOddMidpointHalfRoot hc s k j))‖ /
          ‖sixVertexBetheM c (sixVertexBethePhase
            (sixVertexCanonicalOddLeftHalfRoot hc s k j))‖) := by
    unfold sixVertexCanonicalOddActualHalfProduct
    rw [Real.log_prod (fun j hj => (hterm j).ne')]
  unfold sixVertexCanonicalOddZeroModeWallisCorrection
    sixVertexBetheLogObservable
  rw [Real.log_mul (div_ne_zero hP.ne' (by norm_num))
      (pow_ne_zero 2
        (sixVertexCanonicalOddActualHalfProduct_pos hc s k).ne'),
    Real.log_div hP.ne' (by norm_num : (2 : Real) ≠ 0),
    Real.log_pow, hlogProd]
  simp_rw [Real.log_div
    (norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc _)).ne'
    (norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc _)).ne']
  ring

def sixVertexCanonicalOddWallisProductRatio
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  sixVertexCanonicalOddActualHalfProduct hc s k /
    sixVertexOddWallisHalfProduct (s + k + 1)



def SixVertexCanonicalOddGeneralizedWallisComparison
    {c : Real} (hc : 2 < c) (s : Nat) : Prop :=
  Tendsto (fun k => sixVertexCanonicalOddWallisProductRatio hc s k ^ 2)
    atTop (nhds
      (Real.cosh (sixVertexAntiferroelectricLambda c) /
        (4 * c ^ 2 * sixVertexFourierPhysicalDensity c hc 0)))

def sixVertexCanonicalOddSmoothWallisLog
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  let N := sixVertexFourWidth (2 * s + 1) k
  let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
  2 * ∑ j : Fin (s + k + 1),
    ((sixVertexBetheLogObservable c
          (sixVertexCanonicalOddMidpointHalfRoot hc s k j) +
        Real.log (sixVertexBetheCountingFunction c N n p
          (sixVertexCanonicalOddMidpointHalfRoot hc s k j))) -
      (sixVertexBetheLogObservable c
          (sixVertexCanonicalOddLeftHalfRoot hc s k j) +
        Real.log (sixVertexBetheCountingFunction c N n p
          (sixVertexCanonicalOddLeftHalfRoot hc s k j))))

def SixVertexCanonicalOddSmoothWallisLimit
    {c : Real} (hc : 2 < c) (s : Nat) : Prop :=
  Tendsto (sixVertexCanonicalOddSmoothWallisLog hc s) atTop
    (nhds (Real.log
      (Real.cosh (sixVertexAntiferroelectricLambda c) /
        (4 * c ^ 2 * sixVertexFourierPhysicalDensity c hc 0))))

theorem log_sixVertexCanonicalOddWallisProductRatio_sq
    {c : Real} (hc : 2 < c) (s k : Nat) :
    Real.log (sixVertexCanonicalOddWallisProductRatio hc s k ^ 2) =
      sixVertexCanonicalOddSmoothWallisLog hc s k -
        2 * (
          let N := sixVertexFourWidth (2 * s + 1) k
          let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
          let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
          ∑ j : Fin (s + k + 1),
            (Real.log (sixVertexBetheCountingFunction c N n p
                (sixVertexCanonicalOddMidpointHalfRoot hc s k j)) -
              Real.log (((j : Real) + 1) / N))) := by
  let N := sixVertexFourWidth (2 * s + 1) k
  let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
  let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
  let A := sixVertexCanonicalOddActualHalfProduct hc s k
  let W := sixVertexOddWallisHalfProduct (s + k + 1)
  have hA : 0 < A := sixVertexCanonicalOddActualHalfProduct_pos hc s k
  have hW : 0 < W := by
    dsimp [W, sixVertexOddWallisHalfProduct]
    exact Finset.prod_pos fun j hj => div_pos (by positivity) (by positivity)
  have hterm (j : Fin (s + k + 1)) :
      0 < ‖sixVertexBetheM c (sixVertexBethePhase
          (sixVertexCanonicalOddMidpointHalfRoot hc s k j))‖ /
        ‖sixVertexBetheM c (sixVertexBethePhase
          (sixVertexCanonicalOddLeftHalfRoot hc s k j))‖ :=
    div_pos (norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc _))
      (norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc _))
  have hlogA : Real.log A =
      ∑ j : Fin (s + k + 1),
        (sixVertexBetheLogObservable c
            (sixVertexCanonicalOddMidpointHalfRoot hc s k j) -
          sixVertexBetheLogObservable c
            (sixVertexCanonicalOddLeftHalfRoot hc s k j)) := by
    dsimp [A, sixVertexCanonicalOddActualHalfProduct,
      sixVertexBetheLogObservable]
    rw [Real.log_prod (fun j hj => (hterm j).ne')]
    simp_rw [Real.log_div
      (norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc _)).ne'
      (norm_pos_iff.mpr (sixVertexBetheM_phase_ne_zero hc _)).ne']
  have hlogW : Real.log W =
      ∑ j : Fin (s + k + 1),
        (Real.log (sixVertexBetheCountingFunction c N n p
            (sixVertexCanonicalOddLeftHalfRoot hc s k j)) -
          Real.log (((j : Real) + 1) / N)) := by
    have hN : 0 < (N : Real) := by
      exact_mod_cast sixVertexFourWidth_pos (2 * s + 1) k
    have hNne : (sixVertexFourWidth (2 * s + 1) k : Real) ≠ 0 := by
      exact_mod_cast (sixVertexFourWidth_pos (2 * s + 1) k).ne'
    have href :
        (∑ j : Fin (s + k + 1),
          (Real.log (sixVertexBetheCountingFunction c N n p
              (sixVertexCanonicalOddLeftHalfRoot hc s k j)) -
            Real.log (((j : Real) + 1) / N))) =
          sixVertexOddWallisReferenceLogSum (s + k + 1) := by
      calc
        _ = ∑ j : Fin (s + k + 1),
            Real.log (((2 * j.val + 1 : Nat) : Real) /
              (2 * j.val + 2)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [sixVertexCanonicalOddLeftHalfRoot_countingFunction hc s k j]
          dsimp [N]
          rw [← Real.log_div]
          · congr 1
            field_simp [hN.ne']
            push_cast
            simp [hNne, mul_assoc]
            ring
          · positivity
          · positivity
        _ = ∑ j ∈ Finset.range (s + k + 1),
            Real.log (((2 * j + 1 : Nat) : Real) / (2 * j + 2)) := by
          simpa using (Fin.sum_univ_eq_sum_range (fun j : Nat =>
            Real.log (((2 * j + 1 : Nat) : Real) / (2 * j + 2)))
              (s + k + 1))
        _ = _ := rfl
    exact (sixVertexOddWallisReferenceLogSum_eq_log _).symm.trans href.symm
  unfold sixVertexCanonicalOddWallisProductRatio
  rw [Real.log_pow, Real.log_div hA.ne' hW.ne', hlogA, hlogW]
  dsimp [sixVertexCanonicalOddSmoothWallisLog, N, n, p]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [div_eq_mul_inv, add_mul, one_mul, mul_comm, add_comm]
  ring_nf

theorem sixVertexCanonicalOddGeneralizedWallisComparison_of_smooth
    {c : Real} (hc : 2 < c) (s : Nat)
    (hsmooth : SixVertexCanonicalOddSmoothWallisLimit hc s) :
    SixVertexCanonicalOddGeneralizedWallisComparison hc s := by
  let E : Nat → Real := fun k =>
    let N := sixVertexFourWidth (2 * s + 1) k
    let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)
    let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)
    ∑ j : Fin (s + k + 1),
      (Real.log (sixVertexBetheCountingFunction c N n p
          (sixVertexCanonicalOddMidpointHalfRoot hc s k j)) -
        Real.log (((j : Real) + 1) / N))
  let L := Real.cosh (sixVertexAntiferroelectricLambda c) /
    (4 * c ^ 2 * sixVertexFourierPhysicalDensity c hc 0)
  have hE : Tendsto E atTop (nhds 0) :=
    tendsto_sum_log_sixVertexCanonicalOddMidpointCounting_sub_reference hc s
  have hlog : Tendsto (fun k => Real.log
      (sixVertexCanonicalOddWallisProductRatio hc s k ^ 2)) atTop
      (nhds (Real.log L)) := by
    have h := hsmooth.sub (hE.const_mul 2)
    simpa [E, L, log_sixVertexCanonicalOddWallisProductRatio_sq hc s] using h
  have hexp : Tendsto (fun k => Real.exp (Real.log
      (sixVertexCanonicalOddWallisProductRatio hc s k ^ 2))) atTop
      (nhds (Real.exp (Real.log L))) :=
    Real.continuous_exp.continuousAt.tendsto.comp hlog
  have hpos : 0 < L := by
    dsimp [L]
    exact div_pos (Real.cosh_pos _)
      (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos (by linarith)))
        (sixVertexFourierPhysicalDensity_pos hc 0))
  unfold SixVertexCanonicalOddGeneralizedWallisComparison
  have hexp' : Tendsto (fun k =>
      sixVertexCanonicalOddWallisProductRatio hc s k ^ 2) atTop
      (nhds L) := by
    rw [← Real.exp_log hpos]
    apply hexp.congr'
    filter_upwards [] with k
    rw [Real.exp_log]
    exact pow_pos (div_pos
      (sixVertexCanonicalOddActualHalfProduct_pos hc s k)
      (by
        unfold sixVertexOddWallisHalfProduct
        exact Finset.prod_pos fun j hj => div_pos (by positivity) (by positivity))) 2
  exact hexp'

def sixVertexCanonicalOddWallisProductArgument
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  (sixVertexZeroPhaseBethePrefactor c
      (sixVertexFourWidth (2 * s + 1) k)
      (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
      (sixVertexOddCentralIndex (s + k + 1)) / 2) *
    sixVertexCanonicalOddActualHalfProduct hc s k ^ 2

theorem tendsto_sixVertexCanonicalOddWallisProductArgument_of_comparison
    {c : Real} (hc : 2 < c) (s : Nat)
    (hcomparison : SixVertexCanonicalOddGeneralizedWallisComparison hc s) :
    Tendsto (sixVertexCanonicalOddWallisProductArgument hc s) atTop
      (nhds (Real.cosh (sixVertexAntiferroelectricLambda c))) := by
  let rho0 := sixVertexFourierPhysicalDensity c hc 0
  let A : Nat -> Real := fun k =>
    sixVertexCanonicalOddZeroPrefactorNormalized hc s k / 2
  let B : Nat -> Real := fun k =>
    (sixVertexFourWidth (2 * s + 1) k : Real) *
      sixVertexOddWallisHalfProduct (s + k + 1) ^ 2
  let R : Nat -> Real := fun k =>
    sixVertexCanonicalOddWallisProductRatio hc s k ^ 2
  have hA : Tendsto A atTop
      (nhds ((c ^ 2 * (2 * Real.pi) * rho0) / 2)) :=
    (tendsto_sixVertexCanonicalOddZeroPrefactorNormalized hc s).div_const 2
  have hB : Tendsto B atTop (nhds (4 / Real.pi)) :=
    tendsto_sixVertexOddWallisReferenceProduct_bridge s
  have hR : Tendsto R atTop
      (nhds (Real.cosh (sixVertexAntiferroelectricLambda c) /
        (4 * c ^ 2 * rho0))) := hcomparison
  have hmul := (hA.mul hB).mul hR
  have hlimit :
      (c ^ 2 * (2 * Real.pi) * rho0 / 2) * (4 / Real.pi) *
          (Real.cosh (sixVertexAntiferroelectricLambda c) /
            (4 * c ^ 2 * rho0)) =
        Real.cosh (sixVertexAntiferroelectricLambda c) := by
    have hc0 : c ≠ 0 := by linarith
    have hrho : rho0 ≠ 0 := (sixVertexFourierPhysicalDensity_pos hc 0).ne'
    field_simp [hc0, hrho, Real.pi_ne_zero]
  rw [hlimit] at hmul
  apply hmul.congr'
  filter_upwards [] with k
  have hN : (sixVertexFourWidth (2 * s + 1) k : Real) ≠ 0 := by
    exact_mod_cast (sixVertexFourWidth_pos (2 * s + 1) k).ne'
  have href : sixVertexOddWallisHalfProduct (s + k + 1) ≠ 0 :=
    ne_of_gt (Finset.prod_pos fun j hj => div_pos (by positivity) (by positivity))
  unfold A B R sixVertexCanonicalOddWallisProductArgument
    sixVertexCanonicalOddWallisProductRatio
    sixVertexCanonicalOddZeroPrefactorNormalized
  field_simp [hN, href]

theorem sixVertexCanonicalOddZeroModeWallisLimit_of_comparison
    {c : Real} (hc : 2 < c) (s : Nat)
    (hcomparison : SixVertexCanonicalOddGeneralizedWallisComparison hc s) :
    SixVertexCanonicalOddZeroModeWallisLimit hc s := by
  have harg :=
    tendsto_sixVertexCanonicalOddWallisProductArgument_of_comparison
      hc s hcomparison
  have hlog : Tendsto (fun k => Real.log
      (sixVertexCanonicalOddWallisProductArgument hc s k)) atTop
      (nhds (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)))) :=
    (Real.continuousAt_log (Real.cosh_pos _).ne').tendsto.comp harg
  unfold SixVertexCanonicalOddZeroModeWallisLimit
  apply hlog.congr'
  filter_upwards
    [eventually_sixVertexCanonicalFixedOddDensityPerronBetheRoots_witness hc s]
      with k hk
  exact (sixVertexCanonicalOddZeroModeWallisCorrection_eq_log_product
    hc s k hk).symm

theorem sixVertexCanonicalFixedOddCharge_matchesOffsetFourier_of_comparison
    {c : Real} (hc : 2 < c) (s : Nat)
    (hcomparison : SixVertexCanonicalOddGeneralizedWallisComparison hc s) :
    SixVertexCanonicalFixedChargeBetheCandidateMatchesOffsetFourier hc
      (2 * s + 1) := by
  exact sixVertexCanonicalFixedOddCharge_matchesOffsetFourier_of_three_limits
    hc s
    (by
      simpa [Nat.cast_add, Nat.cast_mul] using
        tendsto_sixVertexCanonicalOddBulkLogDisplacement hc s)
    (sixVertexCanonicalOddZeroModeWallisLimit_of_comparison hc s hcomparison)
    (by
      simpa [sixVertexCanonicalOddBoundaryLogSum] using
        tendsto_sum_sixVertexCanonicalOddBoundaryLogObservable hc s)

end

end StatMech.FrontierD
