/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheLogRegularizationCutoff
import Code.FrontierD.SixVertexBetheCanonicalRegularizedQuadrature





namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

theorem sixVertexBetheLogObservable_eq_logNormKernel
    {c x : Real} (hc : 2 < c) (hx : x ∈ Set.Ioo 0 Real.pi) :
    sixVertexBetheLogObservable c x = sixVertexBetheLogNormKernel c x := by
  have hphase : sixVertexBethePhase x ≠ 1 :=
    sixVertexBethePhase_ne_one_of_mem_Ioo
      ⟨(neg_lt_zero.mpr Real.pi_pos).trans hx.1, hx.2⟩ hx.1.ne'
  unfold sixVertexBetheLogObservable
  rw [sixVertexBetheM_log_norm_eq_logNumerator_sub_logDenominator hc hphase]
  unfold sixVertexBetheLogNormKernel sixVertexBetheLogNumerator
    sixVertexBetheLogDenominator
  rfl

def sixVertexCanonicalEvenBulkLogDisplacement
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  ∑ j, (sixVertexBetheLogObservable c
      (sixVertexCanonicalFixedEvenDensityPositiveRoots hc s k j) -
    sixVertexBetheLogObservable c
      (sixVertexCanonicalEvenCommonHalfRoot hc s k j))

theorem eventually_abs_sixVertexCanonicalEvenBulkLogDisplacement_sub_regularized_le
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (s : Nat) {M : Nat} (hM : 0 < M) :
    ∀ᶠ k : Nat in atTop,
      let N := sixVertexFourWidth (2 * s) k
      let C := sixVertexCanonicalEvenOffsetLinearBound c hc s
      |sixVertexCanonicalEvenBulkLogDisplacement hc s k -
          sixVertexCanonicalEvenRegularizedBulkLogDisplacement
            hc epsilon s k| <=
        2 * Real.pi * C * (1 / M + 1 / N) +
          epsilon * C * Real.pi * M ^ 4 / 16 := by
  filter_upwards
    [eventually_abs_sum_sixVertexCanonicalEvenLogRegularizationError_le_simple
      hc hepsilon s hM,
      eventually_sixVertexCanonicalFixedEvenDensityPerronBetheRoots_witness
        hc s] with k hk hfixed
  let n := s + k + 1
  let q : Fin n -> Real :=
    sixVertexCanonicalFixedEvenDensityPositiveRoots hc s k
  let p : Fin n -> Real := sixVertexCanonicalEvenCommonHalfRoot hc s k
  have hq (j : Fin n) : q j ∈ Set.Ioo 0 Real.pi := by
    apply sixVertexEvenSymmetricLift_positive_mem_Ioo
    unfold q sixVertexCanonicalFixedEvenDensityPositiveRoots
    rw [sixVertexEvenSymmetricLift_projection (s + k + 1)
      hfixed.1.1.2.1]
    exact hfixed.1.1
  have hp (j : Fin n) : p j ∈ Set.Ioo 0 Real.pi := by
    exact sixVertexCanonicalDensityPerronPositiveHalfRoots_mem_Ioo hc
      (2 * s + k) ⟨j.val, by dsimp [n] at j ⊢; omega⟩
  have heq :
      sixVertexCanonicalEvenBulkLogDisplacement hc s k -
          sixVertexCanonicalEvenRegularizedBulkLogDisplacement
            hc epsilon s k =
        ∑ j : Fin n,
          (sixVertexBetheLogRegularizationError c epsilon (q j) -
            sixVertexBetheLogRegularizationError c epsilon (p j)) := by
    unfold sixVertexCanonicalEvenBulkLogDisplacement
      sixVertexCanonicalEvenRegularizedBulkLogDisplacement
      sixVertexBetheLogRegularizationError
    rw [<- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [sixVertexBetheLogObservable_eq_logNormKernel hc (hq j),
      sixVertexBetheLogObservable_eq_logNormKernel hc (hp j)]
    ring
  rw [heq]
  simpa [q, p, n] using hk

def sixVertexLogRegularizationSchedule (m : Nat) : Real :=
  1 / ((m : Real) + 1)

theorem tendsto_sixVertexLogRegularizationSchedule :
    Tendsto sixVertexLogRegularizationSchedule atTop (nhds 0) := by
  change Tendsto (fun m : Nat => 1 / ((m : Real) + 1)) atTop (nhds 0)
  simpa only [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))

theorem sixVertexLogRegularizationSchedule_pos (m : Nat) :
    0 < sixVertexLogRegularizationSchedule m := by
  unfold sixVertexLogRegularizationSchedule
  positivity

theorem tendsto_sixVertexRegularizedLogPairing_schedule
    {c : Real} (hc : 2 < c) :
    Tendsto (fun m =>
      ∫ x in -Real.pi..Real.pi,
        sixVertexRegularizedBetheLogNormDerivative c
            (sixVertexLogRegularizationSchedule m) x *
          sixVertexContinuousOffsetFourier c hc x) atTop
      (nhds (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) -
        sixVertexAntiferroelectricGapRate
          (sixVertexAntiferroelectricLambda c))) := by
  have h := tendsto_sixVertexOffsetLogFourierDampedValue_regularization
    (sixVertexAntiferroelectricLambda_pos hc)
    tendsto_sixVertexLogRegularizationSchedule
    (Eventually.of_forall sixVertexLogRegularizationSchedule_pos)
  apply h.congr'
  filter_upwards [] with m
  exact (intervalIntegral_sixVertexRegularizedBetheLogDerivative_mul_offset
    hc (sixVertexLogRegularizationSchedule_pos m)).symm

theorem tendsto_sixVertexCanonicalEvenBulkLogDisplacement
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (sixVertexCanonicalEvenBulkLogDisplacement hc s) atTop
      (nhds ((2 * s : Real) / 2 *
        (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) -
          sixVertexAntiferroelectricGapRate
            (sixVertexAntiferroelectricLambda c)))) := by
  let raw := sixVertexCanonicalEvenBulkLogDisplacement hc s
  let reg : Nat -> Nat -> Real := fun m =>
    sixVertexCanonicalEvenRegularizedBulkLogDisplacement hc
      (sixVertexLogRegularizationSchedule m) s
  let value : Nat -> Real := fun m => (2 * s : Real) / 2 *
    (∫ x in -Real.pi..Real.pi,
      sixVertexRegularizedBetheLogNormDerivative c
          (sixVertexLogRegularizationSchedule m) x *
        sixVertexContinuousOffsetFourier c hc x)
  let target : Real := (2 * s : Real) / 2 *
    (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) -
      sixVertexAntiferroelectricGapRate
        (sixVertexAntiferroelectricLambda c))
  have hreg (m : Nat) : Tendsto (reg m) atTop (nhds (value m)) := by
    exact tendsto_sixVertexCanonicalEvenRegularizedBulkLogDisplacement hc
      (sixVertexLogRegularizationSchedule_pos m) s
  have hvalue : Tendsto value atTop (nhds target) := by
    exact (tendsto_sixVertexRegularizedLogPairing_schedule hc).const_mul
      ((2 * s : Real) / 2)
  have hC : 0 <= sixVertexCanonicalEvenOffsetLinearBound c hc s :=
    sixVertexCanonicalEvenOffsetLinearBound_nonneg hc s
  have hwidthNat : Tendsto (sixVertexFourWidth (2 * s)) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto
      (fun k : Nat => (sixVertexFourWidth (2 * s) k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwidthNat
  have happrox : forall eta : Real, 0 < eta -> exists m : Nat,
      dist (value m) target < eta ∧
        ∀ᶠ k : Nat in atTop, dist (raw k) (reg m k) < eta := by
    intro eta heta
    let A := 2 * Real.pi * sixVertexCanonicalEvenOffsetLinearBound c hc s
    have hA : 0 <= A := by dsimp [A]; positivity
    obtain ⟨M0, hM0⟩ : exists M0 : Nat,
        A * (1 / ((M0 + 1 : Nat) : Real)) < eta / 3 := by
      by_cases hAzero : A = 0
      · exact ⟨0, by simp [hAzero, heta]⟩
      · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
        obtain ⟨M0, hM0⟩ := exists_nat_one_div_lt
          (show 0 < eta / (3 * A) by positivity)
        refine ⟨M0, ?_⟩
        calc
          A * (1 / ((M0 + 1 : Nat) : Real)) <
              A * (eta / (3 * A)) := by
            apply mul_lt_mul_of_pos_left _ hApos
            simpa only [Nat.cast_add, Nat.cast_one] using hM0
          _ = eta / 3 := by field_simp [hApos.ne']
    let M := M0 + 1
    have hM : 0 < M := Nat.succ_pos _
    let K := sixVertexCanonicalEvenOffsetLinearBound c hc s *
      Real.pi * (M : Real) ^ 4 / 16
    have hK : 0 <= K := by dsimp [K]; positivity
    have hepsK : Tendsto
        (fun m => sixVertexLogRegularizationSchedule m * K) atTop
        (nhds 0) := by
      simpa using tendsto_sixVertexLogRegularizationSchedule.mul_const K
    have hevValue : ∀ᶠ m : Nat in atTop, dist (value m) target < eta :=
      hvalue.eventually (Metric.ball_mem_nhds target heta)
    have hevK : ∀ᶠ m : Nat in atTop,
        sixVertexLogRegularizationSchedule m * K < eta / 3 := by
      have hz : 0 < eta / 3 := by positivity
      filter_upwards [hepsK.eventually (Metric.ball_mem_nhds 0 hz)]
        with m hm
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (mul_nonneg
          (sixVertexLogRegularizationSchedule_pos m).le hK)] at hm
      exact hm
    obtain ⟨m, hm⟩ := eventually_atTop.1 (hevValue.and hevK)
    have hm' := hm m le_rfl
    refine ⟨m, hm'.1, ?_⟩
    have hcut :=
      eventually_abs_sixVertexCanonicalEvenBulkLogDisplacement_sub_regularized_le
        hc (sixVertexLogRegularizationSchedule_pos m) s hM
    have htail : ∀ᶠ k : Nat in atTop,
        A / (sixVertexFourWidth (2 * s) k : Real) < eta / 3 := by
      have ht : Tendsto (fun k : Nat =>
          A / (sixVertexFourWidth (2 * s) k : Real)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop hwidth
      have hz : 0 < eta / 3 := by positivity
      filter_upwards [ht.eventually (Metric.ball_mem_nhds 0 hz)] with k hk
      have hN : 0 < (sixVertexFourWidth (2 * s) k : Real) := by
        exact_mod_cast sixVertexFourWidth_pos (2 * s) k
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (div_nonneg hA hN.le)] at hk
      exact hk
    filter_upwards [hcut, htail] with k hk hkTail
    rw [Real.dist_eq]
    have hfirst : A * (1 / (M : Real)) < eta / 3 := by
      simpa [A, M] using hM0
    have hthird :
        sixVertexLogRegularizationSchedule m *
            sixVertexCanonicalEvenOffsetLinearBound c hc s * Real.pi *
              (M : Real) ^ 4 / 16 < eta / 3 := by
      convert hm'.2 using 1 <;> dsimp [K] <;> ring
    have hbound :
        2 * Real.pi * sixVertexCanonicalEvenOffsetLinearBound c hc s *
              (1 / (M : Real) +
                1 / (sixVertexFourWidth (2 * s) k : Real)) +
            sixVertexLogRegularizationSchedule m *
              sixVertexCanonicalEvenOffsetLinearBound c hc s * Real.pi *
                (M : Real) ^ 4 / 16 < eta := by
      dsimp [A] at hkTail hfirst
      calc
        _ =
            (2 * Real.pi * sixVertexCanonicalEvenOffsetLinearBound c hc s *
              (1 / (M : Real))) +
            (2 * Real.pi * sixVertexCanonicalEvenOffsetLinearBound c hc s /
              (sixVertexFourWidth (2 * s) k : Real)) +
            sixVertexLogRegularizationSchedule m *
              sixVertexCanonicalEvenOffsetLinearBound c hc s * Real.pi *
                (M : Real) ^ 4 / 16 := by ring
        _ < eta := by linarith
    exact hk.trans_lt hbound
  rw [Metric.tendsto_atTop]
  intro eta heta
  obtain ⟨m, hmValue, hmClose⟩ := happrox (eta / 3) (by positivity)
  obtain ⟨Kclose, hKclose⟩ := eventually_atTop.1 hmClose
  have hregm := hreg m
  rw [Metric.tendsto_atTop] at hregm
  obtain ⟨Kreg, hKreg⟩ := hregm (eta / 3) (by positivity)
  refine ⟨max Kclose Kreg, ?_⟩
  intro k hk
  have hclose := hKclose k ((le_max_left _ _).trans hk)
  have hregk := hKreg k ((le_max_right _ _).trans hk)
  exact (dist_triangle4 (raw k) (reg m k) (value m) target).trans_lt
    (by linarith)

theorem eventually_sixVertexCanonicalFixedChargeCandidate_even_eq_density
    {c : Real} (hc : 2 < c) (s : Nat) :
    (fun k => sixVertexCanonicalFixedChargeBetheCandidateLogRatio hc
      (2 * s) k) =ᶠ[atTop]
      sixVertexCanonicalFixedEvenDensityCandidateLogRatio hc s := by
  filter_upwards
    [eventually_sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue_eq hc s]
      with k hk
  unfold sixVertexCanonicalFixedChargeBetheCandidateLogRatio
    sixVertexFixedChargeBetheEigenvalueValue
    sixVertexCanonicalFixedEvenDensityCandidateLogRatio
  rw [dif_pos (show Even (2 * s) by exact ⟨s, by omega⟩)]
  have hhalf : 2 * s / 2 = s := by omega
  rw [hhalf, <- hk]

theorem tendsto_sixVertexCanonicalFixedEvenDensityCandidateLogRatio
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (sixVertexCanonicalFixedEvenDensityCandidateLogRatio hc s) atTop
      (nhds (-((2 * s : Nat) : Real) *
        sixVertexAntiferroelectricGapRate
          (sixVertexAntiferroelectricLambda c))) := by
  have hbulk := tendsto_sixVertexCanonicalEvenBulkLogDisplacement hc s
  have hboundary :=
    tendsto_sum_sixVertexCanonicalEvenBoundaryLogObservable hc s
  have hcomb := (hbulk.sub hboundary).const_mul 2
  have hvalue :
      2 * ((2 * s : Real) / 2 *
            (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) -
              sixVertexAntiferroelectricGapRate
                (sixVertexAntiferroelectricLambda c)) -
          (s : Real) *
            Real.log (Real.cosh (sixVertexAntiferroelectricLambda c))) =
        -((2 * s : Nat) : Real) *
          sixVertexAntiferroelectricGapRate
            (sixVertexAntiferroelectricLambda c) := by
    push_cast
    ring
  rw [hvalue] at hcomb
  apply hcomb.congr'
  filter_upwards [] with k
  exact (sixVertexCanonicalFixedEvenDensityCandidateLogRatio_decomposition
    hc s k).symm

theorem sixVertexCanonicalFixedEvenCharge_matchesOffsetFourier
    {c : Real} (hc : 2 < c) (s : Nat) :
    SixVertexCanonicalFixedChargeBetheCandidateMatchesOffsetFourier hc
      (2 * s) := by
  let lam := sixVertexAntiferroelectricLambda c
  have hdensity :=
    tendsto_sixVertexCanonicalFixedEvenDensityCandidateLogRatio hc s
  have hcanonical : Tendsto
      (fun k => sixVertexCanonicalFixedChargeBetheCandidateLogRatio hc
        (2 * s) k) atTop
      (nhds (-((2 * s : Nat) : Real) *
        sixVertexAntiferroelectricGapRate lam)) :=
    hdensity.congr'
      (eventually_sixVertexCanonicalFixedChargeCandidate_even_eq_density
        hc s).symm
  unfold SixVertexCanonicalFixedChargeBetheCandidateMatchesOffsetFourier
  have hpartial := (sixVertexOffsetFourierPartialSum_tendsto
    (sixVertexAntiferroelectricLambda_pos hc)).const_mul
      ((2 * s : Nat) : Real)
  have hadd := hcanonical.add hpartial
  have hzero :
      -((2 * s : Nat) : Real) * sixVertexAntiferroelectricGapRate lam +
        ((2 * s : Nat) : Real) * sixVertexAntiferroelectricGapRate lam = 0 := by
    ring
  rw [hzero] at hadd
  simpa [lam] using hadd

end

end StatMech.FrontierD
