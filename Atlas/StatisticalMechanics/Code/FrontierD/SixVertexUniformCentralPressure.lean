/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Code.FrontierD.FKRectBalancedShareSpectralGapLogConcavity
import Code.FrontierD.SixVertexMarkedTraceParticleHole

open Finset Matrix Filter Topology

namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSectorTrace_particleHole_uniformPressure
    {N n : Nat} (hn : n <= N) (M : Nat) (c : Real) :
    Matrix.trace (sixVertexSectorTransfer N (N - n) c ^ M) =
      Matrix.trace (sixVertexSectorTransfer N n c ^ M) := by
  have hpoly := congrArg (Polynomial.eval (c - 2))
    (sixVertexShiftedSectorTracePolynomial_particleHole hn M)
  simpa [eval_sixVertexShiftedSectorTracePolynomial] using hpoly

theorem sixVertexCentralTrace_le_fixedWidthPartitionSum
    (N M : Nat) (hM : 0 < M)
    {c : Real} (hc : 0 < c) :
    Matrix.trace (sixVertexSectorTransfer N (N / 2) c ^ M) <=
      sixVertexFixedWidthPartitionSum N M c := by
  rw [sixVertexFixedWidthPartitionSum_eq_sum_sector_traces N M hM]
  let middle : Fin (N + 1) :=
    ⟨N / 2, Nat.lt_succ_of_le (Nat.div_le_self N 2)⟩
  change Matrix.trace
      (sixVertexSectorTransfer N middle.val c ^ M) <= _
  exact Finset.single_le_sum
    (s := Finset.univ)
    (fun sector (_ : sector ∈ (Finset.univ : Finset (Fin (N + 1)))) =>
      (sixVertexSector_trace_pow_pos (by omega) hc M).le)
    (Finset.mem_univ middle)

theorem sixVertexBalancedTraceShare_mem_Ioc
    (N M : Nat) (hM : 0 < M)
    {c : Real} (hc : 0 < c) :
    sixVertexBalancedTraceShare N M c ∈ Set.Ioc 0 1 := by
  have hcentral : 0 < Matrix.trace
      (sixVertexSectorTransfer N (N / 2) c ^ M) :=
    sixVertexSector_trace_pow_pos (Nat.div_le_self N 2) hc M
  have hfull : 0 < sixVertexFixedWidthPartitionSum N M c :=
    sixVertexFixedWidthPartitionSum_pos N M hM hc
  constructor
  · exact div_pos hcentral hfull
  · rw [sixVertexBalancedTraceShare, div_le_one hfull]
    exact sixVertexCentralTrace_le_fixedWidthPartitionSum N M hM hc


def SixVertexUniformHeightCentralTraceBound
    (N : Nat) (c : Real) : Prop :=
  exists C : Real, 0 < C ∧ forall M : Nat, 0 < M ->
    sixVertexFixedWidthPartitionSum N M c <=
      C * Matrix.trace (sixVertexSectorTransfer N (N / 2) c ^ M)


def SixVertexAllHeightCentralTraceMaximal (N : Nat) (c : Real) : Prop :=
  forall M n : Nat, 0 < M -> n <= N ->
    Matrix.trace (sixVertexSectorTransfer N n c ^ M) <=
      Matrix.trace (sixVertexSectorTransfer N (N / 2) c ^ M)

theorem sixVertexAllHeightCentralTraceMaximal_of_traceLogConcave
    (N : Nat) (hN : Even N) {c : Real} (hc : 0 < c)
    (hlc : SixVertexSectorTraceLogConcave N c) :
    SixVertexAllHeightCentralTraceMaximal N c := by
  intro M n hM hn
  let a : Nat -> Real := fun sector =>
    Matrix.trace (sixVertexSectorTransfer N sector c ^ M)
  have hpos : forall sector, sector <= N -> 0 < a sector := by
    intro sector hsector
    exact sixVertexSector_trace_pow_pos hsector hc M
  have hsym : forall sector, sector <= N ->
      a (N - sector) = a sector := by
    intro sector hsector
    exact sixVertexSectorTrace_particleHole_uniformPressure hsector M c
  have hlocal : forall sector, 0 < sector -> sector < N ->
      a (sector - 1) * a (sector + 1) <= a sector ^ 2 := by
    intro sector hsector0 hsectorN
    have h := hlc M sector hM hsector0 hsectorN
    rw [sixVertexSectorTraceProfile_eq (by omega),
      sixVertexSectorTraceProfile_eq (by omega),
      sixVertexSectorTraceProfile_eq (by omega)] at h
    exact h
  change a n <= a (N / 2)
  by_cases hnHalf : n <= N / 2
  · exact lowerHalf_le_middle_of_pos_logConcave_symmetric
      a N hN hpos hsym hlocal hnHalf
  · rw [← hsym n hn]
    apply lowerHalf_le_middle_of_pos_logConcave_symmetric
      a N hN hpos hsym hlocal
    obtain ⟨half, rfl⟩ := hN
    omega

theorem sixVertexUniformHeightCentralTraceBound_of_allHeightCentralTraceMaximal
    (N : Nat) {c : Real}
    (hmax : SixVertexAllHeightCentralTraceMaximal N c) :
    SixVertexUniformHeightCentralTraceBound N c := by
  refine ⟨(N + 1 : Nat), by positivity, ?_⟩
  intro M hM
  rw [sixVertexFixedWidthPartitionSum_eq_sum_sector_traces N M hM]
  calc
    _ <= ∑ _sector : Fin (N + 1),
        Matrix.trace (sixVertexSectorTransfer N (N / 2) c ^ M) := by
      apply Finset.sum_le_sum
      intro sector _
      exact hmax M sector.val hM (by omega)
    _ = _ := by simp

theorem sixVertexUniformHeightCentralTraceBound_of_traceLogConcave
    (N : Nat) (hN : Even N) {c : Real} (hc : 0 < c)
    (hlc : SixVertexSectorTraceLogConcave N c) :
    SixVertexUniformHeightCentralTraceBound N c :=
  sixVertexUniformHeightCentralTraceBound_of_allHeightCentralTraceMaximal N
    (sixVertexAllHeightCentralTraceMaximal_of_traceLogConcave
      N hN hc hlc)


def SixVertexPositiveEvenHeightCentralTraceMaximal
    (N : Nat) (c : Real) : Prop :=
  forall M n : Nat, n <= N ->
    Matrix.trace (sixVertexSectorTransfer N n c ^
        sixVertexPositiveEvenHeight M) <=
      Matrix.trace (sixVertexSectorTransfer N (N / 2) c ^
        sixVertexPositiveEvenHeight M)

theorem
    sixVertexPositiveEvenHeightCentralTraceMaximal_of_traceLogConcave
    (N : Nat) (hN : Even N) {c : Real} (hc : 0 < c)
    (hlc : SixVertexSectorPositiveEvenTraceLogConcave N c) :
    SixVertexPositiveEvenHeightCentralTraceMaximal N c := by
  intro M n hn
  let a : Nat -> Real := fun sector => Matrix.trace
    (sixVertexSectorTransfer N sector c ^ sixVertexPositiveEvenHeight M)
  have hpos : forall sector, sector <= N -> 0 < a sector := by
    intro sector hsector
    exact sixVertexSector_trace_pow_pos hsector hc _
  have hsym : forall sector, sector <= N ->
      a (N - sector) = a sector := by
    intro sector hsector
    exact sixVertexSectorTrace_particleHole_uniformPressure hsector _ c
  have hlocal : forall sector, 0 < sector -> sector < N ->
      a (sector - 1) * a (sector + 1) <= a sector ^ 2 := by
    intro sector hsector0 hsectorN
    exact hlc M sector hsector0 hsectorN
  change a n <= a (N / 2)
  by_cases hnHalf : n <= N / 2
  · exact lowerHalf_le_middle_of_pos_logConcave_symmetric
      a N hN hpos hsym hlocal hnHalf
  · rw [← hsym n hn]
    apply lowerHalf_le_middle_of_pos_logConcave_symmetric
      a N hN hpos hsym hlocal
    obtain ⟨half, rfl⟩ := hN
    omega



theorem
    sixVertexPositiveEvenHeight_full_le_card_mul_central_of_traceLogConcave
    (N : Nat) (hN : Even N) {c : Real} (hc : 0 < c)
    (hlc : SixVertexSectorPositiveEvenTraceLogConcave N c)
    (M : Nat) :
    sixVertexFixedWidthPartitionSum N (sixVertexPositiveEvenHeight M) c <=
      (N + 1 : Nat) * Matrix.trace
        (sixVertexSectorTransfer N (N / 2) c ^
          sixVertexPositiveEvenHeight M) := by
  have hmax :=
    sixVertexPositiveEvenHeightCentralTraceMaximal_of_traceLogConcave
      N hN hc hlc
  rw [sixVertexFixedWidthPartitionSum_eq_sum_sector_traces N
    (sixVertexPositiveEvenHeight M) (sixVertexPositiveEvenHeight_pos M)]
  calc
    _ <= ∑ _sector : Fin (N + 1), Matrix.trace
        (sixVertexSectorTransfer N (N / 2) c ^
          sixVertexPositiveEvenHeight M) := by
      apply Finset.sum_le_sum
      intro sector _
      exact hmax M sector.val (by omega)
    _ = _ := by simp

theorem sixVertexWidthTopEigenvalue_eq_halfFilled_of_uniformHeightCentralTraceBound
    (N : Nat) (hN : Even N) {c : Real} (hc : 0 < c)
    (hbound : SixVertexUniformHeightCentralTraceBound N c) :
    sixVertexWidthTopEigenvalue N c =
      sixVertexSectorTopEigenvalue N (N / 2)
        (Nat.div_le_self N 2) c := by
  obtain ⟨C, hC, hbound⟩ := hbound
  let gap : Nat -> Real := fun M =>
    -Real.log (sixVertexBalancedTraceShare N M c) / (M : Real)
  have hgapLimit : Tendsto gap atTop
      (nhds (Real.log (sixVertexWidthTopEigenvalue N c) -
        Real.log (sixVertexSectorTopEigenvalue N (N / 2)
          (Nat.div_le_self N 2) c))) := by
    simpa [gap, sixVertexLambda] using
      sixVertexBalancedTraceShare_negLog_div_height_tendsto N hN hc
  have hgapZero : Tendsto gap atTop (nhds 0) := by
    apply squeeze_zero
    · intro M
      by_cases hM : 0 < M
      · have hshare := sixVertexBalancedTraceShare_mem_Ioc N M hM hc
        exact div_nonneg (neg_nonneg.mpr
          (Real.log_nonpos hshare.1.le hshare.2)) (by positivity)
      · simp [gap, Nat.eq_zero_of_not_pos hM]
    · intro M
      by_cases hM : 0 < M
      · have hcentral : 0 < Matrix.trace
          (sixVertexSectorTransfer N (N / 2) c ^ M) :=
          sixVertexSector_trace_pow_pos (Nat.div_le_self N 2) hc M
        have hfull : 0 < sixVertexFixedWidthPartitionSum N M c :=
          sixVertexFixedWidthPartitionSum_pos N M hM hc
        have hratio : (1 : Real) / C <=
            sixVertexBalancedTraceShare N M c := by
          rw [sixVertexBalancedTraceShare, le_div_iff₀ hfull]
          have h := hbound M hM
          rw [div_mul_eq_mul_div, div_le_iff₀ hC]
          simpa [mul_comm, mul_left_comm, mul_assoc] using h
        have hlog : -Real.log (sixVertexBalancedTraceShare N M c) <=
            Real.log C := by
          have hratioPos : 0 < (1 : Real) / C := by positivity
          have hmono := Real.log_le_log hratioPos hratio
          rw [Real.log_div (by norm_num : (1 : Real) ≠ 0) hC.ne',
            Real.log_one] at hmono
          linarith
        exact div_le_div_of_nonneg_right hlog (by positivity)
      · simp [gap, Nat.eq_zero_of_not_pos hM]
    · simpa using
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
          Tendsto (fun M : Nat => Real.log C / (M : Real)) atTop (nhds 0))
  have hgapEq :
      Real.log (sixVertexWidthTopEigenvalue N c) -
          Real.log (sixVertexSectorTopEigenvalue N (N / 2)
            (Nat.div_le_self N 2) c) = 0 :=
    tendsto_nhds_unique hgapLimit hgapZero
  have htop : 0 < sixVertexWidthTopEigenvalue N c :=
    sixVertexWidthTopEigenvalue_pos N hc
  have hcentral : 0 < sixVertexSectorTopEigenvalue N (N / 2)
      (Nat.div_le_self N 2) c :=
    sixVertexSectorTopEigenvalue_pos (Nat.div_le_self N 2) hc
  have hlog : Real.log (sixVertexWidthTopEigenvalue N c) =
      Real.log (sixVertexSectorTopEigenvalue N (N / 2)
        (Nat.div_le_self N 2) c) := by
    linarith
  calc
    sixVertexWidthTopEigenvalue N c =
        Real.exp (Real.log (sixVertexWidthTopEigenvalue N c)) :=
      (Real.exp_log htop).symm
    _ = Real.exp (Real.log (sixVertexSectorTopEigenvalue N (N / 2)
          (Nat.div_le_self N 2) c)) := congrArg Real.exp hlog
    _ = sixVertexSectorTopEigenvalue N (N / 2)
          (Nat.div_le_self N 2) c := Real.exp_log hcentral


def SixVertexCanonicalUniformHeightCentralTraceBound (q : Real) : Prop :=
  forall r k : Nat,
    SixVertexUniformHeightCentralTraceBound
      (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)

theorem fkRectBalancedShareSpectralGap_eq_zero_of_uniformHeightCentralTraceBound
    {q : Real} (hq : 4 < q) (r k : Nat)
    (hbound : SixVertexUniformHeightCentralTraceBound
      (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)) :
    fkRectBalancedShareSpectralGap q r k = 0 := by
  have hc : 0 < fkQgt4SixVertexWeight q := by
    linarith [two_lt_fkQgt4SixVertexWeight hq]
  have htop :=
    sixVertexWidthTopEigenvalue_eq_halfFilled_of_uniformHeightCentralTraceBound
      (sixVertexFourWidth r (k + 1))
      (sixVertexFourWidth_even r (k + 1)) hc hbound
  unfold fkRectBalancedShareSpectralGap
  rw [htop]
  simp [sixVertexLambda]

theorem tendsto_fkRectBalancedShareSpectralGap_zero_of_uniformHeightCentralTraceBound
    {q : Real} (hq : 4 < q) (r : Nat)
    (hbound : SixVertexCanonicalUniformHeightCentralTraceBound q) :
    Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0) := by
  apply (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [] with k
  exact fkRectBalancedShareSpectralGap_eq_zero_of_uniformHeightCentralTraceBound
    hq r k (hbound r k)

theorem
    tendsto_fkRectBalancedNormalizationRate_zero_of_crossingFloor_uniformTrace
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (r : Nat)
    (hbound : SixVertexCanonicalUniformHeightCentralTraceBound q) :
    Tendsto (fkRectBalancedSectorNormalizationVerticalRate hq r)
      atTop (nhds 0) := by
  apply
    tendsto_fkRectBalancedSectorNormalizationVerticalRate_zero_of_freePIMS_and_spectralGap
      hq r
  · exact
      fkQgt4CriticalFree_percolation_zero_of_evenTwoByOneCrossingFloor
        hq hhard hcross
  · exact
      tendsto_fkRectBalancedShareSpectralGap_zero_of_uniformHeightCentralTraceBound
        hq r hbound

theorem
    fkQgt4_windingBridge_of_crossingFloor_uniformCentralTrace
    {q hardFloor : Real} (hq : 4 < q)
    (hhard : 0 < hardFloor)
    (hcross : forall scale k : Nat,
      0 < scale -> Even scale ->
      12 * scale + 2 < 2 * (k + 3) ->
      ∀ᶠ blocks in atTop,
        hardFloor <=
          fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedRectangleHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale
              0 (2 * (scale : Int)) 0 scale))
    (hbound : SixVertexCanonicalUniformHeightCentralTraceBound q) :
    FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q) := by
  apply
    fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_boundaryIncidence_spectralGap_unconditional
      hq hhard hcross
  intro r _hr
  exact
    tendsto_fkRectBalancedShareSpectralGap_zero_of_uniformHeightCentralTraceBound
      hq r hbound

end

end StatMech.FrontierD
