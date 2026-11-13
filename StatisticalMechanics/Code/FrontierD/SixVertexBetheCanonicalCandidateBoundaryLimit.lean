/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheCanonicalCandidateDecomposition
import Code.FrontierD.SixVertexBetheOffsetLogFourier





namespace StatMech.FrontierD

open Filter Topology

noncomputable section

theorem continuousAt_sixVertexBetheLogObservable_pi
    {c : Real} (hc : 2 < c) :
    ContinuousAt (sixVertexBetheLogObservable c) Real.pi := by
  have hp : ContinuousAt (fun p : Real => (p : Complex)) Real.pi :=
    Complex.continuous_ofReal.continuousAt
  have harg : ContinuousAt
      (fun p : Real => Complex.I * (p : Complex)) Real.pi :=
    continuousAt_const.mul hp
  have hexp : ContinuousAt
      (fun p : Real => Complex.exp (Complex.I * (p : Complex))) Real.pi := by
    simpa [Function.comp_def] using
      Complex.continuous_exp.continuousAt.comp harg
  have hden :
      (1 : Complex) - Complex.exp (Complex.I * (Real.pi : Complex)) ≠ 0 := by
    rw [mul_comm, Complex.exp_pi_mul_I]
    norm_num
  have hM : ContinuousAt (fun p : Real =>
      (1 : Complex) - (c : Complex) ^ 2 /
        (1 - Complex.exp (Complex.I * (p : Complex)))) Real.pi :=
    continuousAt_const.sub (continuousAt_const.div
      (continuousAt_const.sub hexp) hden)
  unfold sixVertexBetheLogObservable sixVertexBetheM sixVertexBethePhase
  apply (Real.continuousAt_log ?_).comp
  · exact hM.norm
  · apply norm_ne_zero_iff.mpr
    exact sixVertexBetheM_phase_ne_zero hc Real.pi

theorem sixVertexBetheLogObservable_pi
    {c : Real} (hc : 2 < c) :
    sixVertexBetheLogObservable c Real.pi =
      Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) := by
  have hp : sixVertexBethePhase Real.pi ≠ 1 := by
    unfold sixVertexBethePhase
    rw [mul_comm, Complex.exp_pi_mul_I]
    norm_num
  unfold sixVertexBetheLogObservable
  rw [sixVertexBetheM_log_norm_eq_logNumerator_sub_logDenominator hc hp]
  unfold sixVertexBetheLogNumerator sixVertexBetheLogDenominator
  rw [Real.cos_pi]
  have hd : 0 < c ^ 2 - 2 := by nlinarith [sq_nonneg (c - 2)]
  have hcosh := sixVertex_cosh_antiferroelectricLambda hc
  rw [show (c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * -1 =
      (c ^ 2 - 2) ^ 2 by ring]
  rw [show 2 - 2 * -1 = (2 : Real) ^ 2 by norm_num]
  rw [Real.log_pow, Real.log_pow, hcosh]
  rw [Real.log_div hd.ne' (by norm_num : (2 : Real) ≠ 0)]
  ring

private theorem tendsto_canonicalBoundaryMajorant
    {c : Real} (hc : 2 < c) (r A : Nat) :
    Tendsto (fun k => (A : Real) /
      ((sixVertexFourWidth 0 (r + k) : Real) *
        sixVertexCanonicalHalfDensityFloor hc)) atTop (nhds 0) := by
  have hshift : Tendsto (fun k : Nat => r + k) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat r
  have hwidthNat : Tendsto
      (fun k : Nat => sixVertexFourWidth 0 (r + k)) atTop atTop := by
    have hbase : Tendsto (sixVertexFourWidth 0) atTop atTop :=
      (strictMono_nat_of_lt_succ (fun n => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
    exact hbase.comp hshift
  have hwidth : Tendsto
      (fun k : Nat => (sixVertexFourWidth 0 (r + k) : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hwidthNat
  have hden := hwidth.atTop_mul_const
    (sixVertexCanonicalHalfDensityFloor_pos hc)
  exact tendsto_const_nhds.div_atTop hden

theorem tendsto_sixVertexCanonicalEvenBoundaryHalfRoot
    {c : Real} (hc : 2 < c) (s : Nat) (i : Fin s) :
    Tendsto (fun k => sixVertexCanonicalEvenBoundaryHalfRoot hc s k i)
      atTop (nhds Real.pi) := by
  let lower := sixVertexCanonicalHalfDensityFloor hc
  have hshift : Tendsto (fun k : Nat => 2 * s + k) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat (2 * s)
  have hdensity := hshift.eventually
    (eventually_sixVertexCanonicalHalfDensityFloor_le hc)
  have hmajor : Tendsto (fun k => (s : Real) /
      ((sixVertexFourWidth 0 (2 * s + k) : Real) * lower))
      atTop (nhds 0) :=
    tendsto_canonicalBoundaryMajorant hc (2 * s) s
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun k => norm_nonneg _)) ?_ hmajor
  filter_upwards [hdensity] with k hk
  rw [Real.norm_eq_abs]
  exact abs_sixVertexCanonicalEvenBoundaryHalfRoot_sub_pi_le
    hc s k (sixVertexCanonicalHalfDensityFloor_pos hc) hk i

theorem tendsto_sixVertexCanonicalOddBoundaryHalfRoot
    {c : Real} (hc : 2 < c) (s : Nat) (i : Fin (s + 1)) :
    Tendsto (fun k => sixVertexCanonicalOddBoundaryHalfRoot hc s k i)
      atTop (nhds Real.pi) := by
  let lower := sixVertexCanonicalHalfDensityFloor hc
  have hshift : Tendsto (fun k : Nat => 2 * s + 1 + k) atTop atTop := by
    simpa [Nat.add_comm, Nat.add_assoc] using
      tendsto_add_atTop_nat (2 * s + 1)
  have hdensity := hshift.eventually
    (eventually_sixVertexCanonicalHalfDensityFloor_le hc)
  have hmajor : Tendsto (fun k => (s + 1 : Real) /
      ((sixVertexFourWidth 0 (2 * s + 1 + k) : Real) * lower))
      atTop (nhds 0) :=
    by
      simpa [lower, Nat.cast_add, Nat.cast_one] using
        tendsto_canonicalBoundaryMajorant hc (2 * s + 1) (s + 1)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun k => norm_nonneg _)) ?_ hmajor
  filter_upwards [hdensity] with k hk
  rw [Real.norm_eq_abs]
  exact abs_sixVertexCanonicalOddBoundaryHalfRoot_sub_pi_le
    hc s k (sixVertexCanonicalHalfDensityFloor_pos hc) hk i

theorem tendsto_sum_sixVertexCanonicalEvenBoundaryLogObservable
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (fun k => ∑ i : Fin s, sixVertexBetheLogObservable c
        (sixVertexCanonicalEvenBoundaryHalfRoot hc s k i)) atTop
      (nhds ((s : Real) *
        Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)))) := by
  have h := tendsto_finsetSum Finset.univ (fun i _ =>
    (continuousAt_sixVertexBetheLogObservable_pi hc).tendsto.comp
      (tendsto_sixVertexCanonicalEvenBoundaryHalfRoot hc s i))
  simpa [sixVertexBetheLogObservable_pi hc] using h

theorem tendsto_sum_sixVertexCanonicalOddBoundaryLogObservable
    {c : Real} (hc : 2 < c) (s : Nat) :
    Tendsto (fun k => ∑ i : Fin (s + 1), sixVertexBetheLogObservable c
        (sixVertexCanonicalOddBoundaryHalfRoot hc s k i)) atTop
      (nhds ((s + 1 : Real) *
        Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)))) := by
  have h := tendsto_finsetSum Finset.univ (fun i _ =>
    (continuousAt_sixVertexBetheLogObservable_pi hc).tendsto.comp
      (tendsto_sixVertexCanonicalOddBoundaryHalfRoot hc s i))
  simpa [sixVertexBetheLogObservable_pi hc] using h

end

end StatMech.FrontierD
