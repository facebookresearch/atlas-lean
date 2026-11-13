/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Sharpness.MeanfieldIsingState

open MeasureTheory Real Set Filter Topology
open scoped BigOperators Interval

namespace StatMech
namespace Sharpness

open StatMech.Lattice StatMech.Percolation StatMech.Ising




noncomputable def sctOriginMagBetaDeriv (d n : ℕ) (h beta : ℝ) : ℝ :=
  isingExpectation (sctBoxGraph d n) beta h
      (fun s => spin s (sctBoxOrigin d n) * negHam (sctBoxGraph d n) h s) -
    sctOriginMag d beta h n *
      isingExpectation (sctBoxGraph d n) beta h (negHam (sctBoxGraph d n) h)


theorem hasDerivAt_sctOriginMag_beta (d n : ℕ) (h beta : ℝ) :
    HasDerivAt (fun b => sctOriginMag d b h n)
      (sctOriginMagBetaDeriv d n h beta) beta := by
  exact hasDerivAt_expectation_beta (sctBoxGraph d n) beta h
    (fun s => spin s (sctBoxOrigin d n))


noncomputable def sctOriginMagSqBetaDeriv (d n : ℕ) (h beta : ℝ) : ℝ :=
  2 * sctOriginMag d beta h n * sctOriginMagBetaDeriv d n h beta

theorem hasDerivAt_sctOriginMag_sq_beta (d n : ℕ) (h beta : ℝ) :
    HasDerivAt (fun b => (sctOriginMag d b h n) ^ 2)
      (sctOriginMagSqBetaDeriv d n h beta) beta := by
  convert (hasDerivAt_sctOriginMag_beta d n h beta).pow 2 using 1 <;>
    simp [sctOriginMagSqBetaDeriv] <;> ring

@[simp]
theorem deriv_sctOriginMag_sq_beta (d n : ℕ) (h beta : ℝ) :
    deriv (fun b => (sctOriginMag d b h n) ^ 2) beta =
      sctOriginMagSqBetaDeriv d n h beta :=
  (hasDerivAt_sctOriginMag_sq_beta d n h beta).deriv


noncomputable def sctMeanfieldG (d n : ℕ) (h beta : ℝ) : ℝ :=
  beta ^ 2 * (1 - (sctOriginMag d beta h n) ^ 2)


noncomputable def sctMeanfieldGDeriv (d n : ℕ) (h beta : ℝ) : ℝ :=
  2 * beta * (1 - (sctOriginMag d beta h n) ^ 2) -
    beta ^ 2 * sctOriginMagSqBetaDeriv d n h beta

theorem hasDerivAt_sctMeanfieldG (d n : ℕ) (h beta : ℝ) :
    HasDerivAt (sctMeanfieldG d n h)
      (sctMeanfieldGDeriv d n h beta) beta := by
  have hp : HasDerivAt (fun b : ℝ => b ^ 2) (2 * beta) beta := by
    simpa using hasDerivAt_pow 2 beta
  have hm := hasDerivAt_sctOriginMag_sq_beta d n h beta
  have hs : HasDerivAt (fun b => 1 - (sctOriginMag d b h n) ^ 2)
      (-sctOriginMagSqBetaDeriv d n h beta) beta := by
    simpa using (hasDerivAt_const beta (1 : ℝ)).sub hm
  convert hp.mul hs using 1 <;> simp [sctMeanfieldG, sctMeanfieldGDeriv] <;> ring



theorem continuous_isingExpectation_beta
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : ℝ)
    (f : ConfigSpace V → ℝ) :
    Continuous (fun beta => isingExpectation G beta h f) := by
  rw [continuous_iff_continuousAt]
  intro beta
  exact (hasDerivAt_expectation_beta G beta h f).continuousAt

theorem continuous_sctBoxMag_beta (d n : ℕ) (h : ℝ) (x : sctBox d n) :
    Continuous (fun beta => sctBoxMag d beta h n x) :=
  continuous_isingExpectation_beta (sctBoxGraph d n) h (fun s => spin s x)

theorem continuous_sctOriginMag_beta (d n : ℕ) (h : ℝ) :
    Continuous (fun beta => sctOriginMag d beta h n) :=
  continuous_sctBoxMag_beta d n h (sctBoxOrigin d n)

theorem continuous_sctOriginMagBetaDeriv (d n : ℕ) (h : ℝ) :
    Continuous (sctOriginMagBetaDeriv d n h) := by
  unfold sctOriginMagBetaDeriv
  exact
    (continuous_isingExpectation_beta (sctBoxGraph d n) h
      (fun s => spin s (sctBoxOrigin d n) * negHam (sctBoxGraph d n) h s)).sub
    ((continuous_sctOriginMag_beta d n h).mul
      (continuous_isingExpectation_beta (sctBoxGraph d n) h
        (negHam (sctBoxGraph d n) h)))

theorem continuous_sctOriginMagSqBetaDeriv (d n : ℕ) (h : ℝ) :
    Continuous (sctOriginMagSqBetaDeriv d n h) := by
  unfold sctOriginMagSqBetaDeriv
  exact (continuous_const.mul (continuous_sctOriginMag_beta d n h)).mul
    (continuous_sctOriginMagBetaDeriv d n h)

theorem continuous_sctMeanfieldGDeriv (d n : ℕ) (h : ℝ) :
    Continuous (sctMeanfieldGDeriv d n h) := by
  unfold sctMeanfieldGDeriv
  exact ((continuous_const.mul continuous_id).mul
      (continuous_const.sub ((continuous_sctOriginMag_beta d n h).pow 2))).sub
    (((continuous_id.pow 2)).mul (continuous_sctOriginMagSqBetaDeriv d n h))




theorem continuousOn_sctLatticeC_beta (d n : ℕ) (h : ℝ) (hh : 0 < h)
    {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun beta => sctLatticeC d beta h n) (Icc a b) := by
  unfold sctLatticeC sct_cInfDep
  apply ContinuousOn.finset_inf'_apply (sctBoxSites_nonempty d n)
  intro x hx
  apply ContinuousOn.div
  · exact (continuous_sctOriginMag_beta d n h).continuousOn
  · exact (continuous_sctBoxMag_beta d n h x).continuousOn
  · intro beta hbeta
    exact (sctBoxMag_pos d beta h (ha.trans_le hbeta.1) hh n x).ne'

theorem continuous_sctBoxCovariance_beta (d n : ℕ) (h : ℝ) (x : sctBox d n) :
    Continuous (fun beta => sctBoxCovariance d beta h n x) := by
  unfold sctBoxCovariance sctOriginMag sctBoxMag
  exact
    (continuous_isingExpectation_beta (sctBoxGraph d n) h
      (fun s => spin s (sctBoxOrigin d n) * spin s x)).sub
    ((continuous_isingExpectation_beta (sctBoxGraph d n) h
      (fun s => spin s (sctBoxOrigin d n))).mul
      (continuous_isingExpectation_beta (sctBoxGraph d n) h
        (fun s => spin s x)))

theorem continuous_sctBoundaryCovarianceError_beta (d n : ℕ) (h : ℝ) :
    Continuous (fun beta => sctBoundaryCovarianceError d beta h n) := by
  unfold sctBoundaryCovarianceError
  exact continuous_finset_sum Finset.univ (fun x _ =>
    continuous_const.mul (continuous_sctBoxCovariance_beta d n h x))






noncomputable def sctMeanfieldIntegratedError
    (d n : ℕ) (h beta : ℝ) : ℝ :=
  2 * beta * (1 - sctLatticeC d beta h n) *
      (1 - (sctOriginMag d beta h n) ^ 2) +
    2 * beta ^ 2 * sctLatticeC d beta h n *
      sctBoundaryCovarianceError d beta h n

theorem continuousOn_sctMeanfieldIntegratedError
    (d n : ℕ) (h : ℝ) (hh : 0 < h) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (sctMeanfieldIntegratedError d n h) (Icc a b) := by
  unfold sctMeanfieldIntegratedError
  exact ((((continuousOn_const.mul continuousOn_id).mul
      (continuousOn_const.sub (continuousOn_sctLatticeC_beta d n h hh ha))).mul
        (continuousOn_const.sub
          ((continuous_sctOriginMag_beta d n h).continuousOn.pow 2))).add
    ((((continuousOn_const.mul (continuousOn_id.pow 2)).mul
      (continuousOn_sctLatticeC_beta d n h hh ha)).mul
        (continuous_sctBoundaryCovarianceError_beta d n h).continuousOn)))




theorem sctMeanfieldGDeriv_le_integratedError
    {d n : ℕ} (beta h : ℝ) (hn : 1 ≤ n)
    (hbdd : BddAbove (tildeBetaCIsingSet d))
    (habove : tildeBetaCIsing d < beta) (hh : 0 < h) :
    sctMeanfieldGDeriv d n h beta ≤
      sctMeanfieldIntegratedError d n h beta := by
  have hzero : (0 : ℝ) ∈ tildeBetaCIsingSet d := by
    refine ⟨le_rfl, {Percolation.origin d}, by simp, ?_⟩
    simp [phiIsing]
  have hcrit0 : 0 ≤ tildeBetaCIsing d := by
    unfold tildeBetaCIsing
    exact le_csSup hbdd hzero
  have hbeta : 0 < beta := lt_of_le_of_lt hcrit0 habove
  have hphi : ∀ S : Finset (Site d), Percolation.origin d ∈ S ->
      1 ≤ phiIsing d beta S :=
    si4_phiIsing_ge_one_above_tildeBc d beta hbeta.le hbdd habove
  have hfin := sct_finite_meanfield_inequality_concrete beta h 1 hn hbeta hh hphi
  rw [deriv_sctOriginMag_sq_beta] at hfin
  simp only [one_mul] at hfin
  have hmul := mul_le_mul_of_nonneg_left hfin (sq_nonneg beta)
  have hcancel :
      beta ^ 2 *
          (2 * sctLatticeC d beta h n *
            ((1 / beta) *
                (1 - (sctOriginMag d beta h n) ^ 2) -
              sctBoundaryCovarianceError d beta h n)) =
        2 * beta * sctLatticeC d beta h n *
            (1 - (sctOriginMag d beta h n) ^ 2) -
          2 * beta ^ 2 * sctLatticeC d beta h n *
            sctBoundaryCovarianceError d beta h n := by
    field_simp [hbeta.ne']
    <;> ring
  rw [hcancel] at hmul
  unfold sctMeanfieldGDeriv sctMeanfieldIntegratedError
  linarith


theorem sctMeanfieldG_sub_le_integral_error
    {d n : ℕ} {a b h : ℝ} (hn : 1 ≤ n) (hab : a ≤ b)
    (ha : 0 < a) (hh : 0 < h)
    (hbdd : BddAbove (tildeBetaCIsingSet d))
    (hcrit : tildeBetaCIsing d < a) :
    sctMeanfieldG d n h b - sctMeanfieldG d n h a ≤
      ∫ gamma in a..b, sctMeanfieldIntegratedError d n h gamma := by
  have hftc :
      (∫ gamma in a..b, sctMeanfieldGDeriv d n h gamma) =
        sctMeanfieldG d n h b - sctMeanfieldG d n h a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro gamma hgamma
      exact hasDerivAt_sctMeanfieldG d n h gamma
    · exact (continuous_sctMeanfieldGDeriv d n h).intervalIntegrable a b
  rw [← hftc]
  apply intervalIntegral.integral_mono_on hab
  · exact (continuous_sctMeanfieldGDeriv d n h).intervalIntegrable a b
  · apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using
      (continuousOn_sctMeanfieldIntegratedError d n h hh ha)
  · intro gamma hgamma
    exact sctMeanfieldGDeriv_le_integratedError gamma h hn hbdd
      (hcrit.trans_le hgamma.1) hh






theorem sctBoundaryCovarianceError_le_uniform
    {d n : ℕ} (beta h : ℝ) (hn : 1 ≤ n)
    (hbeta : 0 < beta) (hh : 0 < h) :
    sctBoundaryCovarianceError d beta h n ≤
      (2 * d : ℝ) / (beta * h) := by
  have houter := sctBoundaryCovarianceError_le_outer d beta h
    hbeta.le hh.le n hn
  have hann := sctOuterCovarianceSum_le_magDiff d beta h hbeta hh n
  have hcoef : (0 : ℝ) ≤ (2 * d : ℝ) := by positivity
  have hden : 0 < beta * h := mul_pos hbeta hh
  have hm0 : 0 ≤ sctOriginMag d beta h (n - 1) :=
    (sctOriginMag_pos d beta h hbeta hh (n - 1)).le
  have hm1 : sctOriginMag d beta h n ≤ 1 :=
    sctOriginMag_le_one d beta h n
  calc
    sctBoundaryCovarianceError d beta h n
        ≤ (2 * d : ℝ) * sctOuterCovarianceSum d beta h n := houter
    _ ≤ (2 * d : ℝ) *
        ((sctOriginMag d beta h n - sctOriginMag d beta h (n - 1)) /
          (beta * h)) := mul_le_mul_of_nonneg_left hann hcoef
    _ ≤ (2 * d : ℝ) * (1 / (beta * h)) := by
      apply mul_le_mul_of_nonneg_left _ hcoef
      exact div_le_div_of_nonneg_right (by linarith) hden.le
    _ = (2 * d : ℝ) / (beta * h) := by ring



theorem sctMeanfieldIntegratedError_tendsto_zero
    (d : ℕ) (beta h : ℝ) (hbeta : 0 < beta) (hh : 0 < h) :
    Tendsto
      (fun k : ℕ => sctMeanfieldIntegratedError d (k + 1) h beta)
      atTop (nhds 0) := by
  have hc := (sctLatticeC_tendsto_one d beta h hbeta hh).comp
    (tendsto_add_atTop_nat 1)
  have hm := (sctOriginMag_tendsto_iSup d beta h hbeta.le hh.le).comp
    (tendsto_add_atTop_nat 1)
  have heps := (sctBoundaryCovarianceError_tendsto_zero d beta h hbeta hh).comp
    (tendsto_add_atTop_nat 1)
  have hfirst : Tendsto
      (fun k : ℕ =>
        2 * beta * (1 - sctLatticeC d beta h (k + 1)) *
          (1 - (sctOriginMag d beta h (k + 1)) ^ 2))
      atTop (nhds 0) := by
    convert ((tendsto_const_nhds.mul (tendsto_const_nhds.sub hc)).mul
      (tendsto_const_nhds.sub (hm.pow 2))) using 1 <;> simp
  have hsecond : Tendsto
      (fun k : ℕ =>
        2 * beta ^ 2 * sctLatticeC d beta h (k + 1) *
          sctBoundaryCovarianceError d beta h (k + 1))
      atTop (nhds 0) := by
    convert ((tendsto_const_nhds.mul hc).mul heps) using 1 <;> simp
  simpa only [sctMeanfieldIntegratedError, zero_add] using hfirst.add hsecond



theorem norm_sctMeanfieldIntegratedError_le
    {d n : ℕ} {a b h beta : ℝ} (hn : 1 ≤ n)
    (hab : a ≤ beta) (hbetab : beta ≤ b) (ha : 0 < a) (hh : 0 < h) :
    ‖sctMeanfieldIntegratedError d n h beta‖ ≤
      2 * b + 2 * b ^ 2 * ((2 * d : ℝ) / (a * h)) := by
  have hbeta : 0 < beta := ha.trans_le hab
  have hb : 0 < b := hbeta.trans_le hbetab
  have hc0 := sctLatticeC_nonneg beta h hbeta hh (d := d) (n := n)
  have hc1 := sctLatticeC_le_one d beta h hbeta hh n
  have hm0 := (sctOriginMag_pos d beta h hbeta hh n).le
  have hm1 := sctOriginMag_le_one d beta h n
  have he0 := sctBoundaryCovarianceError_nonneg d beta h hbeta.le hh.le n
  have he1 := sctBoundaryCovarianceError_le_uniform
    (d := d) (n := n) beta h hn hbeta hh
  have hdenA : 0 < a * h := mul_pos ha hh
  have hdenB : 0 < beta * h := mul_pos hbeta hh
  have hdiv : (2 * d : ℝ) / (beta * h) ≤ (2 * d : ℝ) / (a * h) := by
    apply div_le_div_of_nonneg_left (by positivity) hdenA
    exact mul_le_mul_of_nonneg_right hab hh.le
  have he : sctBoundaryCovarianceError d beta h n ≤
      (2 * d : ℝ) / (a * h) := he1.trans hdiv
  have hu0 : 0 ≤ 1 - (sctOriginMag d beta h n) ^ 2 := by
    nlinarith [sq_nonneg (sctOriginMag d beta h n)]
  have hu1 : 1 - (sctOriginMag d beta h n) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (sctOriginMag d beta h n)]
  have herr0 : 0 ≤ sctMeanfieldIntegratedError d n h beta := by
    unfold sctMeanfieldIntegratedError
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg herr0]
  unfold sctMeanfieldIntegratedError
  have hfirst :
      2 * beta * (1 - sctLatticeC d beta h n) *
          (1 - (sctOriginMag d beta h n) ^ 2) ≤ 2 * b := by
    have hcsub0 : 0 ≤ 1 - sctLatticeC d beta h n := sub_nonneg.mpr hc1
    have hcsub1 : 1 - sctLatticeC d beta h n ≤ 1 := by linarith
    have h2beta : 2 * beta ≤ 2 * b := by linarith
    calc
      2 * beta * (1 - sctLatticeC d beta h n) *
          (1 - (sctOriginMag d beta h n) ^ 2)
          ≤ 2 * b * (1 - sctLatticeC d beta h n) *
              (1 - (sctOriginMag d beta h n) ^ 2) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right h2beta hcsub0) hu0
      _ ≤ 2 * b * 1 * (1 - (sctOriginMag d beta h n) ^ 2) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcsub1 (by positivity)) hu0
      _ ≤ 2 * b * 1 * 1 := by
            exact mul_le_mul_of_nonneg_left hu1 (by positivity)
      _ = 2 * b := by ring
  have hsecond :
      2 * beta ^ 2 * sctLatticeC d beta h n *
          sctBoundaryCovarianceError d beta h n ≤
        2 * b ^ 2 * ((2 * d : ℝ) / (a * h)) := by
    have hb2 : beta ^ 2 ≤ b ^ 2 := by nlinarith
    have hq0 : 0 ≤ (2 * d : ℝ) / (a * h) := by positivity
    calc
      2 * beta ^ 2 * sctLatticeC d beta h n *
          sctBoundaryCovarianceError d beta h n
          ≤ 2 * b ^ 2 * sctLatticeC d beta h n *
              sctBoundaryCovarianceError d beta h n := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hb2 (by norm_num)) hc0) he0
      _ ≤ 2 * b ^ 2 * 1 * sctBoundaryCovarianceError d beta h n := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hc1 (by positivity)) he0
      _ ≤ 2 * b ^ 2 * 1 * ((2 * d : ℝ) / (a * h)) := by
            exact mul_le_mul_of_nonneg_left he (by positivity)
      _ = 2 * b ^ 2 * ((2 * d : ℝ) / (a * h)) := by ring
  linarith




theorem sctMeanfieldIntegratedError_integral_tendsto_zero
    (d : ℕ) {a b h : ℝ} (hab : a ≤ b) (ha : 0 < a) (hh : 0 < h) :
    Tendsto
      (fun k : ℕ =>
        ∫ beta in a..b, sctMeanfieldIntegratedError d (k + 1) h beta)
      atTop (nhds 0) := by
  let K : ℝ := 2 * b + 2 * b ^ 2 * ((2 * d : ℝ) / (a * h))
  have hlim : Tendsto
      (fun k : ℕ =>
        ∫ beta in a..b, sctMeanfieldIntegratedError d (k + 1) h beta)
      atTop (nhds (∫ _beta in a..b, (0 : ℝ))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => K)
    · exact Filter.Eventually.of_forall (fun k => by
        apply ContinuousOn.aestronglyMeasurable
        · exact (continuousOn_sctMeanfieldIntegratedError d (k + 1) h hh ha).mono
            (by simpa [uIoc_of_le hab] using
              (show Ioc a b ⊆ Icc a b by intro x hx; exact ⟨hx.1.le, hx.2⟩))
        · exact measurableSet_uIoc)
    · exact Filter.Eventually.of_forall (fun k =>
        Filter.Eventually.of_forall (fun beta hbeta => by
          rw [uIoc_of_le hab] at hbeta
          exact norm_sctMeanfieldIntegratedError_le
            (Nat.succ_le_succ (Nat.zero_le k)) hbeta.1.le hbeta.2 ha hh))
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall (fun beta hbeta => by
        rw [uIoc_of_le hab] at hbeta
        exact sctMeanfieldIntegratedError_tendsto_zero d beta h
          (ha.trans hbeta.1) hh)
  simpa using hlim





noncomputable def sctInfiniteMeanfieldG (d : ℕ) (h beta : ℝ) : ℝ :=
  beta ^ 2 * (1 - (sctInfiniteFieldMag d beta h) ^ 2)

theorem sctMeanfieldG_tendsto_infinite
    (d : ℕ) (beta h : ℝ) (hbeta : 0 ≤ beta) (hh : 0 ≤ h) :
    Tendsto (fun k : ℕ => sctMeanfieldG d (k + 1) h beta)
      atTop (nhds (sctInfiniteMeanfieldG d h beta)) := by
  have hm := (sctOriginMag_tendsto_iSup d beta h hbeta hh).comp
    (tendsto_add_atTop_nat 1)
  simpa only [sctMeanfieldG, sctInfiniteMeanfieldG, sctInfiniteFieldMag]
    using tendsto_const_nhds.mul (tendsto_const_nhds.sub (hm.pow 2))




theorem sctInfiniteMeanfieldG_antitone_above
    (d : ℕ) {a b h : ℝ} (hab : a ≤ b) (ha : 0 < a) (hh : 0 < h)
    (hbdd : BddAbove (tildeBetaCIsingSet d))
    (hcrit : tildeBetaCIsing d < a) :
    sctInfiniteMeanfieldG d h b ≤ sctInfiniteMeanfieldG d h a := by
  have hb : 0 < b := ha.trans_le hab
  have hleft : Tendsto
      (fun k : ℕ =>
        sctMeanfieldG d (k + 1) h b - sctMeanfieldG d (k + 1) h a)
      atTop
      (nhds (sctInfiniteMeanfieldG d h b - sctInfiniteMeanfieldG d h a)) :=
    (sctMeanfieldG_tendsto_infinite d b h hb.le hh.le).sub
      (sctMeanfieldG_tendsto_infinite d a h ha.le hh.le)
  have hright := sctMeanfieldIntegratedError_integral_tendsto_zero
    d hab ha hh
  have hle : sctInfiniteMeanfieldG d h b - sctInfiniteMeanfieldG d h a ≤ 0 :=
    le_of_tendsto_of_tendsto hleft hright
      (Filter.Eventually.of_forall (fun k =>
        sctMeanfieldG_sub_le_integral_error
          (Nat.succ_le_succ (Nat.zero_le k)) hab ha hh hbdd hcrit))
  linarith




theorem sctInfiniteFieldMag_meanfield_lower_bound_integrated
    (d : ℕ) (hbdd : BddAbove (tildeBetaCIsingSet d))
    (hcrit : 0 < tildeBetaCIsing d) {beta h : ℝ}
    (hbeta : tildeBetaCIsing d ≤ beta) (hh : 0 < h) :
    Real.sqrt (1 - (tildeBetaCIsing d / beta) ^ 2) ≤
      sctInfiniteFieldMag d beta h := by
  have hbeta0 : 0 < beta := hcrit.trans_le hbeta
  have hm0 := sctInfiniteFieldMag_nonneg d beta h hbeta0.le hh.le
  rcases hbeta.eq_or_lt with rfl | hcritbeta
  · simpa [hcrit.ne'] using hm0
  · let a : ℕ -> ℝ := fun k =>
      tildeBetaCIsing d +
        (beta - tildeBetaCIsing d) * (1 / ((k : ℝ) + 1))
    have ha_gt (k : ℕ) : tildeBetaCIsing d < a k := by
      dsimp [a]
      have hfrac : 0 < (1 : ℝ) / ((k : ℝ) + 1) := by positivity
      nlinarith
    have ha_le (k : ℕ) : a k ≤ beta := by
      dsimp [a]
      have hfrac0 : 0 ≤ (1 : ℝ) / ((k : ℝ) + 1) := by positivity
      have hfrac1 : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        norm_num
      nlinarith
    have ha_pos (k : ℕ) : 0 < a k := hcrit.trans (ha_gt k)
    have hG : sctInfiniteMeanfieldG d h beta ≤ (tildeBetaCIsing d) ^ 2 := by
      have hbounds : ∀ k : ℕ,
          sctInfiniteMeanfieldG d h beta ≤ (a k) ^ 2 := by
        intro k
        have hanti := sctInfiniteMeanfieldG_antitone_above d
          (ha_le k) (ha_pos k) hh hbdd (ha_gt k)
        have hma0 := sctInfiniteFieldMag_nonneg d (a k) h
          (ha_pos k).le hh.le
        have hdrop : sctInfiniteMeanfieldG d h (a k) ≤ (a k) ^ 2 := by
          unfold sctInfiniteMeanfieldG
          nlinarith [sq_nonneg (sctInfiniteFieldMag d (a k) h)]
        exact hanti.trans hdrop
      have ha_tendsto : Tendsto a atTop (nhds (tildeBetaCIsing d)) := by
        have hz := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        simpa only [a, mul_zero, add_zero] using
          tendsto_const_nhds.add (tendsto_const_nhds.mul hz)
      exact le_of_tendsto_of_tendsto tendsto_const_nhds (ha_tendsto.pow 2)
        (Filter.Eventually.of_forall hbounds)
    have hsquare : 1 - (tildeBetaCIsing d / beta) ^ 2 ≤
        (sctInfiniteFieldMag d beta h) ^ 2 := by
      unfold sctInfiniteMeanfieldG at hG
      have hb2 : 0 < beta ^ 2 := sq_pos_of_pos hbeta0
      rw [div_pow]
      have hone : 1 - (sctInfiniteFieldMag d beta h) ^ 2 ≤
          (tildeBetaCIsing d) ^ 2 / beta ^ 2 := by
        rw [le_div_iff₀ hb2]
        nlinarith
      linarith
    calc
      Real.sqrt (1 - (tildeBetaCIsing d / beta) ^ 2)
          ≤ Real.sqrt ((sctInfiniteFieldMag d beta h) ^ 2) :=
        Real.sqrt_le_sqrt hsquare
      _ = sctInfiniteFieldMag d beta h := Real.sqrt_sq hm0



theorem sctZeroPlus_meanfield_lower_bound_integrated
    (d : ℕ) (hbdd : BddAbove (tildeBetaCIsingSet d))
    (hcrit : 0 < tildeBetaCIsing d) {beta : ℝ}
    (hbeta : tildeBetaCIsing d ≤ beta) :
    Real.sqrt (1 - (tildeBetaCIsing d / beta) ^ 2) ≤
      sctZeroPlusMag d beta := by
  have hbounds : ∀ k : ℕ,
      Real.sqrt (1 - (tildeBetaCIsing d / beta) ^ 2) ≤
        sctInfiniteFieldMag d beta (sctFieldToZero k) := by
    intro k
    exact sctInfiniteFieldMag_meanfield_lower_bound_integrated d hbdd hcrit
      hbeta (sctFieldToZero_pos k)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    (sctInfiniteFieldMag_tendsto_zeroPlus d beta (hcrit.le.trans hbeta))
    (Filter.Eventually.of_forall hbounds)

end Sharpness
end StatMech
