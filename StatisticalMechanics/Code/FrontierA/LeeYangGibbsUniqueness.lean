/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.LeeYangBoundaryPressure
import Code.FrontierA.LeeYangLocalCorrelationReduction
import Code.FrontierB.CurrentContinuityPhaseCollapse
import Code.FrontierB.CurrentContinuityVaryingTemperature
import Code.Ising.GibbsSimplexInfinite
import Code.Ising.IsingPlusTIFromPlacement
import Code.Ising.MinusStateDLR
import Code.Ising.Peierls
import Code.Ising.ZeroBetaDLRUniqueness
import Code.Sharpness.MeanfieldIsingPlusBridge

open Filter Finset MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators BoundedContinuousFunction ENNReal

namespace StatMech.FrontierA

open StatMech.ConfigSpace StatMech.FK StatMech.Ising StatMech.Lattice
  StatMech.Sharpness


noncomputable def fvBoxPressure (eta : ConfigSpace (Site d))
    (n : ℕ) (B : Finset (Sym2 (Site d))) (beta h : ℝ) : ℝ :=
  Real.log (fvZ eta n B beta h) / ((boxFinset d n).card : ℝ)


noncomputable def fvBoxAverageSpin (eta : ConfigSpace (Site d))
    (n : ℕ) (B : Finset (Sym2 (Site d))) (beta h : ℝ) : ℝ :=
  (∑ x ∈ boxFinset d n,
      ∫ omega, spin omega x ∂(fvMeasure eta n B beta h)) /
    ((boxFinset d n).card : ℝ)

theorem fvWeight_hasDerivAt_field (eta : ConfigSpace (Site d))
    (n : ℕ) (B : Finset (Sym2 (Site d))) (beta h : ℝ)
    (tau : {x // x ∈ box d n} → Bool) :
    HasDerivAt (fun t => fvWeight eta n B beta t tau)
      (fvWeight eta n B beta h tau *
        (beta * ∑ x ∈ boxFinset d n, spin (glue eta tau) x)) h := by
  unfold fvWeight fvEnergy
  let E := ∑ e ∈ B, bond (glue eta tau) e
  let M := ∑ x ∈ boxFinset d n, spin (glue eta tau) x
  have hrw : (fun t => Real.exp (-beta * (-E - t * M))) =
      fun t => Real.exp (beta * E + t * (beta * M)) := by
    funext t
    congr 1
    ring
  rw [hrw]
  have hlin : HasDerivAt (fun t : ℝ => t * (beta * M)) (beta * M) h := by
    simpa using (hasDerivAt_id h).mul_const (beta * M)
  have hd : HasDerivAt (fun t : ℝ => beta * E + t * (beta * M))
      (beta * M) h := by
    simpa using hlin.const_add (beta * E)
  convert (Real.hasDerivAt_exp (beta * E + h * (beta * M))).comp h hd using 1
  dsimp only [E, M]
  congr 2
  ring

theorem fvZ_hasDerivAt_field (eta : ConfigSpace (Site d))
    (n : ℕ) (B : Finset (Sym2 (Site d))) (beta h : ℝ) :
    HasDerivAt (fun t => fvZ eta n B beta t)
      (∑ tau : {x // x ∈ box d n} → Bool,
        fvWeight eta n B beta h tau *
          (beta * ∑ x ∈ boxFinset d n, spin (glue eta tau) x)) h := by
  unfold fvZ
  simpa only [Finset.sum_fn] using
    (HasDerivAt.sum fun tau (_ : tau ∈ (Finset.univ : Finset
      ({x // x ∈ box d n} → Bool))) =>
        fvWeight_hasDerivAt_field eta n B beta h tau)

theorem fvBoxAverageSpin_eq_completion_sum
    (eta : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (beta h : ℝ) :
    fvBoxAverageSpin eta n B beta h =
      (∑ tau : {x // x ∈ box d n} → Bool,
        fvProb eta n B beta h tau *
          (∑ x ∈ boxFinset d n, spin (glue eta tau) x)) /
        ((boxFinset d n).card : ℝ) := by
  unfold fvBoxAverageSpin
  simp_rw [integral_fvMeasure_eq_sum eta n B beta h]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro tau htau
  rw [Finset.mul_sum]

theorem fvBoxPressure_hasDerivAt_field
    (eta : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (beta h : ℝ) :
    HasDerivAt (fun t => fvBoxPressure eta n B beta t)
      (beta * fvBoxAverageSpin eta n B beta h) h := by
  have hZ := fvZ_hasDerivAt_field eta n B beta h
  have hlog := hZ.log (fvZ_ne_zero eta n B beta h)
  have hdiv := hlog.div_const ((boxFinset d n).card : ℝ)
  rw [fvBoxAverageSpin_eq_completion_sum]
  convert hdiv using 1
  unfold fvProb
  simp_rw [div_eq_mul_inv]
  conv_lhs =>
    rw [← mul_assoc, Finset.mul_sum]
  conv_rhs =>
    rw [show (∑ tau : {x // x ∈ box d n} → Bool,
          fvWeight eta n B beta h tau *
            (beta * ∑ x ∈ boxFinset d n, spin (glue eta tau) x)) *
          (fvZ eta n B beta h)⁻¹ *
          (((boxFinset d n).card : ℝ))⁻¹ =
        ((fvZ eta n B beta h)⁻¹ *
          (∑ tau : {x // x ∈ box d n} → Bool,
            fvWeight eta n B beta h tau *
              (beta * ∑ x ∈ boxFinset d n, spin (glue eta tau) x))) *
          (((boxFinset d n).card : ℝ))⁻¹ by ring,
      Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro tau htau
  ring

theorem plusBoxPressure_hasDerivAt_field
    (d n : ℕ) (beta h : ℝ) :
    HasDerivAt
      (fun t => fvBoxPressure (plusField d) n (bondFinsetTouch d n) beta t)
      (beta * fvBoxAverageSpin (plusField d) n
        (bondFinsetTouch d n) beta h) h :=
  fvBoxPressure_hasDerivAt_field _ _ _ _ _

theorem minusBoxPressure_hasDerivAt_field
    (d n : ℕ) (beta h : ℝ) :
    HasDerivAt
      (fun t => fvBoxPressure (minusField d) n (bondFinsetTouch d n) beta t)
      (beta * fvBoxAverageSpin (minusField d) n
        (bondFinsetTouch d n) beta h) h :=
  fvBoxPressure_hasDerivAt_field _ _ _ _ _

theorem fvBoxPressure_convexOn_field
    (eta : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (beta : ℝ) :
    ConvexOn ℝ Set.univ (fun h => fvBoxPressure eta n B beta h) := by
  have hcard : 0 ≤ (((boxFinset d n).card : ℝ))⁻¹ := by positivity
  have hconv := (logFvZ_convexOn_field eta n B beta).smul hcard
  simpa only [fvBoxPressure, div_eq_inv_mul, smul_eq_mul] using hconv

theorem isingBoxPressureLimit_hasDerivAt_pos
    (d : ℕ) (hd : 1 ≤ d) {beta : ℝ} (hbeta : 0 < beta)
    {h : ℝ} (hh : 0 < h) :
    ∃ L : ℝ, HasDerivAt (isingBoxPressureLimit d hd beta) L h := by
  obtain ⟨P, g, hanchor, hlimit, hPdiff, hgdiff, hPderiv, hreal⟩ :=
    leeYangBox_holomorphicPressure_rightHalfPlane_identified
      d hd hbeta h hh
  have hmap : MapsTo (fun t : ℝ => (t : ℂ)) (Ioi 0) {z : ℂ | 0 < z.re} := by
    intro t ht
    simpa using ht
  have hpre := hlimit.comp (fun t : ℝ => (t : ℂ)) hmap
    Complex.continuous_ofReal.continuousOn
  have hre := Complex.reCLM.uniformContinuous.comp_tendstoLocallyUniformlyOn hpre
  have hfamily : (fun n => (Complex.reCLM : ℂ → ℝ) ∘
      leeYangNormalizedFieldLogDerivative (boxGraph d n) beta ∘
        fun t : ℝ => (t : ℂ)) =
      (fun n t => isingBoxPressureFieldDerivative d n beta t) := by
    funext n t
    rw [Function.comp_apply, Function.comp_apply,
      leeYangNormalizedFieldLogDerivative_real_eq_pressureDerivative]
    simp
  rw [hfamily] at hre
  have hderiv : TendstoLocallyUniformlyOn
      (fun n t => isingBoxPressureFieldDerivative d n beta t)
      (fun t => (g (t : ℂ)).re) atTop (Ioi 0) := by
    simpa only [Function.comp_apply] using hre
  refine ⟨(g (h : ℂ)).re, ?_⟩
  apply hasDerivAt_of_tendstoLocallyUniformlyOn isOpen_Ioi hderiv
  · exact Filter.Eventually.of_forall fun n t _ =>
      isingBoxPressureSeq_hasDerivAt_field d n beta t
  · intro t ht
    exact isingBoxPressure_tendsto_limit d hd beta t
  · exact hh

theorem isingBoxPressureLimit_oneSided_eq_pos
    (d : ℕ) (hd : 1 ≤ d) {beta : ℝ} (hbeta : 0 < beta)
    {h : ℝ} (hh : 0 < h) :
    pressureLeftDeriv (isingBoxPressureLimit d hd beta) h =
      pressureRightDeriv (isingBoxPressureLimit d hd beta) h := by
  obtain ⟨L, hL⟩ := isingBoxPressureLimit_hasDerivAt_pos d hd hbeta hh
  unfold pressureLeftDeriv pressureRightDeriv
  rw [hL.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio h),
    hL.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi h)]

theorem plusBoxAverageSpin_tendsto_pressureDeriv
    (d : ℕ) (hd : 1 ≤ d) {beta : ℝ} (hbeta : 0 < beta)
    {h : ℝ} (hh : 0 < h) :
    Tendsto (fun n => beta * fvBoxAverageSpin (plusField d) n
        (bondFinsetTouch d n) beta h) atTop
      (nhds (pressureRightDeriv (isingBoxPressureLimit d hd beta) h)) := by
  apply fpd_deriv_interchange_of_differentiable
    (fun n t => fvBoxPressure (plusField d) n (bondFinsetTouch d n) beta t)
    (isingBoxPressureLimit d hd beta)
    (fun n t => beta * fvBoxAverageSpin (plusField d) n
      (bondFinsetTouch d n) beta t)
  · exact fun n => fvBoxPressure_convexOn_field _ _ _ _
  · exact fun n t => plusBoxPressure_hasDerivAt_field d n beta t
  · intro t
    simpa only [fvBoxPressure] using
      plusBoxFvPressure_tendsto_isingBoxPressureLimit d hd beta t
  · exact isingBoxPressureLimit_convexOn_field d hd beta
  · exact isingBoxPressureLimit_oneSided_eq_pos d hd hbeta hh

theorem minusBoxAverageSpin_tendsto_pressureDeriv
    (d : ℕ) (hd : 1 ≤ d) {beta : ℝ} (hbeta : 0 < beta)
    {h : ℝ} (hh : 0 < h) :
    Tendsto (fun n => beta * fvBoxAverageSpin (minusField d) n
        (bondFinsetTouch d n) beta h) atTop
      (nhds (pressureRightDeriv (isingBoxPressureLimit d hd beta) h)) := by
  apply fpd_deriv_interchange_of_differentiable
    (fun n t => fvBoxPressure (minusField d) n (bondFinsetTouch d n) beta t)
    (isingBoxPressureLimit d hd beta)
    (fun n t => beta * fvBoxAverageSpin (minusField d) n
      (bondFinsetTouch d n) beta t)
  · exact fun n => fvBoxPressure_convexOn_field _ _ _ _
  · exact fun n t => minusBoxPressure_hasDerivAt_field d n beta t
  · intro t
    simpa only [fvBoxPressure] using
      minusBoxFvPressure_tendsto_isingBoxPressureLimit d hd beta t
  · exact isingBoxPressureLimit_convexOn_field d hd beta
  · exact isingBoxPressureLimit_oneSided_eq_pos d hd hbeta hh

theorem integral_spin_eq_origin_of_translationInvariant
    (mu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure mu]
    (hti : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site d)) mu) (x : Site d) :
    (∫ omega, spin omega x ∂mu) =
      ∫ omega, spin omega (StatMech.Percolation.origin d) ∂mu := by
  let g : Multiplicative (Site d) := Multiplicative.ofAdd x
  calc
    (∫ omega, spin omega x ∂mu) =
        ∫ omega, spin omega x ∂Measure.map (ConfigSpace.shift g) mu := by
      rw [hti.map_eq g]
    _ = ∫ omega, spin (ConfigSpace.shift g omega) x ∂mu := by
      change (∫ omega, spinBCF x omega ∂Measure.map (ConfigSpace.shift g) mu) = _
      rw [integral_map (continuous_shift g).measurable.aemeasurable
        (spinBCF x).continuous.aestronglyMeasurable]
      simp only [spinBCF_apply]
    _ = ∫ omega, spin omega (StatMech.Percolation.origin d) ∂mu := by
      apply integral_congr_ae
      filter_upwards with omega
      have hxg : g • StatMech.Percolation.origin d = x := by
        ext i
        simp [g, StatMech.Percolation.origin]
      rw [← hxg, iptp_spin_shift]

theorem plusState_spin_le_fvBoxAverageSpin
    (d n : ℕ) {beta h : ℝ} (hbeta : 0 ≤ beta) (hh : 0 ≤ h)
    (hti : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site d))
      (plusState d beta h : Measure (ConfigSpace (Site d)))) :
    (∫ omega, spin omega (StatMech.Percolation.origin d)
        ∂(plusState d beta h : Measure (ConfigSpace (Site d)))) ≤
      fvBoxAverageSpin (plusField d) n (bondFinsetTouch d n) beta h := by
  let mu : Measure (ConfigSpace (Site d)) := plusState d beta h
  have hpoint : ∀ x : Site d,
      (∫ omega, spin omega x ∂mu) ≤
        ∫ omega, spin omega x ∂(plusMeasure d n beta h : Measure _) := by
    intro x
    have hprob := gsi_dlr_real_le_plusMeasure beta h hbeta hh mu
      (psdlr_plusState_isDLR_uncond beta h) n
      (ibs_measurableSet_spinUp x) (sct_isIncreasing_spinUp x)
    rw [sct_integral_spin_eq_two_siteProb_sub_one,
      sct_integral_spin_eq_two_siteProb_sub_one]
    linarith
  have hsum :
      ∑ x ∈ boxFinset d n, (∫ omega, spin omega x ∂mu) ≤
        ∑ x ∈ boxFinset d n,
          ∫ omega, spin omega x ∂(plusMeasure d n beta h : Measure _) :=
    Finset.sum_le_sum fun x _ => hpoint x
  have hcard : (0 : ℝ) < (boxFinset d n).card := by
    exact_mod_cast boxFinset_card_pos (d := d) n
  unfold fvBoxAverageSpin
  apply (le_div_iff₀ hcard).2
  calc
    (∫ omega, spin omega (StatMech.Percolation.origin d) ∂mu) *
        ((boxFinset d n).card : ℝ) =
      ∑ x ∈ boxFinset d n, (∫ omega, spin omega x ∂mu) := by
        simp_rw [integral_spin_eq_origin_of_translationInvariant mu hti]
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ ∑ x ∈ boxFinset d n,
          ∫ omega, spin omega x ∂(plusMeasure d n beta h : Measure _) := hsum
    _ = ∑ x ∈ boxFinset d n,
          ∫ omega, spin omega x ∂(fvMeasure (plusField d) n
            (bondFinsetTouch d n) beta h) := by rfl

theorem fvBoxAverageSpin_le_minusState_spin
    (d n : ℕ) {beta h : ℝ} (hbeta : 0 ≤ beta) (hh : 0 ≤ h)
    (hdlr : IsDLRState d beta h
      (minusState d beta h : Measure (ConfigSpace (Site d))))
    (hti : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site d))
      (minusState d beta h : Measure (ConfigSpace (Site d)))) :
    fvBoxAverageSpin (minusField d) n (bondFinsetTouch d n) beta h ≤
      ∫ omega, spin omega (StatMech.Percolation.origin d)
        ∂(minusState d beta h : Measure (ConfigSpace (Site d))) := by
  let mu : Measure (ConfigSpace (Site d)) := minusState d beta h
  have hpoint : ∀ x : Site d,
      (∫ omega, spin omega x ∂(minusMeasure d n beta h : Measure _)) ≤
        ∫ omega, spin omega x ∂mu := by
    intro x
    have hprob := gsi_minusMeasure_le_dlr_real beta h hbeta hh mu hdlr n
      (ibs_measurableSet_spinUp x) (sct_isIncreasing_spinUp x)
    rw [sct_integral_spin_eq_two_siteProb_sub_one,
      sct_integral_spin_eq_two_siteProb_sub_one]
    linarith
  have hsum :
      ∑ x ∈ boxFinset d n,
          (∫ omega, spin omega x ∂(minusMeasure d n beta h : Measure _)) ≤
        ∑ x ∈ boxFinset d n, ∫ omega, spin omega x ∂mu :=
    Finset.sum_le_sum fun x _ => hpoint x
  have hcard : (0 : ℝ) < (boxFinset d n).card := by
    exact_mod_cast boxFinset_card_pos (d := d) n
  unfold fvBoxAverageSpin
  apply (div_le_iff₀ hcard).2
  calc
    (∑ x ∈ boxFinset d n,
        ∫ omega, spin omega x ∂(fvMeasure (minusField d) n
          (bondFinsetTouch d n) beta h)) =
      ∑ x ∈ boxFinset d n,
        ∫ omega, spin omega x ∂(minusMeasure d n beta h : Measure _) := by rfl
    _ ≤ ∑ x ∈ boxFinset d n, ∫ omega, spin omega x ∂mu := hsum
    _ = (∫ omega, spin omega (StatMech.Percolation.origin d) ∂mu) *
        ((boxFinset d n).card : ℝ) := by
      simp_rw [integral_spin_eq_origin_of_translationInvariant mu hti]
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

theorem plusState_eq_minusState_of_positive_field_aux
    (d : ℕ) (hd : 1 ≤ d) {beta h : ℝ}
    (hbeta : 0 < beta) (hh : 0 < h)
    (hminusDLR : IsDLRState d beta h
      (minusState d beta h : Measure (ConfigSpace (Site d))))
    (hminusTI : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site d))
      (minusState d beta h : Measure (ConfigSpace (Site d)))) :
    (plusState d beta h : Measure (ConfigSpace (Site d))) =
      (minusState d beta h : Measure (ConfigSpace (Site d))) := by
  let mup : Measure (ConfigSpace (Site d)) := plusState d beta h
  let mum : Measure (ConfigSpace (Site d)) := minusState d beta h
  let mp : ℝ := ∫ omega, spin omega (StatMech.Percolation.origin d) ∂mup
  let mm : ℝ := ∫ omega, spin omega (StatMech.Percolation.origin d) ∂mum
  let L := pressureRightDeriv (isingBoxPressureLimit d hd beta) h
  have hplusTI := iptp_plusState_isTranslationInvariant (d := d) hbeta.le hh.le
  have hplusLim := plusBoxAverageSpin_tendsto_pressureDeriv d hd hbeta hh
  have hminusLim := minusBoxAverageSpin_tendsto_pressureDeriv d hd hbeta hh
  have hple : beta * mp ≤ L := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hplusLim
    exact Filter.Eventually.of_forall fun n =>
      mul_le_mul_of_nonneg_left
        (plusState_spin_le_fvBoxAverageSpin d n hbeta.le hh.le hplusTI)
        hbeta.le
  have hmle : L ≤ beta * mm := by
    apply le_of_tendsto_of_tendsto hminusLim tendsto_const_nhds
    exact Filter.Eventually.of_forall fun n =>
      mul_le_mul_of_nonneg_left
        (fvBoxAverageSpin_le_minusState_spin d n hbeta.le hh.le
          hminusDLR hminusTI) hbeta.le
  have hdomc : StochasticallyDominatedClopen mum mup :=
    (gsi_infinite_volume_sandwich beta h hbeta.le hh.le mup
      (psdlr_plusState_isDLR_uncond beta h)).1
  have hmmple : mm ≤ mp := by
    have hprob := hdomc {omega | omega (StatMech.Percolation.origin d) = true}
      (ibs_isClopen_spinUp (StatMech.Percolation.origin d))
      (sct_isIncreasing_spinUp (StatMech.Percolation.origin d))
    have hm := StatMech.FrontierB.integral_spin_eq_two_mul_spinUp_sub_one
      mum (StatMech.Percolation.origin d)
    have hp := StatMech.FrontierB.integral_spin_eq_two_mul_spinUp_sub_one
      mup (StatMech.Percolation.origin d)
    dsimp only [mm, mp]
    linarith
  have hmpeq : mm = mp := by
    nlinarith
  have hmarg : ∀ x : Site d,
      mum.real {omega | omega x = true} =
        mup.real {omega | omega x = true} := by
    intro x
    have hmhom := integral_spin_eq_origin_of_translationInvariant mum hminusTI x
    have hphom := integral_spin_eq_origin_of_translationInvariant mup hplusTI x
    have hm := StatMech.FrontierB.integral_spin_eq_two_mul_spinUp_sub_one mum x
    have hp := StatMech.FrontierB.integral_spin_eq_two_mul_spinUp_sub_one mup x
    dsimp only [mm, mp] at hmpeq
    linarith
  exact (StatMech.FrontierB.measure_eq_of_clopenDom_coordinate_eq mum mup
    hdomc hmarg).symm

theorem gibbs_unique_of_positive_field_aux
    (d : ℕ) (hd : 1 ≤ d) {beta h : ℝ}
    (hbeta : 0 < beta) (hh : 0 < h)
    (hminusDLR : IsDLRState d beta h
      (minusState d beta h : Measure (ConfigSpace (Site d))))
    (hminusTI : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site d))
      (minusState d beta h : Measure (ConfigSpace (Site d))))
    (mu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure mu]
    (hmu : IsDLRState d beta h mu) :
    mu = (minusState d beta h : Measure (ConfigSpace (Site d))) := by
  exact gsi_gibbs_unique_of_phases_eq beta h hbeta.le hh.le mu hmu
    (plusState_eq_minusState_of_positive_field_aux d hd hbeta hh
      hminusDLR hminusTI)

theorem specApply_flipConfig
    (n : ℕ) (B : Finset (Sym2 (Site d))) (beta h : ℝ)
    (f : ConfigSpace (Site d) →ᵇ ℝ) (omega : ConfigSpace (Site d)) :
    specApply n B beta (-h) (f : ConfigSpace (Site d) → ℝ)
        (flipConfig omega) =
      specApply n B beta h
        (fun eta => f (flipConfig eta)) omega := by
  unfold specApply
  rw [← map_fvMeasure_flip omega n B beta h]
  rw [integral_map measurable_flipConfig.aemeasurable
    f.continuous.aestronglyMeasurable]



theorem isDLRState_map_flipConfig
    (beta h : ℝ) (mu : Measure (ConfigSpace (Site d)))
    [IsProbabilityMeasure mu] (hmu : IsDLRState d beta h mu) :
    IsDLRState d beta (-h) (Measure.map flipConfig mu) := by
  let muf : Measure (ConfigSpace (Site d)) := Measure.map flipConfig mu
  haveI : IsProbabilityMeasure muf :=
    Measure.isProbabilityMeasure_map measurable_flipConfig.aemeasurable
  apply isDLRState_of_specFull_bind_eq beta (-h) muf
  intro n
  let K := isingSpecFull n (bondFinsetTouch d n) beta (-h)
  haveI : IsProbabilityMeasure (K ∘ₘ muf) := by dsimp [K]; infer_instance
  have hfm : (⟨K ∘ₘ muf, inferInstance⟩ : FiniteMeasure (ConfigSpace (Site d))) =
      (⟨muf, inferInstance⟩ : FiniteMeasure (ConfigSpace (Site d))) := by
    refine FiniteMeasure.ext_of_forall_integral_eq (fun f => ?_)
    let T : C(ConfigSpace (Site d), ConfigSpace (Site d)) :=
      ⟨flipConfig, continuous_flipConfig⟩
    let ff : ConfigSpace (Site d) →ᵇ ℝ := f.compContinuous T
    change (∫ omega, f omega ∂(K ∘ₘ muf)) = ∫ omega, f omega ∂muf
    rw [integral_bind_specApply n (bondFinsetTouch d n) beta (-h) muf f]
    change (∫ omega, (specApply_bcf n (bondFinsetTouch d n) beta (-h) f) omega
        ∂Measure.map flipConfig mu) = _
    rw [integral_map measurable_flipConfig.aemeasurable
      (specApply_bcf n (bondFinsetTouch d n) beta (-h) f).continuous.aestronglyMeasurable]
    simp only [specApply_bcf_apply]
    have hspec : (fun omega => specApply n (bondFinsetTouch d n) beta (-h)
        (f : ConfigSpace (Site d) → ℝ) (flipConfig omega)) =
      fun omega => specApply n (bondFinsetTouch d n) beta h
        (fun eta => f (flipConfig eta)) omega := by
      funext omega
      exact specApply_flipConfig n (bondFinsetTouch d n) beta h f omega
    rw [hspec]
    change (∫ omega, specApply n (bondFinsetTouch d n) beta h
        (ff : ConfigSpace (Site d) → ℝ) omega ∂mu) = _
    rw [StatMech.FrontierB.specApply_integral_eq_of_isDLRState beta h mu hmu n ff]
    change (∫ omega, f (flipConfig omega) ∂mu) = ∫ omega, f omega ∂muf
    dsimp only [muf]
    rw [integral_map measurable_flipConfig.aemeasurable
      f.continuous.aestronglyMeasurable]
  simpa only [K] using congrArg
    (fun nu : FiniteMeasure (ConfigSpace (Site d)) =>
      (nu : Measure (ConfigSpace (Site d)))) hfm



theorem plusState_eq_minusState_of_positive_field
    (d : ℕ) (hd : 1 ≤ d) {beta h : ℝ}
    (hbeta : 0 < beta) (hh : 0 < h) :
    (plusState d beta h : Measure (ConfigSpace (Site d))) =
      (minusState d beta h : Measure (ConfigSpace (Site d))) :=
  plusState_eq_minusState_of_positive_field_aux d hd hbeta hh
    (msdlr_minusState_isDLR_uncond beta h)
    (iptm_minusState_isTranslationInvariant hbeta.le hh.le)



theorem gibbs_unique_of_positive_field
    (d : ℕ) (hd : 1 ≤ d) {beta h : ℝ}
    (hbeta : 0 < beta) (hh : 0 < h)
    (mu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure mu]
    (hmu : IsDLRState d beta h mu) :
    mu = (minusState d beta h : Measure (ConfigSpace (Site d))) :=
  gsi_gibbs_unique_of_phases_eq beta h hbeta.le hh.le mu hmu
    (plusState_eq_minusState_of_positive_field d hd hbeta hh)

theorem map_flipConfig_map_flipConfig
    (mu : Measure (ConfigSpace (Site d))) :
    Measure.map flipConfig (Measure.map flipConfig mu) = mu := by
  rw [Measure.map_map measurable_flipConfig measurable_flipConfig]
  have hfun : (flipConfig (d := d)) ∘ (flipConfig (d := d)) =
      (id : ConfigSpace (Site d) → ConfigSpace (Site d)) := by
    funext omega
    exact flipConfig_involutive omega
  rw [hfun, Measure.map_id]



theorem gibbs_states_eq_of_negative_field
    (d : ℕ) (hd : 1 ≤ d) {beta h : ℝ}
    (hbeta : 0 < beta) (hh : h < 0)
    (mu nu : Measure (ConfigSpace (Site d)))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmu : IsDLRState d beta h mu) (hnu : IsDLRState d beta h nu) :
    mu = nu := by
  let muf := Measure.map flipConfig mu
  let nuf := Measure.map flipConfig nu
  haveI : IsProbabilityMeasure muf :=
    Measure.isProbabilityMeasure_map measurable_flipConfig.aemeasurable
  haveI : IsProbabilityMeasure nuf :=
    Measure.isProbabilityMeasure_map measurable_flipConfig.aemeasurable
  have hmudlr : IsDLRState d beta (-h) muf :=
    isDLRState_map_flipConfig beta h mu hmu
  have hnudlr : IsDLRState d beta (-h) nuf :=
    isDLRState_map_flipConfig beta h nu hnu
  have hm := gibbs_unique_of_positive_field d hd hbeta (neg_pos.mpr hh)
    muf hmudlr
  have hn := gibbs_unique_of_positive_field d hd hbeta (neg_pos.mpr hh)
    nuf hnudlr
  have heq : muf = nuf := hm.trans hn.symm
  have hmap := congrArg (Measure.map flipConfig) heq
  simpa only [muf, nuf, map_flipConfig_map_flipConfig] using hmap



theorem plusState_eq_minusState_of_nonzero_field_of_pos_beta
    (d : ℕ) (hd : 1 ≤ d) {beta h : ℝ}
    (hbeta : 0 < beta) (hh : h ≠ 0) :
    (plusState d beta h : Measure (ConfigSpace (Site d))) =
      (minusState d beta h : Measure (ConfigSpace (Site d))) := by
  rcases lt_or_gt_of_ne hh with hhneg | hhpos
  · exact gibbs_states_eq_of_negative_field d hd hbeta hhneg _ _
      (psdlr_plusState_isDLR_uncond beta h)
      (msdlr_minusState_isDLR_uncond beta h)
  · exact plusState_eq_minusState_of_positive_field d hd hbeta hhpos



theorem gibbs_unique_of_nonzero_field_of_pos_beta
    (d : ℕ) (hd : 1 ≤ d) {beta h : ℝ}
    (hbeta : 0 < beta) (hh : h ≠ 0)
    (mu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure mu]
    (hmu : IsDLRState d beta h mu) :
    mu = (minusState d beta h : Measure (ConfigSpace (Site d))) := by
  rcases lt_or_gt_of_ne hh with hhneg | hhpos
  · exact gibbs_states_eq_of_negative_field d hd hbeta hhneg mu _ hmu
      (msdlr_minusState_isDLR_uncond beta h)
  · exact gibbs_unique_of_positive_field d hd hbeta hhpos mu hmu




theorem plusState_eq_minusState_of_nonzero_field
    (d : ℕ) (hd : 1 ≤ d) {beta h : ℝ}
    (hbeta : 0 ≤ beta) (hh : h ≠ 0) :
    (plusState d beta h : Measure (ConfigSpace (Site d))) =
      (minusState d beta h : Measure (ConfigSpace (Site d))) := by
  rcases hbeta.eq_or_lt with hzero | hpos
  · subst beta
    exact gibbs_unique_zero_beta h _
      (psdlr_plusState_isDLR_uncond 0 h)
  · exact plusState_eq_minusState_of_nonzero_field_of_pos_beta d hd hpos hh


theorem gibbs_unique_of_nonzero_field
    (d : ℕ) (hd : 1 ≤ d) {beta h : ℝ}
    (hbeta : 0 ≤ beta) (hh : h ≠ 0)
    (mu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure mu]
    (hmu : IsDLRState d beta h mu) :
    mu = (minusState d beta h : Measure (ConfigSpace (Site d))) := by
  rcases hbeta.eq_or_lt with hzero | hpos
  · subst beta
    exact gibbs_unique_zero_beta h mu hmu
  · exact gibbs_unique_of_nonzero_field_of_pos_beta d hd hpos hh mu hmu

end StatMech.FrontierA
