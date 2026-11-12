/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.SLE.LoewnerMaximal
import Mathlib.Analysis.Complex.Conformal











open Complex Set Metric Filter Topology
open scoped Interval

namespace StatMech.SLE

noncomputable section



theorem linearODE_terminal_eq_initial_mul_exp_integral
    {T : Real} (hT : 0 <= T) {a f : Real -> Complex}
    (ha : ContinuousOn a (Icc (0 : Real) T))
    (hf : ContinuousOn f (Icc (0 : Real) T))
    (hderiv : ∀ t ∈ Icc (0 : Real) T,
      HasDerivWithinAt f (a t * f t) (Icc (0 : Real) T) t) :
    f T = f 0 * Complex.exp (∫ s in (0 : Real)..T, a s) := by
  rcases hT.eq_or_lt with rfl | hTpos
  · simp
  let A : Real -> Complex := fun t => ∫ s in (0 : Real)..t, a s
  let r : Real -> Complex := fun t => Complex.exp (-A t) * f t
  have hA : ∀ t ∈ Icc (0 : Real) T,
      HasDerivWithinAt A (a t) (Icc (0 : Real) T) t := by
    intro t ht
    letI : Fact (t ∈ Icc (0 : Real) T) := ⟨ht⟩
    apply intervalIntegral.integral_hasDerivWithinAt_right
    · apply ContinuousOn.intervalIntegrable
      exact ha.mono (by
        rw [uIcc_of_le ht.1]
        exact Icc_subset_Icc_right ht.2)
    · exact ha.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t
    · exact ha t ht
  have hr : ∀ t ∈ Icc (0 : Real) T,
      HasDerivWithinAt r 0 (Icc (0 : Real) T) t := by
    intro t ht
    have hexp : HasDerivWithinAt (fun s => Complex.exp (-A s))
        (Complex.exp (-A t) * (-a t)) (Icc (0 : Real) T) t := by
      simpa only [Function.comp_apply] using
        (Complex.hasDerivAt_exp (-A t)).comp_hasDerivWithinAt t (hA t ht).neg
    dsimp only [r]
    convert hexp.mul (hderiv t ht) using 1
    all_goals ring
  have hrdiff : DifferentiableOn Real r (Icc (0 : Real) T) :=
    fun t ht => (hr t ht).differentiableWithinAt
  have hrfderiv : ∀ t ∈ Icc (0 : Real) T,
      fderivWithin Real r (Icc (0 : Real) T) t = 0 := by
    intro t ht
    simpa using (hr t ht).hasFDerivWithinAt.fderivWithin
      ((uniqueDiffOn_Icc hTpos).uniqueDiffWithinAt ht)
  have hconst : r 0 = r T :=
    (convex_Icc (0 : Real) T).is_const_of_fderivWithin_eq_zero
      hrdiff hrfderiv ⟨le_rfl, hTpos.le⟩ ⟨hTpos.le, le_rfl⟩
  have hconst' : f 0 = Complex.exp (-(∫ s in (0 : Real)..T, a s)) * f T := by
    simpa [r, A] using hconst
  calc
    f T = Complex.exp (∫ s in (0 : Real)..T, a s) *
        (Complex.exp (-(∫ s in (0 : Real)..T, a s)) * f T) := by
      rw [<- mul_assoc, <- Complex.exp_add]
      simp
    _ = Complex.exp (∫ s in (0 : Real)..T, a s) * f 0 := by rw [<- hconst']
    _ = f 0 * Complex.exp (∫ s in (0 : Real)..T, a s) := mul_comm _ _



theorem loewnerField_hasDerivAt_initial
    (W : Real -> Real) (t : Real) {z : Complex}
    (hz : z ≠ (W t : Complex)) :
    HasDerivAt (loewnerField W t)
      (-2 / (z - (W t : Complex)) ^ 2) z := by
  have hden : z - (W t : Complex) ≠ 0 := sub_ne_zero.mpr hz
  simpa [loewnerField, hden] using
    (hasDerivAt_const z (2 : Complex)).div
      ((hasDerivAt_id z).sub_const (W t : Complex)) hden



def loewnerInitialVariationalCoefficient
    (W : Real -> Real) (z : Complex) (s : Real) : Complex :=
  -2 / (loewnerMaximalMaps W s z - (W s : Complex)) ^ 2



def loewnerInitialJacobian
    (W : Real -> Real) (t : Real) (z : Complex) : Complex :=
  Complex.exp
    (∫ s in (0 : Real)..t, loewnerInitialVariationalCoefficient W z s)


theorem loewnerInitialJacobian_ne_zero
    (W : Real -> Real) (t : Real) (z : Complex) :
    loewnerInitialJacobian W t z ≠ 0 := by
  exact Complex.exp_ne_zero _

@[simp] theorem loewnerInitialJacobian_zero
    (W : Real -> Real) (z : Complex) :
    loewnerInitialJacobian W 0 z = 1 := by
  simp [loewnerInitialJacobian]



theorem loewnerMaximalMaps_hasDerivAt_of_lt_im_sq_div_sixteen
    {W : Real -> Real} (hW : Continuous W) {u : Real} (hu : 0 <= u)
    {z : Complex} (hz : z ∈ upperHalfPlane) (hshort : u < z.im ^ 2 / 16) :
    HasDerivAt (loewnerMaximalMaps W u) (loewnerInitialJacobian W u z) z := by
  have hzpos : 0 < z.im := mem_upperHalfPlane.mp hz
  let E : Real := z.im ^ 2 / 16
  let delta : Real := z.im / 2
  have hE : 0 < E := by dsimp [E]; positivity
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hradius : 0 < z.im / 4 := by positivity
  obtain ⟨alpha, halpha, C, hC⟩ := loewner_local_flow_chart hW hzpos 0
  have halpha' : ∀ w ∈ closedBall z (z.im / 4),
      alpha w 0 = w ∧
        (∀ t ∈ Icc (-E) E,
          HasDerivWithinAt (alpha w) (loewnerField W t (alpha w t))
            (Icc (-E) E) t) ∧
        ∀ t, alpha w t ∈ loewnerStrip delta := by
    simpa [E, delta] using halpha
  have hC' : ∀ t ∈ Icc (-E) E,
      LipschitzOnWith C (fun w => alpha w t) (closedBall z (z.im / 4)) := by
    simpa [E] using hC
  have htimeSubset : Icc (0 : Real) E ⊆ Icc (-E) E := by
    intro t ht
    exact ⟨(neg_nonpos.mpr hE.le).trans ht.1, ht.2⟩
  let g : ∀ w : Complex, w ∈ closedBall z (z.im / 4) ->
      LoewnerForwardSolution W w E := fun w hw =>
    { curve := alpha w
      initial := (halpha' w hw).1
      deriv := by
        intro t ht
        exact ((halpha' w hw).2.1 t (htimeSubset ht)).mono htimeSubset
      upper := by
        intro t _ht
        exact loewnerStrip_subset_upperHalfPlane hdelta ((halpha' w hw).2.2 t) }
  have hzball : z ∈ closedBall z (z.im / 4) := mem_closedBall_self hradius.le
  have hmaximal (w : Complex) (hw : w ∈ closedBall z (z.im / 4))
      (t : Real) (ht0 : 0 <= t) (htE : t < E) :
      loewnerMaximalMaps W t w = alpha w t := by
    simpa [loewnerMaximalMaps] using
      loewnerMaximalCurve_eq_forwardSolution hE (g w hw) ⟨ht0, htE⟩
  have hden (w : Complex) (hw : w ∈ closedBall z (z.im / 4)) (t : Real) :
      alpha w t - (W t : Complex) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    have himzero : (alpha w t).im = 0 := by
      simpa using congrArg Complex.im heq
    have him := mem_loewnerStrip.mp ((halpha' w hw).2.2 t)
    linarith
  let coeff : Complex -> Real -> Complex := fun w t =>
    -2 / ((alpha w t - (W t : Complex)) * (alpha z t - (W t : Complex)))
  have hfield (w : Complex) (hw : w ∈ closedBall z (z.im / 4)) (t : Real) :
      loewnerField W t (alpha w t) - loewnerField W t (alpha z t) =
        coeff w t * (alpha w t - alpha z t) := by
    have h1 := hden w hw t
    have h2 := hden z hzball t
    dsimp only [coeff]
    simp only [loewnerField_apply]
    field_simp [h1, h2]
    ring
  have hcoeffContinuous (w : Complex) (hw : w ∈ closedBall z (z.im / 4)) :
      ContinuousOn (coeff w) (Icc (0 : Real) u) := by
    have hsubE : Icc (0 : Real) u ⊆ Icc (0 : Real) E :=
      Icc_subset_Icc_right hshort.le
    have haw := (g w hw).continuousOn.mono hsubE
    have haz := (g z hzball).continuousOn.mono hsubE
    have hWcomplex : Continuous (fun t => (W t : Complex)) :=
      Complex.continuous_ofReal.comp hW
    dsimp only [coeff]
    exact continuousOn_const.div
      ((haw.sub hWcomplex.continuousOn).mul (haz.sub hWcomplex.continuousOn))
      (fun t _ht => mul_ne_zero (hden w hw t) (hden z hzball t))
  have hnormDen (w : Complex) (hw : w ∈ closedBall z (z.im / 4)) (t : Real) :
      delta <= ‖alpha w t - (W t : Complex)‖ := by
    calc
      delta <= (alpha w t).im := mem_loewnerStrip.mp ((halpha' w hw).2.2 t)
      _ = (alpha w t - (W t : Complex)).im := by simp
      _ <= ‖alpha w t - (W t : Complex)‖ := Complex.im_le_norm _
  have hcoeffBound (w : Complex) (hw : w ∈ closedBall z (z.im / 4)) (t : Real) :
      ‖coeff w t‖ <= 2 / delta ^ 2 := by
    have hprod : delta * delta <=
        ‖alpha w t - (W t : Complex)‖ * ‖alpha z t - (W t : Complex)‖ :=
      mul_le_mul (hnormDen w hw t) (hnormDen z hzball t)
        hdelta.le (norm_nonneg _)
    dsimp only [coeff]
    rw [norm_div, norm_neg, norm_ofNat, norm_mul]
    simpa [pow_two] using
      div_le_div_of_nonneg_left (show (0 : Real) <= 2 by norm_num)
        (mul_pos hdelta hdelta) hprod
  have hcoeffTendsto (t : Real) (ht : t ∈ Icc (0 : Real) u) :
      Tendsto (fun w => coeff w t) (nhds z) (nhds (coeff z t)) := by
    have htFull : t ∈ Icc (-E) E := by
      exact ⟨by linarith [ht.1], ht.2.trans hshort.le⟩
    have hat : ContinuousAt (fun w => alpha w t) z :=
      ((hC' t htFull).continuousOn z hzball).continuousAt
        (closedBall_mem_nhds z hradius)
    have hprod : ContinuousAt (fun w =>
        (alpha w t - (W t : Complex)) * (alpha z t - (W t : Complex))) z :=
      (hat.sub continuousAt_const).mul continuousAt_const
    have hprodne :
        (alpha z t - (W t : Complex)) * (alpha z t - (W t : Complex)) ≠ 0 :=
      mul_ne_zero (hden z hzball t) (hden z hzball t)
    simpa only [coeff] using (continuousAt_const.div hprod hprodne)
  have hintegral : Tendsto (fun w => ∫ t in (0 : Real)..u, coeff w t)
      (nhds z) (nhds (∫ t in (0 : Real)..u, coeff z t)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ => 2 / delta ^ 2)
    · filter_upwards [closedBall_mem_nhds z hradius] with w hw
      apply ((hcoeffContinuous w hw).mono ?_).aestronglyMeasurable measurableSet_uIoc
      intro t ht
      have := uIoc_subset_uIcc ht
      simpa [uIcc_of_le hu] using this
    · filter_upwards [closedBall_mem_nhds z hradius] with w hw
      exact Filter.Eventually.of_forall (fun t _ht => hcoeffBound w hw t)
    · exact continuous_const.intervalIntegrable _ _
    · exact Filter.Eventually.of_forall (fun t ht => by
        apply hcoeffTendsto t
        have := uIoc_subset_uIcc ht
        simpa [uIcc_of_le hu] using this)
  have hdiff (w : Complex) (hw : w ∈ closedBall z (z.im / 4)) :
      alpha w u - alpha z u =
        (w - z) * Complex.exp (∫ t in (0 : Real)..u, coeff w t) := by
    have hsubE : Icc (0 : Real) u ⊆ Icc (0 : Real) E :=
      Icc_subset_Icc_right hshort.le
    have hdiffContinuous : ContinuousOn (fun t => alpha w t - alpha z t)
        (Icc (0 : Real) u) :=
      ((g w hw).continuousOn.mono hsubE).sub ((g z hzball).continuousOn.mono hsubE)
    have hdiffDeriv : ∀ t ∈ Icc (0 : Real) u,
        HasDerivWithinAt (fun s => alpha w s - alpha z s)
          (coeff w t * (alpha w t - alpha z t)) (Icc (0 : Real) u) t := by
      intro t ht
      have hraw := ((g w hw).deriv t (hsubE ht)).sub
        ((g z hzball).deriv t (hsubE ht))
      have hmono := hraw.mono hsubE
      convert hmono using 1
      exact (hfield w hw t).symm
    have hlinear := linearODE_terminal_eq_initial_mul_exp_integral hu
      (hcoeffContinuous w hw) hdiffContinuous hdiffDeriv
    simpa [(halpha' w hw).1, (halpha' z hzball).1] using hlinear
  have hslope : Filter.Eventually (fun w =>
      slope (loewnerMaximalMaps W u) z w =
        Complex.exp (∫ t in (0 : Real)..u, coeff w t))
      (nhdsWithin z ({z}ᶜ)) := by
    have hballEventually : Filter.Eventually
        (fun w => w ∈ closedBall z (z.im / 4)) (nhdsWithin z ({z}ᶜ)) :=
      by
        have hb : Filter.Eventually (fun w => w ∈ closedBall z (z.im / 4)) (nhds z) :=
          closedBall_mem_nhds z hradius
        exact hb.filter_mono inf_le_left
    have hneEventually : Filter.Eventually (fun w => w ≠ z)
        (nhdsWithin z ({z}ᶜ)) := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      simpa only [mem_compl_iff, mem_singleton_iff] using hw
    filter_upwards [hballEventually, hneEventually] with w hw hwne
    rw [slope_def_field, hmaximal w hw u hu hshort,
      hmaximal z hzball u hu hshort, hdiff w hw]
    exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hwne)
  have hexpTendsto : Tendsto
      (fun w => Complex.exp (∫ t in (0 : Real)..u, coeff w t))
      (nhdsWithin z ({z}ᶜ))
      (nhds (Complex.exp (∫ t in (0 : Real)..u, coeff z t))) :=
    (Complex.continuous_exp.continuousAt.tendsto.comp hintegral).mono_left inf_le_left
  have hderiv : HasDerivAt (loewnerMaximalMaps W u)
      (Complex.exp (∫ t in (0 : Real)..u, coeff z t)) z :=
    hasDerivAt_iff_tendsto_slope.mpr
      (hexpTendsto.congr' (hslope.mono fun _ hw => hw.symm))
  have hintegralEq : (∫ t in (0 : Real)..u, coeff z t) =
      ∫ t in (0 : Real)..u, loewnerInitialVariationalCoefficient W z t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Icc (0 : Real) u := by
      simpa [uIcc_of_le hu] using ht
    dsimp only [coeff, loewnerInitialVariationalCoefficient]
    rw [hmaximal z hzball t htIcc.1 (htIcc.2.trans_lt hshort)]
    simp only [pow_two]
  simpa [loewnerInitialJacobian, hintegralEq] using hderiv



theorem loewnerMaximalMaps_hasDerivAt_initial_zero
    {W : Real -> Real} (hW : Continuous W) {z : Complex}
    (hz : z ∈ upperHalfPlane) :
    HasDerivAt (loewnerMaximalMaps W 0) 1 z := by
  apply (hasDerivAt_id z).congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlane.mem_nhds hz] with w hw
  simpa using loewnerMaximalMaps_zero hW hw



def HasLoewnerLocalInitialVariationalFormula (W : Real -> Real) : Prop :=
  forall (s u : Real) (z : Complex), 0 <= u -> z ∈ upperHalfPlane ->
    u < z.im ^ 2 / 16 ->
    HasDerivAt (loewnerMaximalMaps (fun r => W (s + r)) u)
      (loewnerInitialJacobian (fun r => W (s + r)) u z) z



theorem hasLoewnerLocalInitialVariationalFormula
    {W : Real -> Real} (hW : Continuous W) :
    HasLoewnerLocalInitialVariationalFormula W := by
  intro s u z hu hz hshort
  exact loewnerMaximalMaps_hasDerivAt_of_lt_im_sq_div_sixteen
    (hW.comp (continuous_const.add continuous_id)) hu hz hshort




theorem exists_loewnerMaximalMaps_hasDerivAt_ne_zero_of_localVariational
    {W : Real -> Real} (hW : Continuous W)
    (hlocal : HasLoewnerLocalInitialVariationalFormula W)
    {t : Real} (ht : 0 <= t) {z : Complex}
    (hz : z ∈ loewnerUnswallowedDomain W t) :
    exists c : Complex, c ≠ 0 /\
      HasDerivAt (loewnerMaximalMaps W t) c z := by
  let delta : Real := (loewnerMaximalMaps W t z).im
  have hdelta : 0 < delta :=
    mem_upperHalfPlane.mp (loewnerMaximalMaps_mem_upperHalfPlane hz)
  obtain ⟨n, hn⟩ := exists_nat_gt (16 * t / delta ^ 2)
  have hquot : 0 <= 16 * t / delta ^ 2 := by positivity
  have hn0 : 0 < (n : Real) := hquot.trans_lt hn
  let u : Real := t / (n : Real)
  have hu : 0 <= u := by dsimp [u]; positivity
  have hnu : (n : Real) * u = t := by
    dsimp [u]
    field_simp
  have hushort : u < delta ^ 2 / 16 := by
    rw [div_lt_iff₀ hn0]
    have hmul : 16 * t < (n : Real) * delta ^ 2 :=
      (div_lt_iff₀ (sq_pos_of_pos hdelta)).mp hn
    nlinarith
  have htime (k : Nat) (hk : k <= n) :
      0 <= (k : Real) * u ∧ (k : Real) * u <= t := by
    refine ⟨mul_nonneg (Nat.cast_nonneg k) hu, ?_⟩
    rw [<- hnu]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hu
  have hsurvives (k : Nat) (hk : k <= n) :
      z ∈ loewnerUnswallowedDomain W ((k : Real) * u) :=
    loewnerUnswallowedDomain_antitoneOn W (htime k hk).1 ht
      (htime k hk).2 hz
  have hind : forall k : Nat, k <= n ->
      exists c : Complex, c ≠ 0 /\
        HasDerivAt (loewnerMaximalMaps W ((k : Real) * u)) c z := by
    intro k
    induction k with
    | zero =>
        intro _
        refine ⟨1, one_ne_zero, ?_⟩
        simpa using loewnerMaximalMaps_hasDerivAt_initial_zero hW hz.1
    | succ k ih =>
        intro hkn
        have hk : k <= n := (Nat.le_succ k).trans hkn
        obtain ⟨c, hc, hderiv⟩ := ih hk
        let s : Real := (k : Real) * u
        let y : Complex := loewnerMaximalMaps W s z
        have hs : 0 <= s := (htime k hk).1
        have hstepTime : ((k + 1 : Nat) : Real) * u = s + u := by
          dsimp [s]
          rw [Nat.cast_add, Nat.cast_one]
          ring
        have hznext : z ∈ loewnerUnswallowedDomain W (s + u) := by
          rw [<- hstepTime]
          exact hsurvives (k + 1) hkn
        have hysurvives : y ∈
            loewnerUnswallowedDomain (fun r => W (s + r)) u :=
          loewnerMaximalMaps_mem_shiftedUnswallowedDomain hs hu hznext
        have hy : y ∈ upperHalfPlane := hysurvives.1
        have him : delta <= y.im := by
          exact loewnerMaximalCurve_im_antitoneOn
            (hsurvives k hk).2 hz.2 (htime k hk).2
        have hshort : u < y.im ^ 2 / 16 := by
          calc
            u < delta ^ 2 / 16 := hushort
            _ <= y.im ^ 2 / 16 := by gcongr
        have hlocalDeriv := hlocal s u y hu hy hshort
        have hderivS : HasDerivAt (loewnerMaximalMaps W s) c z := by
          simpa [s] using hderiv
        have hcomp : HasDerivAt
            (fun w => loewnerMaximalMaps (fun r => W (s + r)) u
              (loewnerMaximalMaps W s w))
            (loewnerInitialJacobian (fun r => W (s + r)) u y * c) z :=
          by simpa [Function.comp_def] using hlocalDeriv.comp z hderivS
        have heq : loewnerMaximalMaps W (s + u) =ᶠ[nhds z]
            (fun w => loewnerMaximalMaps (fun r => W (s + r)) u
              (loewnerMaximalMaps W s w)) := by
          filter_upwards [
            (isOpen_loewnerUnswallowedDomain hW (add_nonneg hs hu)).mem_nhds
              hznext] with w hw
          exact loewnerMaximalMaps_flow hs hu hw
        refine ⟨loewnerInitialJacobian (fun r => W (s + r)) u y * c,
          mul_ne_zero (loewnerInitialJacobian_ne_zero _ _ _) hc, ?_⟩
        rw [hstepTime]
        exact hcomp.congr_of_eventuallyEq heq
  obtain ⟨c, hc, hderiv⟩ := hind n le_rfl
  rw [hnu] at hderiv
  exact ⟨c, hc, hderiv⟩



theorem loewnerMaximalMaps_differentiableOn_of_localVariational
    {W : Real -> Real} (hW : Continuous W)
    (hlocal : HasLoewnerLocalInitialVariationalFormula W)
    {t : Real} (ht : 0 <= t) :
    DifferentiableOn Complex (loewnerMaximalMaps W t)
      (loewnerUnswallowedDomain W t) := by
  intro z hz
  obtain ⟨c, _hc, hderiv⟩ :=
    exists_loewnerMaximalMaps_hasDerivAt_ne_zero_of_localVariational
      hW hlocal ht hz
  exact hderiv.differentiableAt.differentiableWithinAt




theorem loewnerMaximalMaps_conformalAt_of_localVariational
    {W : Real -> Real} (hW : Continuous W)
    (hlocal : HasLoewnerLocalInitialVariationalFormula W)
    {t : Real} (ht : 0 <= t) {z : Complex}
    (hz : z ∈ loewnerUnswallowedDomain W t) :
    ConformalAt (loewnerMaximalMaps W t) z := by
  obtain ⟨c, hc, hderiv⟩ :=
    exists_loewnerMaximalMaps_hasDerivAt_ne_zero_of_localVariational
      hW hlocal ht hz
  apply hderiv.differentiableAt.conformalAt
  rw [hderiv.deriv]
  exact hc



theorem loewnerMaximalMaps_conformalOn_of_localVariational
    {W : Real -> Real} (hW : Continuous W)
    (hlocal : HasLoewnerLocalInitialVariationalFormula W)
    {t : Real} (ht : 0 <= t) :
    forall z, z ∈ loewnerUnswallowedDomain W t ->
      ConformalAt (loewnerMaximalMaps W t) z := by
  intro z hz
  exact loewnerMaximalMaps_conformalAt_of_localVariational
    hW hlocal ht hz



theorem exists_loewnerMaximalMaps_hasDerivAt_ne_zero
    {W : Real -> Real} (hW : Continuous W)
    {t : Real} (ht : 0 <= t) {z : Complex}
    (hz : z ∈ loewnerUnswallowedDomain W t) :
    exists c : Complex, c ≠ 0 /\
      HasDerivAt (loewnerMaximalMaps W t) c z :=
  exists_loewnerMaximalMaps_hasDerivAt_ne_zero_of_localVariational
    hW (hasLoewnerLocalInitialVariationalFormula hW) ht hz



theorem loewnerMaximalMaps_differentiableOn
    {W : Real -> Real} (hW : Continuous W)
    {t : Real} (ht : 0 <= t) :
    DifferentiableOn Complex (loewnerMaximalMaps W t)
      (loewnerUnswallowedDomain W t) :=
  loewnerMaximalMaps_differentiableOn_of_localVariational
    hW (hasLoewnerLocalInitialVariationalFormula hW) ht



theorem loewnerMaximalMaps_conformalAt
    {W : Real -> Real} (hW : Continuous W)
    {t : Real} (ht : 0 <= t) {z : Complex}
    (hz : z ∈ loewnerUnswallowedDomain W t) :
    ConformalAt (loewnerMaximalMaps W t) z :=
  loewnerMaximalMaps_conformalAt_of_localVariational
    hW (hasLoewnerLocalInitialVariationalFormula hW) ht hz



theorem loewnerMaximalMaps_conformalOn
    {W : Real -> Real} (hW : Continuous W)
    {t : Real} (ht : 0 <= t) :
    forall z, z ∈ loewnerUnswallowedDomain W t ->
      ConformalAt (loewnerMaximalMaps W t) z := by
  intro z hz
  exact loewnerMaximalMaps_conformalAt hW ht hz

end

end StatMech.SLE
