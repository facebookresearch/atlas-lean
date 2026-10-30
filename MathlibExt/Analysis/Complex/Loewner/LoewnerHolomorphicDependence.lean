/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.Complex.Loewner.LoewnerMaximal
public import Mathlib.Analysis.Complex.Conformal

/-!
# Holomorphy and conformality of the Loewner maps

For a continuous driving function `W` and `t ≥ 0`, the maximal Loewner map
`g_t = loewnerMaximalMaps W t` is complex differentiable with nonzero derivative at every point of
the unswallowed domain `H_t = loewnerUnswallowedDomain W t`, hence holomorphic and conformal there
(`loewnerMaximalMaps_differentiableOn`, `loewnerMaximalMaps_conformalAt`). Together with
`loewnerMaximalMaps_bijOn_upperHalfPlane` (in `LoewnerMaximal`) this shows that `g_t` is a
conformal bijection `H_t → ℍ`. These results are unconditional.

The proof first treats short times `u < (Im z)² / 16`, where the flow is given by a local
Picard–Lindelöf chart: the difference quotient of two solutions satisfies a linear ODE, solved
explicitly by `linearODE_terminal_eq_initial_mul_exp_integral`, and dominated convergence gives
`g_u'(z) = exp ∫₀ᵘ -2 / (g_s(z) - W_s)² ds` (`loewnerInitialJacobian`). General times follow by
composing short-time maps of shifted drivers through the flow property.

## Main definitions

* `loewnerInitialVariationalCoefficient`, `loewnerInitialJacobian`: the variational equation and
  its solution `exp ∫ -2/(g_s(z) - W_s)²`.
* `HasLoewnerLocalInitialVariationalFormula W`: the short-time derivative formula for every
  time-shift of `W`; proved for continuous `W` (`hasLoewnerLocalInitialVariationalFormula`).

## Main results

* `loewnerMaximalMaps_hasDerivAt_of_lt_im_sq_div_sixteen`: `g_u'(z) = loewnerInitialJacobian W u z`
  for short times.
* `exists_loewnerMaximalMaps_hasDerivAt_ne_zero`, `loewnerMaximalMaps_differentiableOn`,
  `loewnerMaximalMaps_conformalAt`: `g_t` is holomorphic with nonvanishing derivative on `H_t`.

## References

* G. F. Lawler, *Conformally Invariant Processes in the Plane*, Mathematical Surveys and Monographs
  114, Amer. Math. Soc., 2005, Chapter 4.
-/

@[expose] public section

open Complex Set Metric Filter Topology
open UpperHalfPlane (upperHalfPlaneSet isOpen_upperHalfPlaneSet)
open scoped Interval

namespace StatMech.SLE

noncomputable section

/-- Explicit solution of the scalar linear ODE `f' = a f` on `[0, T]`:
`f T = f 0 · exp ∫₀ᵀ a`. -/
theorem linearODE_terminal_eq_initial_mul_exp_integral
    {T : ℝ} (hT : 0 ≤ T) {a f : ℝ → ℂ}
    (ha : ContinuousOn a (Icc (0 : ℝ) T))
    (hf : ContinuousOn f (Icc (0 : ℝ) T))
    (hderiv : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt f (a t * f t) (Icc (0 : ℝ) T) t) :
    f T = f 0 * Complex.exp (∫ s in (0 : ℝ)..T, a s) := by
  rcases hT.eq_or_lt with rfl | hTpos
  · simp
  let A : ℝ → ℂ := fun t => ∫ s in (0 : ℝ)..t, a s
  let r : ℝ → ℂ := fun t => Complex.exp (-A t) * f t
  have hA : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt A (a t) (Icc (0 : ℝ) T) t := by
    intro t ht
    let _ : Fact (t ∈ Icc (0 : ℝ) T) := ⟨ht⟩
    apply intervalIntegral.integral_hasDerivWithinAt_right
    · apply ContinuousOn.intervalIntegrable
      exact ha.mono (by
        rw [uIcc_of_le ht.1]
        exact Icc_subset_Icc_right ht.2)
    · exact ha.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t
    · exact ha t ht
  have hr : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt r 0 (Icc (0 : ℝ) T) t := by
    intro t ht
    have hexp : HasDerivWithinAt (fun s => Complex.exp (-A s))
        (Complex.exp (-A t) * (-a t)) (Icc (0 : ℝ) T) t := by
      simpa only [Function.comp_def, Pi.neg_apply] using
        (Complex.hasDerivAt_exp (-A t)).comp_hasDerivWithinAt t (hA t ht).neg
    dsimp only [r]
    convert hexp.mul (hderiv t ht) using 1
    all_goals ring
  have hrdiff : DifferentiableOn ℝ r (Icc (0 : ℝ) T) :=
    fun t ht => (hr t ht).differentiableWithinAt
  have hrfderiv : ∀ t ∈ Icc (0 : ℝ) T,
      fderivWithin ℝ r (Icc (0 : ℝ) T) t = 0 := by
    intro t ht
    simpa using (hr t ht).hasFDerivWithinAt.fderivWithin
      ((uniqueDiffOn_Icc hTpos).uniqueDiffWithinAt ht)
  have hconst : r 0 = r T :=
    (convex_Icc (0 : ℝ) T).is_const_of_fderivWithin_eq_zero
      hrdiff hrfderiv ⟨le_rfl, hTpos.le⟩ ⟨hTpos.le, le_rfl⟩
  have hconst' : f 0 = Complex.exp (-(∫ s in (0 : ℝ)..T, a s)) * f T := by
    simpa [r, A] using hconst
  calc
    f T = Complex.exp (∫ s in (0 : ℝ)..T, a s) *
        (Complex.exp (-(∫ s in (0 : ℝ)..T, a s)) * f T) := by
      rw [← mul_assoc, ← Complex.exp_add]
      simp
    _ = Complex.exp (∫ s in (0 : ℝ)..T, a s) * f 0 := by rw [← hconst']
    _ = f 0 * Complex.exp (∫ s in (0 : ℝ)..T, a s) := mul_comm _ _

/-- The derivative of the Loewner vector field `2 / (z - W_t)` in `z` is `-2 / (z - W_t)²`. -/
theorem loewnerField_hasDerivAt_initial
    (W : ℝ → ℝ) (t : ℝ) {z : ℂ}
    (hz : z ≠ (W t : ℂ)) :
    HasDerivAt (loewnerField W t)
      (-2 / (z - (W t : ℂ)) ^ 2) z := by
  have hden : z - (W t : ℂ) ≠ 0 := sub_ne_zero.mpr hz
  rw [show loewnerField W t = fun w => 2 / (w - (W t : ℂ)) from
    funext (loewnerField_apply W t)]
  simpa [hden, Pi.div_def] using
    (hasDerivAt_const z (2 : ℂ)).div
      ((hasDerivAt_id z).sub_const (W t : ℂ)) hden

/-- The coefficient `-2 / (g_s(z) - W_s)²` of the variational equation along the flow from `z`. -/
def loewnerInitialVariationalCoefficient
    (W : ℝ → ℝ) (z : ℂ) (s : ℝ) : ℂ :=
  -2 / (loewnerMaximalMaps W s z - (W s : ℂ)) ^ 2

/-- `exp ∫₀ᵗ -2 / (g_s(z) - W_s)² ds`, the derivative of `g_t` at `z`. -/
def loewnerInitialJacobian
    (W : ℝ → ℝ) (t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp
    (∫ s in (0 : ℝ)..t, loewnerInitialVariationalCoefficient W z s)

/-- The Jacobian never vanishes. -/
theorem loewnerInitialJacobian_ne_zero
    (W : ℝ → ℝ) (t : ℝ) (z : ℂ) :
    loewnerInitialJacobian W t z ≠ 0 := by
  exact Complex.exp_ne_zero _

@[simp] theorem loewnerInitialJacobian_zero
    (W : ℝ → ℝ) (z : ℂ) :
    loewnerInitialJacobian W 0 z = 1 := by
  simp [loewnerInitialJacobian]

/-- Short-time derivative formula: for `0 ≤ u < (Im z)² / 16`, `g_u` is complex differentiable at
`z` with derivative `loewnerInitialJacobian W u z`. -/
theorem loewnerMaximalMaps_hasDerivAt_of_lt_im_sq_div_sixteen
    {W : ℝ → ℝ} (hW : Continuous W) {u : ℝ} (hu : 0 ≤ u)
    {z : ℂ} (hz : z ∈ upperHalfPlaneSet) (hshort : u < z.im ^ 2 / 16) :
    HasDerivAt (loewnerMaximalMaps W u) (loewnerInitialJacobian W u z) z := by
  have hzpos : 0 < z.im := mem_upperHalfPlane.mp hz
  let E : ℝ := z.im ^ 2 / 16
  let delta : ℝ := z.im / 2
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
  have htimeSubset : Icc (0 : ℝ) E ⊆ Icc (-E) E := by
    intro t ht
    exact ⟨(neg_nonpos.mpr hE.le).trans ht.1, ht.2⟩
  let g : ∀ w : ℂ, w ∈ closedBall z (z.im / 4) →
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
  have hmaximal (w : ℂ) (hw : w ∈ closedBall z (z.im / 4))
      (t : ℝ) (ht0 : 0 ≤ t) (htE : t < E) :
      loewnerMaximalMaps W t w = alpha w t := by
    simpa [loewnerMaximalMaps] using
      loewnerMaximalCurve_eq_forwardSolution hE (g w hw) ⟨ht0, htE⟩
  have hden (w : ℂ) (hw : w ∈ closedBall z (z.im / 4)) (t : ℝ) :
      alpha w t - (W t : ℂ) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    have himzero : (alpha w t).im = 0 := by
      simpa using congrArg Complex.im heq
    have him := mem_loewnerStrip.mp ((halpha' w hw).2.2 t)
    linarith
  let coeff : ℂ → ℝ → ℂ := fun w t =>
    -2 / ((alpha w t - (W t : ℂ)) * (alpha z t - (W t : ℂ)))
  have hfield (w : ℂ) (hw : w ∈ closedBall z (z.im / 4)) (t : ℝ) :
      loewnerField W t (alpha w t) - loewnerField W t (alpha z t) =
        coeff w t * (alpha w t - alpha z t) := by
    have h1 := hden w hw t
    have h2 := hden z hzball t
    dsimp only [coeff]
    simp only [loewnerField_apply]
    field_simp [h1, h2]
    ring
  have hcoeffContinuous (w : ℂ) (hw : w ∈ closedBall z (z.im / 4)) :
      ContinuousOn (coeff w) (Icc (0 : ℝ) u) := by
    have hsubE : Icc (0 : ℝ) u ⊆ Icc (0 : ℝ) E :=
      Icc_subset_Icc_right hshort.le
    have haw := (g w hw).continuousOn.mono hsubE
    have haz := (g z hzball).continuousOn.mono hsubE
    have hWcomplex : Continuous (fun t => (W t : ℂ)) :=
      Complex.continuous_ofReal.comp hW
    dsimp only [coeff]
    exact continuousOn_const.div
      ((haw.sub hWcomplex.continuousOn).mul (haz.sub hWcomplex.continuousOn))
      (fun t _ht => mul_ne_zero (hden w hw t) (hden z hzball t))
  have hnormDen (w : ℂ) (hw : w ∈ closedBall z (z.im / 4)) (t : ℝ) :
      delta ≤ ‖alpha w t - (W t : ℂ)‖ := by
    calc
      delta ≤ (alpha w t).im := mem_loewnerStrip.mp ((halpha' w hw).2.2 t)
      _ = (alpha w t - (W t : ℂ)).im := by simp
      _ ≤ ‖alpha w t - (W t : ℂ)‖ := Complex.im_le_norm _
  have hcoeffBound (w : ℂ) (hw : w ∈ closedBall z (z.im / 4)) (t : ℝ) :
      ‖coeff w t‖ ≤ 2 / delta ^ 2 := by
    have hprod : delta * delta ≤
        ‖alpha w t - (W t : ℂ)‖ * ‖alpha z t - (W t : ℂ)‖ :=
      mul_le_mul (hnormDen w hw t) (hnormDen z hzball t)
        hdelta.le (norm_nonneg _)
    dsimp only [coeff]
    rw [norm_div, norm_neg, norm_ofNat, norm_mul]
    simpa [pow_two] using
      div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 2 by norm_num)
        (mul_pos hdelta hdelta) hprod
  have hcoeffTendsto (t : ℝ) (ht : t ∈ Icc (0 : ℝ) u) :
      Tendsto (fun w => coeff w t) (nhds z) (nhds (coeff z t)) := by
    have htFull : t ∈ Icc (-E) E := by
      exact ⟨by linarith [ht.1], ht.2.trans hshort.le⟩
    have hat : ContinuousAt (fun w => alpha w t) z :=
      ((hC' t htFull).continuousOn z hzball).continuousAt
        (closedBall_mem_nhds z hradius)
    have hprod : ContinuousAt (fun w =>
        (alpha w t - (W t : ℂ)) * (alpha z t - (W t : ℂ))) z :=
      (hat.sub continuousAt_const).mul continuousAt_const
    have hprodne :
        (alpha z t - (W t : ℂ)) * (alpha z t - (W t : ℂ)) ≠ 0 :=
      mul_ne_zero (hden z hzball t) (hden z hzball t)
    simpa only [coeff, Pi.div_def] using (continuousAt_const.div hprod hprodne).tendsto
  have hintegral : Tendsto (fun w => ∫ t in (0 : ℝ)..u, coeff w t)
      (nhds z) (nhds (∫ t in (0 : ℝ)..u, coeff z t)) := by
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
  have hdiff (w : ℂ) (hw : w ∈ closedBall z (z.im / 4)) :
      alpha w u - alpha z u =
        (w - z) * Complex.exp (∫ t in (0 : ℝ)..u, coeff w t) := by
    have hsubE : Icc (0 : ℝ) u ⊆ Icc (0 : ℝ) E :=
      Icc_subset_Icc_right hshort.le
    have hdiffContinuous : ContinuousOn (fun t => alpha w t - alpha z t)
        (Icc (0 : ℝ) u) :=
      ((g w hw).continuousOn.mono hsubE).sub ((g z hzball).continuousOn.mono hsubE)
    have hdiffDeriv : ∀ t ∈ Icc (0 : ℝ) u,
        HasDerivWithinAt (fun s => alpha w s - alpha z s)
          (coeff w t * (alpha w t - alpha z t)) (Icc (0 : ℝ) u) t := by
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
        Complex.exp (∫ t in (0 : ℝ)..u, coeff w t))
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
      (fun w => Complex.exp (∫ t in (0 : ℝ)..u, coeff w t))
      (nhdsWithin z ({z}ᶜ))
      (nhds (Complex.exp (∫ t in (0 : ℝ)..u, coeff z t))) :=
    (Complex.continuous_exp.continuousAt.tendsto.comp hintegral).mono_left inf_le_left
  have hderiv : HasDerivAt (loewnerMaximalMaps W u)
      (Complex.exp (∫ t in (0 : ℝ)..u, coeff z t)) z :=
    hasDerivAt_iff_tendsto_slope.mpr
      (hexpTendsto.congr' (hslope.mono fun _ hw => hw.symm))
  have hintegralEq : (∫ t in (0 : ℝ)..u, coeff z t) =
      ∫ t in (0 : ℝ)..u, loewnerInitialVariationalCoefficient W z t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) u := by
      simpa [uIcc_of_le hu] using ht
    dsimp only [coeff, loewnerInitialVariationalCoefficient]
    rw [hmaximal z hzball t htIcc.1 (htIcc.2.trans_lt hshort)]
    simp only [pow_two]
  simpa [loewnerInitialJacobian, hintegralEq] using hderiv

/-- `g_0` has derivative `1` on `ℍ`. -/
theorem loewnerMaximalMaps_hasDerivAt_initial_zero
    {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ}
    (hz : z ∈ upperHalfPlaneSet) :
    HasDerivAt (loewnerMaximalMaps W 0) 1 z := by
  apply (hasDerivAt_id z).congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
  simpa using loewnerMaximalMaps_zero hW hw

/-- The short-time derivative formula holds for every time-shift `r ↦ W (s + r)` of `W`. -/
def HasLoewnerLocalInitialVariationalFormula (W : ℝ → ℝ) : Prop :=
  ∀ (s u : ℝ) (z : ℂ), 0 ≤ u → z ∈ upperHalfPlaneSet →
    u < z.im ^ 2 / 16 →
    HasDerivAt (loewnerMaximalMaps (fun r => W (s + r)) u)
      (loewnerInitialJacobian (fun r => W (s + r)) u z) z

/-- The short-time derivative formula holds for every continuous driving function. -/
theorem hasLoewnerLocalInitialVariationalFormula
    {W : ℝ → ℝ} (hW : Continuous W) :
    HasLoewnerLocalInitialVariationalFormula W := by
  intro s u z hu hz hshort
  exact loewnerMaximalMaps_hasDerivAt_of_lt_im_sq_div_sixteen
    (hW.comp (continuous_const.add continuous_id)) hu hz hshort

/-- Given the short-time formula, `g_t` has a nonzero complex derivative at every point of
`H_t`. -/
theorem exists_loewnerMaximalMaps_hasDerivAt_ne_zero_of_localVariational
    {W : ℝ → ℝ} (hW : Continuous W)
    (hlocal : HasLoewnerLocalInitialVariationalFormula W)
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ loewnerUnswallowedDomain W t) :
    ∃ c : ℂ, c ≠ 0 ∧
      HasDerivAt (loewnerMaximalMaps W t) c z := by
  let delta : ℝ := (loewnerMaximalMaps W t z).im
  have hdelta : 0 < delta :=
    mem_upperHalfPlane.mp (loewnerMaximalMaps_mem_upperHalfPlane hz)
  obtain ⟨n, hn⟩ := exists_nat_gt (16 * t / delta ^ 2)
  have hquot : 0 ≤ 16 * t / delta ^ 2 := by positivity
  have hn0 : 0 < (n : ℝ) := hquot.trans_lt hn
  let u : ℝ := t / (n : ℝ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hnu : (n : ℝ) * u = t := by
    dsimp [u]
    field_simp
  have hushort : u < delta ^ 2 / 16 := by
    rw [div_lt_iff₀ hn0]
    have hmul : 16 * t < (n : ℝ) * delta ^ 2 :=
      (div_lt_iff₀ (sq_pos_of_pos hdelta)).mp hn
    nlinarith
  have htime (k : Nat) (hk : k ≤ n) :
      0 ≤ (k : ℝ) * u ∧ (k : ℝ) * u ≤ t := by
    refine ⟨mul_nonneg (Nat.cast_nonneg k) hu, ?_⟩
    rw [← hnu]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hu
  have hsurvives (k : Nat) (hk : k ≤ n) :
      z ∈ loewnerUnswallowedDomain W ((k : ℝ) * u) :=
    loewnerUnswallowedDomain_antitoneOn W (htime k hk).1 ht
      (htime k hk).2 hz
  have hind : ∀ k : Nat, k ≤ n →
      ∃ c : ℂ, c ≠ 0 ∧
        HasDerivAt (loewnerMaximalMaps W ((k : ℝ) * u)) c z := by
    intro k
    induction k with
    | zero =>
        intro _
        refine ⟨1, one_ne_zero, ?_⟩
        simpa using loewnerMaximalMaps_hasDerivAt_initial_zero hW hz.1
    | succ k ih =>
        intro hkn
        have hk : k ≤ n := (Nat.le_succ k).trans hkn
        obtain ⟨c, hc, hderiv⟩ := ih hk
        let s : ℝ := (k : ℝ) * u
        let y : ℂ := loewnerMaximalMaps W s z
        have hs : 0 ≤ s := (htime k hk).1
        have hstepTime : ((k + 1 : Nat) : ℝ) * u = s + u := by
          dsimp [s]
          rw [Nat.cast_add, Nat.cast_one]
          ring
        have hznext : z ∈ loewnerUnswallowedDomain W (s + u) := by
          rw [← hstepTime]
          exact hsurvives (k + 1) hkn
        have hysurvives : y ∈
            loewnerUnswallowedDomain (fun r => W (s + r)) u :=
          loewnerMaximalMaps_mem_shiftedUnswallowedDomain hs hu hznext
        have hy : y ∈ upperHalfPlaneSet := hysurvives.1
        have him : delta ≤ y.im := by
          exact loewnerMaximalCurve_im_antitoneOn
            (hsurvives k hk).2 hz.2 (htime k hk).2
        have hshort : u < y.im ^ 2 / 16 := by
          calc
            u < delta ^ 2 / 16 := hushort
            _ ≤ y.im ^ 2 / 16 := by gcongr
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

/-- Given the short-time formula, `g_t` is holomorphic on `H_t`. -/
theorem loewnerMaximalMaps_differentiableOn_of_localVariational
    {W : ℝ → ℝ} (hW : Continuous W)
    (hlocal : HasLoewnerLocalInitialVariationalFormula W)
    {t : ℝ} (ht : 0 ≤ t) :
    DifferentiableOn ℂ (loewnerMaximalMaps W t)
      (loewnerUnswallowedDomain W t) := by
  intro z hz
  obtain ⟨c, _hc, hderiv⟩ :=
    exists_loewnerMaximalMaps_hasDerivAt_ne_zero_of_localVariational
      hW hlocal ht hz
  exact hderiv.differentiableAt.differentiableWithinAt

/-- Given the short-time formula, `g_t` is conformal at every point of `H_t`. -/
theorem loewnerMaximalMaps_conformalAt_of_localVariational
    {W : ℝ → ℝ} (hW : Continuous W)
    (hlocal : HasLoewnerLocalInitialVariationalFormula W)
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ loewnerUnswallowedDomain W t) :
    ConformalAt (loewnerMaximalMaps W t) z := by
  obtain ⟨c, hc, hderiv⟩ :=
    exists_loewnerMaximalMaps_hasDerivAt_ne_zero_of_localVariational
      hW hlocal ht hz
  apply hderiv.differentiableAt.conformalAt
  rw [hderiv.deriv]
  exact hc

/-- `g_t` has a nonzero complex derivative at every point of `H_t` (continuous `W`). -/
theorem exists_loewnerMaximalMaps_hasDerivAt_ne_zero
    {W : ℝ → ℝ} (hW : Continuous W)
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ loewnerUnswallowedDomain W t) :
    ∃ c : ℂ, c ≠ 0 ∧
      HasDerivAt (loewnerMaximalMaps W t) c z :=
  exists_loewnerMaximalMaps_hasDerivAt_ne_zero_of_localVariational
    hW (hasLoewnerLocalInitialVariationalFormula hW) ht hz

/-- `g_t` is holomorphic on the unswallowed domain `H_t` (continuous `W`). -/
theorem loewnerMaximalMaps_differentiableOn
    {W : ℝ → ℝ} (hW : Continuous W)
    {t : ℝ} (ht : 0 ≤ t) :
    DifferentiableOn ℂ (loewnerMaximalMaps W t)
      (loewnerUnswallowedDomain W t) :=
  loewnerMaximalMaps_differentiableOn_of_localVariational
    hW (hasLoewnerLocalInitialVariationalFormula hW) ht

/-- `g_t` is conformal at every point of `H_t` (continuous `W`). -/
theorem loewnerMaximalMaps_conformalAt
    {W : ℝ → ℝ} (hW : Continuous W)
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ loewnerUnswallowedDomain W t) :
    ConformalAt (loewnerMaximalMaps W t) z :=
  loewnerMaximalMaps_conformalAt_of_localVariational
    hW (hasLoewnerLocalInitialVariationalFormula hW) ht hz

end

end StatMech.SLE
