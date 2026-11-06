/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Winding numbers of closed piecewise `C¹` paths

A path `γ` is piecewise `C¹` (`Path.IsPiecewiseC1`) if it is `C¹` on each closed piece of a finite
subdivision of `[0, 1]`. For a closed path `γ : Path x x` in `ℂ`, the winding number around `z` is
`Complex.windingNumber γ z = (2πi)⁻¹ ∫_γ (ζ - z)⁻¹ dζ`, where `∫_γ φ(ζ) dζ` is Mathlib's curve
integral `∫ᶜ ζ in γ, φ ζ • ContinuousLinearMap.id ℂ ℂ` of the `1`-form `φ(ζ) dζ`.

For a closed piecewise `C¹` path the winding number is an integer off the path
(`Complex.exists_windingNumber_eq_intCast`), locally constant off the path
(`Complex.eventually_windingNumber_eq`), hence constant on every preconnected set missing the path
(`Complex.windingNumber_eq_of_isPreconnected`), and zero near infinity
(`Complex.eventually_windingNumber_eq_zero`) and on the unbounded components of the complement of
the path (`Complex.windingNumber_eq_zero_of_not_isBounded`).

Supporting results on curve integrals along a piecewise `C¹` path `γ`:
* holomorphic dependence on a parameter (`Complex.differentiableOn_curveIntegral`);
* the Cauchy-type integral `z ↦ ∫_γ φ(ζ) / (ζ - z) dζ` is holomorphic off `γ`
  (`Complex.differentiableOn_curveIntegral_div_sub`) and tends to `0` at infinity
  (`Complex.tendsto_curveIntegral_div_sub_cocompact`);
* for `z` off a closed path, `∫_γ dslope f z ζ dζ = ∫_γ f ζ / (ζ - z) dζ - 2πi n(γ, z) f z`
  (`Complex.curveIntegral_dslope_of_notMem`).

Circles are closed `C¹` paths (`Complex.circlePath`); their curve integrals are Mathlib's circle
integrals (`Complex.curveIntegral_circlePath`) and their winding numbers are `1` inside and `0`
outside.

Mathlib has curve integrals along paths, but no piecewise `C¹` paths, no analytic winding number
of a path in `ℂ` (only the covering-space `AddCircle.windingNumber`), and no link between
`curveIntegral` and `circleIntegral`.

Rubric-guided revision of the winding number of v1 ComplexVariables Lecture 13
(`ClosedCurve.windingNumber`, with its integrality and local constancy, in
`v1/Atlas/ComplexVariables/code/Lecture13.lean` at commit
`6191bf1ba03d204784385ef5be2472be88035b93`). The archived winding number was defined on the
project-local `ClosedCurve`, a single `C¹` parametrization whose regularity used `deriv` rather
than a derivative within the parameter interval; it is now defined on Mathlib paths through
Mathlib's `curveIntegral`, and the integrality argument (the `exp (-∫)` trick, adapted from the
archive) runs off a countable set so that it covers piecewise `C¹` paths. The archived
formalization and its original license/provenance remain in `v1/` (the original license text is
`v1/LICENSE`).
-/

set_option autoImplicit false

open Filter Function MeasureTheory Metric Set Topology
open scoped Interval Real

namespace Path

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x y : E}

/-- A path `γ` is *piecewise `C¹`* if some subdivision `0 = p 0 ≤ p 1 ≤ ⋯ ≤ p n = 1` of `[0, 1]`
makes `γ` continuously differentiable on each closed piece `[p k, p (k + 1)]`, with one-sided
derivatives at the subdivision points. These are the curves of line integration in Ahlfors. -/
@[expose] public def IsPiecewiseC1 (γ : Path x y) : Prop :=
  ∃ (n : ℕ) (p : ℕ → ℝ), Monotone p ∧ p 0 = 0 ∧ p n = 1 ∧
    ∀ k < n, ContDiffOn ℝ 1 γ.extend (Icc (p k) (p (k + 1)))

/-- A path that is `C¹` on `[0, 1]` is piecewise `C¹`. -/
public theorem IsPiecewiseC1.of_contDiffOn {γ : Path x y}
    (h : ContDiffOn ℝ 1 γ.extend (Icc 0 1)) : γ.IsPiecewiseC1 :=
  ⟨1, fun k => k, Nat.mono_cast, Nat.cast_zero, Nat.cast_one, fun k hk => by
    obtain rfl : k = 0 := by omega
    simpa using h⟩

private theorem exists_mem_Ioo_of_notMem_range {p : ℕ → ℝ} {n : ℕ} (h0 : p 0 = 0) (hn : p n = 1)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (htp : t ∉ range p) :
    ∃ k < n, t ∈ Ioo (p k) (p (k + 1)) := by
  classical
  have hk : p (Nat.findGreatest (fun k => p k < t) n) < t :=
    Nat.findGreatest_spec (P := fun k => p k < t) (Nat.zero_le n) (by simpa [h0] using ht.1)
  have hkn : Nat.findGreatest (fun k => p k < t) n < n :=
    (Nat.findGreatest_le n).lt_of_ne fun h => by rw [h, hn] at hk; exact lt_asymm hk ht.2
  exact ⟨_, hkn, hk, lt_of_le_of_ne (not_lt.1 (Nat.findGreatest_is_greatest (Nat.lt_succ_self _)
    hkn)) fun h => htp ⟨_, h.symm⟩⟩

/-- The derivative of a piecewise `C¹` path is interval integrable on `[0, 1]`. -/
private theorem IsPiecewiseC1.intervalIntegrable_deriv {γ : Path x y} (hγ : γ.IsPiecewiseC1) :
    IntervalIntegrable (deriv γ.extend) volume 0 1 := by
  obtain ⟨n, p, hp, hp0, hp1, hpC⟩ := hγ
  have : IntervalIntegrable (deriv γ.extend) volume (p 0) (p n) :=
    IntervalIntegrable.trans_iterate fun k hk => by
      rcases (hp (Nat.le_succ k)).lt_or_eq with hlt | heq
      · refine (((hpC k hk).continuousOn_derivWithin (uniqueDiffOn_Icc hlt) le_rfl
          ).intervalIntegrable_of_Icc hlt.le).congr_uIoo fun u hu => ?_
        rw [uIoo_of_le hlt.le] at hu
        exact derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)
      · rw [heq]
  rwa [hp0, hp1] at this

/-- Off a countable set of parameters, a piecewise `C¹` path is differentiable with continuous
derivative. -/
private theorem IsPiecewiseC1.exists_countable_hasDerivAt {γ : Path x y}
    (hγ : γ.IsPiecewiseC1) :
    ∃ s : Set ℝ, s.Countable ∧ ∀ t ∈ Ioo (0 : ℝ) 1 \ s,
      HasDerivAt γ.extend (deriv γ.extend t) t ∧ ContinuousAt (deriv γ.extend) t := by
  obtain ⟨n, p, -, hp0, hp1, hpC⟩ := hγ
  refine ⟨range p, countable_range p, fun t ⟨ht, htp⟩ => ?_⟩
  obtain ⟨k, hk, htk⟩ := exists_mem_Ioo_of_notMem_range hp0 hp1 ht htp
  have hC : ContDiffOn ℝ 1 γ.extend (Ioo (p k) (p (k + 1))) :=
    (hpC k hk).mono Ioo_subset_Icc_self
  have hnhds : Ioo (p k) (p (k + 1)) ∈ 𝓝 t := isOpen_Ioo.mem_nhds htk
  exact ⟨((hC.differentiableOn one_ne_zero).differentiableAt hnhds).hasDerivAt,
    (hC.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).continuousAt hnhds⟩

end Path

namespace Complex

/-- The winding number `n(γ, z) = (2πi)⁻¹ ∫_γ (ζ - z)⁻¹ dζ` of a closed path `γ` around `z`. It is
meaningful for a piecewise `C¹` path and `z` off the path; otherwise the curve integral may take a
junk value. -/
@[expose] public noncomputable def windingNumber {x : ℂ} (γ : Path x x) (z : ℂ) : ℂ :=
  (2 * π * I)⁻¹ * ∫ᶜ ζ in γ, (ζ - z)⁻¹ • ContinuousLinearMap.id ℂ ℂ

/-! ### Curve integrals along a piecewise `C¹` path -/

section CurveIntegral

variable {x y : ℂ} {γ : Path x y}

private theorem extend_mem_range (γ : Path x y) (t : ℝ) : γ.extend t ∈ range γ := by
  rw [← γ.extend_range]
  exact mem_range_self t

private theorem continuousOn_sub_inv {s : Set ℂ} {z : ℂ} (hz : z ∉ s) :
    ContinuousOn (fun ζ => (ζ - z)⁻¹) s :=
  (continuousOn_id.sub continuousOn_const).inv₀ fun ζ hζ h0 =>
    hz ((sub_eq_zero.1 h0 : ζ = z) ▸ hζ)

private theorem curveIntegral_eq_integral (γ : Path x y) (φ : ℂ → ℂ) :
    ∫ᶜ ζ in γ, φ ζ • ContinuousLinearMap.id ℂ ℂ =
      ∫ t in 0..1, φ (γ.extend t) * deriv γ.extend t := by
  rw [curveIntegral_eq_intervalIntegral_deriv]
  simp

private theorem intervalIntegrable_comp_mul_deriv (hγ : γ.IsPiecewiseC1) {φ : ℂ → ℂ}
    (hφ : ContinuousOn φ (range γ)) :
    IntervalIntegrable (fun t => φ (γ.extend t) * deriv γ.extend t) volume 0 1 :=
  hγ.intervalIntegrable_deriv.continuousOn_mul
    (hφ.comp γ.continuous_extend.continuousOn fun t _ => extend_mem_range γ t)

private theorem norm_integral_comp_mul_deriv_le (hγ : γ.IsPiecewiseC1) {φ : ℂ → ℂ} {C : ℝ}
    (hC : ∀ ζ ∈ range γ, ‖φ ζ‖ ≤ C) :
    ‖∫ t in 0..1, φ (γ.extend t) * deriv γ.extend t‖ ≤
      C * ∫ t in 0..1, ‖deriv γ.extend t‖ := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Eventually.of_forall fun t _ => ?_) (hγ.intervalIntegrable_deriv.norm.const_mul C)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC _ (extend_mem_range γ t)) (norm_nonneg _)

/-- **Holomorphic dependence on a parameter.** If `Φ` is continuous on `U × γ` and holomorphic in
its first variable, then `z ↦ ∫_γ Φ(z, ζ) dζ` is holomorphic on `U`. -/
public theorem differentiableOn_curveIntegral (hγ : γ.IsPiecewiseC1) {U : Set ℂ} (hU : IsOpen U)
    {Φ : ℂ → ℂ → ℂ} (hΦc : ContinuousOn (uncurry Φ) (U ×ˢ range γ))
    (hΦd : ∀ ζ ∈ range γ, DifferentiableOn ℂ (Φ · ζ) U) :
    DifferentiableOn ℂ (fun z => ∫ᶜ ζ in γ, Φ z ζ • ContinuousLinearMap.id ℂ ℂ) U := by
  simp only [curveIntegral_eq_integral]
  intro z₀ hz₀
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  set r := ρ / 3 with hr_def
  have hr : 0 < r := by positivity
  have hsub : closedBall z₀ (2 * r) ⊆ U := (closedBall_subset_ball (by linarith)).trans hρU
  obtain ⟨C, hC⟩ := ((isCompact_closedBall z₀ (2 * r)).prod
    (isCompact_range γ.continuous)).exists_bound_of_continuousOn
      (hΦc.mono (prod_mono hsub subset_rfl))
  have hg' := hγ.intervalIntegrable_deriv
  have hcont : ∀ z ∈ U, ContinuousOn (Φ z) (range γ) := fun z hz =>
    hΦc.comp (continuousOn_const.prodMk continuousOn_id) fun ζ hζ => ⟨hz, hζ⟩
  have hcontI : ∀ z ∈ U, Continuous fun t => Φ z (γ.extend t) := fun z hz =>
    (hcont z hz).comp_continuous γ.continuous_extend (extend_mem_range γ)
  -- Cauchy's estimate bounds the derivative in the parameter near `z₀`.
  have hderiv : ∀ z ∈ ball z₀ r, ∀ ζ ∈ range γ, ‖deriv (Φ · ζ) z‖ ≤ C / r := by
    intro z hz ζ hζ
    have hzb : closedBall z r ⊆ closedBall z₀ (2 * r) :=
      closedBall_subset_closedBall' (by linarith [mem_ball.1 hz])
    exact norm_deriv_le_of_forall_mem_sphere_norm_le hr
      (((hΦd ζ hζ).mono hsub).diffContOnCl_ball hzb)
      fun w hw => hC (w, ζ) ⟨hzb (sphere_subset_closedBall hw), hζ⟩
  -- The derivative of the integrand is measurable, as a limit of difference quotients.
  have hF'meas : AEStronglyMeasurable
      (fun t => deriv (Φ · (γ.extend t)) z₀ * deriv γ.extend t) (volume.restrict (Ι 0 1)) := by
    refine AEStronglyMeasurable.mul ?_ hg'.def'.aestronglyMeasurable
    set h : ℕ → ℂ := fun n => ((r * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ) with h_def
    have hh : ∀ n, z₀ + h n ∈ U := fun n => hsub <| by
      simp only [h_def]
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_real,
        Real.norm_of_nonneg (by positivity)]
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [n.cast_nonneg (α := ℝ)]
      nlinarith
    have hlim : Tendsto h atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
        (Eventually.of_forall fun n => ?_)
      · simpa [h_def] using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul r).ofReal
      · exact ofReal_ne_zero.2 (by positivity : (0 : ℝ) < r * (1 / ((n : ℝ) + 1))).ne'
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n t => (h n)⁻¹ * (Φ (z₀ + h n) (γ.extend t) - Φ z₀ (γ.extend t)))
      (fun n => ?_) (Eventually.of_forall fun t => ?_)
    · exact (continuous_const.mul ((hcontI _ (hh n)).sub (hcontI z₀ hz₀))).aestronglyMeasurable
    · have := ((hΦd _ (extend_mem_range γ t)).differentiableAt
        (hU.mem_nhds hz₀)).hasDerivAt.tendsto_slope_zero
      simpa [Function.comp_def, smul_eq_mul] using this.comp hlim
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => Φ z (γ.extend t) * deriv γ.extend t)
    (F' := fun z t => deriv (Φ · (γ.extend t)) z * deriv γ.extend t)
    (bound := fun t => C / r * ‖deriv γ.extend t‖) (ball_mem_nhds z₀ hr)
    (eventually_of_mem (hU.mem_nhds hz₀) fun z hz =>
      (intervalIntegrable_comp_mul_deriv hγ (hcont z hz)).def'.aestronglyMeasurable)
    (intervalIntegrable_comp_mul_deriv hγ (hcont z₀ hz₀)) hF'meas
    (Eventually.of_forall fun t _ z hz => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hderiv z hz _ (extend_mem_range γ t)) (norm_nonneg _))
    (hg'.norm.const_mul _)
    (Eventually.of_forall fun t _ z hz =>
      ((hΦd _ (extend_mem_range γ t)).differentiableAt
        (hU.mem_nhds (hρU (ball_subset_ball (by linarith) hz)))).hasDerivAt.mul_const _)
  exact key.2.differentiableAt.differentiableWithinAt

/-- The Cauchy-type integral `z ↦ ∫_γ φ(ζ) / (ζ - z) dζ` is holomorphic off the path. -/
public theorem differentiableOn_curveIntegral_div_sub (hγ : γ.IsPiecewiseC1) {φ : ℂ → ℂ}
    (hφ : ContinuousOn φ (range γ)) :
    DifferentiableOn ℂ (fun z => ∫ᶜ ζ in γ, (φ ζ / (ζ - z)) • ContinuousLinearMap.id ℂ ℂ)
      (range γ)ᶜ :=
  differentiableOn_curveIntegral hγ (isCompact_range γ.continuous).isClosed.isOpen_compl
    (Φ := fun z ζ => φ ζ / (ζ - z))
    ((hφ.comp continuousOn_snd fun _ hp => hp.2).div₀
      (continuous_snd.sub continuous_fst).continuousOn fun _ hp h0 =>
        hp.1 (sub_eq_zero.1 h0 ▸ hp.2))
    fun ζ hζ z hz => ((differentiableAt_const _).fun_div
      ((differentiableAt_const ζ).sub differentiableAt_id)
      (sub_ne_zero.2 fun h : ζ = z => hz (h ▸ hζ))).differentiableWithinAt

/-- The Cauchy-type integral `∫_γ φ(ζ) / (ζ - z) dζ` tends to `0` as `z → ∞`. -/
public theorem tendsto_curveIntegral_div_sub_cocompact (hγ : γ.IsPiecewiseC1) {φ : ℂ → ℂ}
    (hφ : ContinuousOn φ (range γ)) :
    Tendsto (fun z => ∫ᶜ ζ in γ, (φ ζ / (ζ - z)) • ContinuousLinearMap.id ℂ ℂ) (cocompact ℂ)
      (𝓝 0) := by
  have hK : IsCompact (range γ) := isCompact_range γ.continuous
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hφ
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  set V := ∫ t in 0..1, ‖deriv γ.extend t‖
  have hlim : Tendsto (fun z : ℂ => ‖z‖ + -R) (cocompact ℂ) atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_norm_cocompact_atTop
  have h' : Tendsto (fun z : ℂ => max C 0 * V * (‖z‖ + -R)⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa using hlim.inv_tendsto_atTop.const_mul (max C 0 * V)
  refine squeeze_zero_norm' ?_ h'
  filter_upwards [hlim.eventually_gt_atTop 0] with z hz
  rw [curveIntegral_eq_integral]
  refine (norm_integral_comp_mul_deriv_le hγ (φ := fun ζ => φ ζ / (ζ - z))
    (C := max C 0 * (‖z‖ + -R)⁻¹) fun ζ hζ => ?_).trans_eq (by ring)
  have hζz : ‖z‖ + -R ≤ ‖ζ - z‖ := by
    rw [norm_sub_rev]
    linarith [norm_sub_norm_le z ζ, hR ζ hζ]
  rw [norm_div, div_eq_mul_inv]
  exact mul_le_mul (le_max_of_le_left (hC ζ hζ)) (inv_anti₀ hz hζz) (by positivity)
    (le_max_right _ _)

end CurveIntegral

/-! ### The winding number -/

section WindingNumber

variable {x : ℂ} {γ : Path x x}

/-- The winding integral `∫_γ (ζ - w)⁻¹ dζ` of a closed piecewise `C¹` path is an integer
multiple of `2πi`: `exp (-∫₀ᵗ γ'/(γ - w)) (γ t - w)` has derivative zero off a countable set. -/
private theorem exists_integral_eq_intCast_mul (hγ : γ.IsPiecewiseC1) {w : ℂ} (hw : w ∉ range γ) :
    ∃ n : ℤ, ∫ t in 0..1, (γ.extend t - w)⁻¹ * deriv γ.extend t = n * (2 * π * I) := by
  obtain ⟨s, hs, hd⟩ := hγ.exists_countable_hasDerivAt
  have hne : ∀ t, γ.extend t - w ≠ 0 := fun t h => hw (sub_eq_zero.1 h ▸ extend_mem_range γ t)
  have hk : IntervalIntegrable (fun t => (γ.extend t - w)⁻¹ * deriv γ.extend t) volume 0 1 :=
    intervalIntegrable_comp_mul_deriv hγ (continuousOn_sub_inv hw)
  set G : ℝ → ℂ := fun t => ∫ u in 0..t, (γ.extend u - w)⁻¹ * deriv γ.extend u
  have hGc : ContinuousOn G (Icc 0 1) := by
    simpa [uIcc_of_le zero_le_one] using
      intervalIntegral.continuousOn_primitive_interval' hk left_mem_uIcc
  have hΦc : ContinuousOn (fun t => exp (-G t) * (γ.extend t - w)) (Icc 0 1) :=
    (continuous_exp.comp_continuousOn hGc.neg).mul
      (γ.continuous_extend.sub continuous_const).continuousOn
  have hΦd : ∀ t ∈ Ioo (0 : ℝ) 1 \ s, HasDerivAt (fun t => exp (-G t) * (γ.extend t - w)) 0 t := by
    intro t ht
    obtain ⟨hgt, hg't⟩ := hd t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht.1
    have hkc : ContinuousAt (fun t => (γ.extend t - w)⁻¹ * deriv γ.extend t) t :=
      ((γ.continuous_extend.continuousAt.sub continuousAt_const).inv₀ (hne t)).mul hg't
    have hkm : StronglyMeasurableAtFilter (fun t => (γ.extend t - w)⁻¹ * deriv γ.extend t)
        (𝓝 t) volume := by
      refine ⟨Ioo 0 1, isOpen_Ioo.mem_nhds ht.1, ?_⟩
      have := hk.def'
      rw [uIoc_of_le zero_le_one] at this
      exact (this.mono_set Ioo_subset_Ioc_self).aestronglyMeasurable
    have hGd : HasDerivAt G ((γ.extend t - w)⁻¹ * deriv γ.extend t) t :=
      intervalIntegral.integral_hasDerivAt_right
        (hk.mono_set (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le ht'.1 ht'.2))) hkm hkc
    refine (hGd.neg.cexp.mul (hgt.sub_const w)).congr_deriv ?_
    linear_combination (-(exp (-G t) * deriv γ.extend t)) * inv_mul_cancel₀ (hne t)
  have hftc := integral_eq_of_hasDerivAt_off_countable_of_le
    (fun t => exp (-G t) * (γ.extend t - w)) (fun _ => (0 : ℂ)) zero_le_one hs hΦc hΦd
    intervalIntegrable_const
  have hG0 : G 0 = 0 := intervalIntegral.integral_same
  simp only [intervalIntegral.integral_zero, hG0, neg_zero, exp_zero, one_mul, Path.extend_zero,
    Path.extend_one] at hftc
  have h0 : x - w ≠ 0 := by simpa using hne 0
  have hexp : exp (-G 1) = 1 := mul_right_cancel₀ h0 (by linear_combination -hftc)
  obtain ⟨n, hn⟩ := exp_eq_one_iff.1 hexp
  refine ⟨-n, ?_⟩
  change G 1 = _
  push_cast
  linear_combination -hn

/-- The winding number of a closed piecewise `C¹` path around a point off the path is an
integer. -/
public theorem exists_windingNumber_eq_intCast (hγ : γ.IsPiecewiseC1) {z : ℂ} (hz : z ∉ range γ) :
    ∃ n : ℤ, windingNumber γ z = n := by
  obtain ⟨n, hn⟩ := exists_integral_eq_intCast_mul hγ hz
  refine ⟨n, ?_⟩
  rw [windingNumber, curveIntegral_eq_integral, hn, mul_comm (n : ℂ),
    inv_mul_cancel_left₀ two_pi_I_ne_zero]

private theorem differentiableOn_windingNumber (hγ : γ.IsPiecewiseC1) :
    DifferentiableOn ℂ (windingNumber γ) (range γ)ᶜ := by
  refine ((differentiableOn_curveIntegral_div_sub hγ (φ := fun _ => 1)
    continuousOn_const).const_mul (2 * π * I)⁻¹).congr fun z _ => ?_
  simp only [windingNumber, one_div]

/-- Off the path, the winding number of a closed piecewise `C¹` path is locally constant. -/
public theorem eventually_windingNumber_eq (hγ : γ.IsPiecewiseC1) {z₀ : ℂ} (hz₀ : z₀ ∉ range γ) :
    ∀ᶠ z in 𝓝 z₀, windingNumber γ z = windingNumber γ z₀ := by
  have hopen : IsOpen (range γ)ᶜ := (isCompact_range γ.continuous).isClosed.isOpen_compl
  have hcont : ContinuousAt (windingNumber γ) z₀ :=
    ((differentiableOn_windingNumber hγ).differentiableAt (hopen.mem_nhds hz₀)).continuousAt
  obtain ⟨n₀, hn₀⟩ := exists_windingNumber_eq_intCast hγ hz₀
  filter_upwards [hopen.mem_nhds hz₀, Metric.tendsto_nhds.mp hcont 1 one_pos] with z hz hdist
  obtain ⟨n, hn⟩ := exists_windingNumber_eq_intCast hγ hz
  rw [hn, hn₀] at hdist ⊢
  have h1 : |((n - n₀ : ℤ) : ℝ)| < 1 := by
    rwa [dist_eq_norm, ← Int.cast_sub, Complex.norm_intCast] at hdist
  have h2 : |n - n₀| < 1 := by exact_mod_cast h1
  rw [abs_lt] at h2
  have : n = n₀ := by omega
  rw [this]

/-- The winding number of a closed piecewise `C¹` path vanishes near infinity. -/
public theorem eventually_windingNumber_eq_zero (hγ : γ.IsPiecewiseC1) :
    ∀ᶠ z in cocompact ℂ, windingNumber γ z = 0 := by
  have htend : Tendsto (windingNumber γ) (cocompact ℂ) (𝓝 0) := by
    have := (tendsto_curveIntegral_div_sub_cocompact hγ (φ := fun _ => 1)
      continuousOn_const).const_mul (2 * π * I)⁻¹
    rw [mul_zero] at this
    refine this.congr fun z => ?_
    simp only [windingNumber, one_div]
  filter_upwards [(isCompact_range γ.continuous).compl_mem_cocompact,
    htend.eventually_mem (ball_mem_nhds 0 one_pos)] with z hz hlt
  obtain ⟨n, hn⟩ := exists_windingNumber_eq_intCast hγ hz
  rw [hn] at hlt ⊢
  rw [mem_ball_zero_iff, norm_intCast] at hlt
  have h1 : |n| < 1 := by exact_mod_cast hlt
  have h0 : n = 0 := by
    rw [abs_lt] at h1
    omega
  simp [h0]

/-- The winding number of a closed piecewise `C¹` path is constant on every preconnected set that
misses the path. -/
public theorem windingNumber_eq_of_isPreconnected (hγ : γ.IsPiecewiseC1) {S : Set ℂ}
    (hS : IsPreconnected S) (hSγ : S ⊆ (range γ)ᶜ) {z w : ℂ} (hz : z ∈ S) (hw : w ∈ S) :
    windingNumber γ w = windingNumber γ z := by
  have hopen : IsOpen (range γ)ᶜ := (isCompact_range γ.continuous).isClosed.isOpen_compl
  set U := {v | v ∉ range γ ∧ windingNumber γ v = windingNumber γ z}
  set V := {v | v ∉ range γ ∧ windingNumber γ v ≠ windingNumber γ z}
  have hUo : IsOpen U := isOpen_iff_mem_nhds.2 fun v hv => by
    filter_upwards [hopen.mem_nhds hv.1, eventually_windingNumber_eq hγ hv.1] with v' h1 h2
    exact ⟨h1, h2.trans hv.2⟩
  have hVo : IsOpen V := isOpen_iff_mem_nhds.2 fun v hv => by
    filter_upwards [hopen.mem_nhds hv.1, eventually_windingNumber_eq hγ hv.1] with v' h1 h2
    exact ⟨h1, fun h => hv.2 (h2.symm.trans h)⟩
  have hcover : S ⊆ U ∪ V := fun v hv => by
    by_cases h : windingNumber γ v = windingNumber γ z
    · exact Or.inl ⟨hSγ hv, h⟩
    · exact Or.inr ⟨hSγ hv, h⟩
  have hdisj : Disjoint U V := Set.disjoint_left.2 fun v hvU hvV => hvV.2 hvU.2
  exact (hS.subset_left_of_subset_union hUo hVo hdisj hcover ⟨z, hz, hSγ hz, rfl⟩ hw).2

/-- The winding number of a closed piecewise `C¹` path vanishes on the unbounded connected
components of the complement of the path. -/
public theorem windingNumber_eq_zero_of_not_isBounded (hγ : γ.IsPiecewiseC1) {z : ℂ}
    (hb : ¬Bornology.IsBounded (connectedComponentIn (range γ)ᶜ z)) : windingNumber γ z = 0 := by
  have hz : z ∈ (range γ)ᶜ := by
    by_contra hz
    rw [connectedComponentIn_eq_empty hz] at hb
    exact hb Bornology.isBounded_empty
  obtain ⟨K, hK, hKs⟩ := mem_cocompact.1 (eventually_windingNumber_eq_zero hγ)
  obtain ⟨w, hwC, hwK⟩ : ∃ w ∈ connectedComponentIn (range γ)ᶜ z, w ∉ K := by
    by_contra! h
    exact hb (hK.isBounded.subset h)
  rw [← windingNumber_eq_of_isPreconnected hγ isPreconnected_connectedComponentIn
    (connectedComponentIn_subset _ _) (mem_connectedComponentIn hz) hwC]
  exact hKs hwK

/-- For `z` off a closed piecewise `C¹` path `γ` and `f` continuous on `γ`,
`∫_γ dslope f z ζ dζ = ∫_γ f ζ / (ζ - z) dζ - 2πi n(γ, z) f z`. -/
public theorem curveIntegral_dslope_of_notMem (hγ : γ.IsPiecewiseC1) {f : ℂ → ℂ}
    (hf : ContinuousOn f (range γ)) {z : ℂ} (hz : z ∉ range γ) :
    ∫ᶜ ζ in γ, dslope f z ζ • ContinuousLinearMap.id ℂ ℂ =
      (∫ᶜ ζ in γ, (f ζ / (ζ - z)) • ContinuousLinearMap.id ℂ ℂ) -
        2 * π * I * windingNumber γ z * f z := by
  have h1 := intervalIntegrable_comp_mul_deriv hγ (φ := fun ζ => f ζ / (ζ - z))
    (hf.div₀ (continuousOn_id.sub continuousOn_const) fun ζ hζ =>
      sub_ne_zero.2 fun h => hz (h ▸ hζ))
  have h2 := intervalIntegrable_comp_mul_deriv hγ (continuousOn_sub_inv hz)
  rw [windingNumber, mul_inv_cancel_left₀ two_pi_I_ne_zero]
  simp only [curveIntegral_eq_integral]
  rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_sub h1 (h2.mul_const _)]
  refine intervalIntegral.integral_congr fun t _ => ?_
  have hne : γ.extend t ≠ z := fun h => hz (h ▸ extend_mem_range γ t)
  simp only [dslope_of_ne _ hne, slope_def_field]
  ring

end WindingNumber

/-! ### Circles -/

section Circle

/-- The circle `C(c, r)` as a closed path: `t ↦ c + r e^{2πit}` on `[0, 1]`, which is Mathlib's
`circleMap c r` on `[0, 2π]` rescaled. -/
@[expose] public noncomputable def circlePath (c : ℂ) (r : ℝ) : Path (c + r) (c + r) where
  toFun t := circleMap c r (2 * π * t)
  continuous_toFun := (continuous_circleMap c r).comp (continuous_const.mul continuous_subtype_val)
  source' := by simp [circleMap]
  target' := by simp [circleMap]

variable {c : ℂ} {r : ℝ}

private theorem circlePath_extend {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (circlePath c r).extend t = circleMap c r (2 * π * t) := by
  rw [Path.extend_apply _ ht]
  rfl

/-- A circle is a closed piecewise `C¹` path. -/
public theorem isPiecewiseC1_circlePath (c : ℂ) (r : ℝ) : (circlePath c r).IsPiecewiseC1 :=
  .of_contDiffOn (((contDiff_circleMap c r).comp (contDiff_const.mul contDiff_id)).contDiffOn.congr
    fun _ ht => circlePath_extend ht)

/-- The circle `C(c, r)` lies on the sphere of radius `|r|` about `c`. -/
public theorem range_circlePath_subset (c : ℂ) (r : ℝ) : range (circlePath c r) ⊆ sphere c |r| := by
  rintro _ ⟨t, rfl⟩
  exact circleMap_mem_sphere' c r _

/-- The curve integral along `circlePath c r` is the circle integral `∮ z in C(c, r), f z`. -/
public theorem curveIntegral_circlePath (c : ℂ) (r : ℝ) (f : ℂ → ℂ) :
    ∫ᶜ z in circlePath c r, f z • ContinuousLinearMap.id ℂ ℂ = ∮ z in C(c, r), f z := by
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, derivWithin (circlePath c r).extend unitInterval t =
      (2 * π : ℝ) • deriv (circleMap c r) (2 * π * t) := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => 2 * π * s) (2 * π) t :=
      ((hasDerivAt_id t).const_mul (2 * π)).congr_deriv (mul_one _)
    have h : HasDerivAt (circleMap c r ∘ fun s : ℝ => 2 * π * s)
        ((2 * π : ℝ) • deriv (circleMap c r) (2 * π * t)) t :=
      ((differentiable_circleMap c r _).hasDerivAt).scomp t h1
    rw [derivWithin_congr (f := circleMap c r ∘ fun s : ℝ => 2 * π * s)
      (fun s hs => circlePath_extend hs) (circlePath_extend ht),
      h.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc_zero_one t ht)]
  have hcv := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
    (f := fun θ => deriv (circleMap c r) θ • f (circleMap c r θ)) (2 * π)
  simp only [mul_zero, mul_one] at hcv
  rw [curveIntegral_def, circleIntegral, ← hcv, ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  rw [curveIntegralFun_def, hd t ht, circlePath_extend ht]
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, real_smul]
  ring

/-- The circle `C(c, r)` winds once around each point of the open disc it bounds. -/
public theorem windingNumber_circlePath_of_mem_ball {z : ℂ} (hz : z ∈ ball c r) :
    windingNumber (circlePath c r) z = 1 := by
  rw [windingNumber, curveIntegral_circlePath, circleIntegral.integral_sub_inv_of_mem_ball hz,
    inv_mul_cancel₀ two_pi_I_ne_zero]

/-- The circle `C(c, r)` does not wind around points outside the closed disc it bounds. -/
public theorem windingNumber_circlePath_of_notMem_closedBall (hr : 0 ≤ r) {z : ℂ}
    (hz : z ∉ closedBall c r) : windingNumber (circlePath c r) z = 0 := by
  rw [windingNumber, curveIntegral_circlePath,
    circleIntegral_eq_zero_of_differentiable_on_off_countable hr countable_empty
      (continuousOn_sub_inv hz) fun w hw => ?_, mul_zero]
  exact (differentiableAt_id.sub_const z).inv
    (sub_ne_zero.2 fun h => hz (h ▸ ball_subset_closedBall hw.1))

end Circle

end Complex
