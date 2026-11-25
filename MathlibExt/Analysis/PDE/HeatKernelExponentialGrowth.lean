/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.HeatKernelSmoothness
public import MathlibExt.Analysis.SpecialFunctions.GaussianGrowth
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Heat evolution for exponentially growing data

The existing heat convolution is integrable and jointly smooth at every positive
time for measurable data of at most exponential growth in `|x|`. Continuous data
have their pointwise initial trace; `C¹` data with an exponentially growing
derivative also admit derivative commutation and its initial trace. Gaussian
moments give the actual heat equation, not only a formal derivative identity.

The estimates are the classical Gaussian-growth argument in Gesztesy and Holden,
*The Cole–Hopf and Miura transformations revisited*, Remark 3.5,
https://arxiv.org/abs/solv-int/9812025. No uniqueness, uniform initial convergence,
or joint regularity at time zero is claimed.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Real
open scoped ContDiff
open MathlibExt.Analysis MathlibExt.Analysis.GaussianMoments

namespace MathlibExt.Analysis.PDE.HeatKernel

/-- A heat kernel absorbs any exponential weight in the absolute spatial variable. -/
theorem integrable_heatKernel_exp_abs {t : ℝ} (ht : 0 < t) (c : ℝ) :
    Integrable (fun y : ℝ => heatKernel ℝ t y * exp (c * |y|)) := by
  have hi := (integrable_pow_mul_exp_neg_sq_add_abs
    (by positivity : 0 < 1 / (4 * t)) c 0).const_mul ((4 * π * t) ^ (-(1 : ℝ) / 2))
  convert hi using 1
  funext y
  simp only [pow_zero, one_mul, heatKernel_real, exp_add]
  have he : -y ^ 2 / (4 * t) = -(1 / (4 * t)) * y ^ 2 := by ring
  rw [he]
  ring

/-- Affine rescaling preserves integrability against the time-one Gaussian. -/
theorem integrable_heatKernel_mul_affine {f : ℝ → ℝ} (hf : Continuous f)
    (hg : HasExpGrowth f) (z s : ℝ) :
    Integrable (fun y => heatKernel ℝ 1 y * f (z - s * y)) := by
  obtain ⟨A, c, _, _, h⟩ := hg.affine_bound |z| |s|
  apply ((integrable_heatKernel_exp_abs one_pos c).mul_const A).mono'
    (((heatKernel_contDiff 1).continuous.mul
      (hf.comp (continuous_const.sub (continuous_const.mul continuous_id)))).aestronglyMeasurable)
  filter_upwards with y
  change ‖heatKernel ℝ 1 y * f (z - s * y)‖ ≤ _
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (heatKernel_pos one_pos y)]
  calc
    _ ≤ heatKernel ℝ 1 y * (A * exp (c * |y|)) :=
      mul_le_mul_of_nonneg_left (h z s y le_rfl le_rfl) (heatKernel_pos one_pos y).le
    _ = _ := by ring

/-- Positive-time convolution is integrable for exponentially growing measurable data. -/
theorem integrable_heatKernel_mul_of_exp_growth {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f) (hg : HasExpGrowth f) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable (fun y => heatKernel ℝ t (x - y) * f y) := by
  have hi := (integrable_gaussianMoment_of_exp_growth hf hg 0
    (p := (1 / (4 * t), x / (2 * t))) (by dsimp; positivity)).const_mul
      (((4 * π * t) ^ (-(1 : ℝ) / 2)) * exp (-x ^ 2 / (4 * t)))
  convert hi using 1
  funext y
  simp only [pow_zero, one_mul, heatKernel_real]
  have he : exp (-(x - y) ^ 2 / (4 * t)) =
      exp (-x ^ 2 / (4 * t)) * exp (-(1 / (4 * t)) * y ^ 2 + x / (2 * t) * y) := by
    rw [← exp_add]
    congr 1
    field_simp
    ring
  rw [he]
  ring

/-- Exponentially growing measurable data have jointly smooth positive-time heat evolution. -/
theorem heatSolution_contDiffOn_of_exp_growth {f : ℝ → ℝ} (hf : AEStronglyMeasurable f)
    (hg : HasExpGrowth f) :
    ContDiffOn ℝ ∞ (Function.uncurry (heatSolution f)) (Ioi 0 ×ˢ univ) := by
  have ht (p : ℝ × ℝ) (hp : p ∈ Ioi (0 : ℝ) ×ˢ univ) : p.1 ≠ 0 := ne_of_gt hp.1
  have h₄ : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => 4 * p.1) (Ioi 0 ×ˢ univ) := by fun_prop
  have h₂ : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => 2 * p.1) (Ioi 0 ×ˢ univ) := by fun_prop
  have ha : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => 1 / (4 * p.1)) (Ioi 0 ×ˢ univ) :=
    contDiffOn_const.div h₄ (fun p hp => mul_ne_zero (by norm_num) (ht p hp))
  have hb' : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => p.2 / (2 * p.1)) (Ioi 0 ×ˢ univ) :=
    contDiff_snd.contDiffOn.div h₂ (fun p hp => mul_ne_zero (by norm_num) (ht p hp))
  have hm : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      gaussianMoment f 0 (1 / (4 * p.1), p.2 / (2 * p.1))) (Ioi 0 ×ˢ univ) :=
    (gaussianMoment_contDiffOn_of_exp_growth hf hg 0).comp (ha.prodMk hb') (fun p hp =>
      ⟨one_div_pos.mpr (mul_pos (by norm_num) hp.1), mem_univ _⟩)
  have hn : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (4 * π * p.1) ^ (-(1 : ℝ) / 2))
      (Ioi 0 ×ˢ univ) := by
    apply ContDiffOn.rpow_const_of_ne (by fun_prop)
    intro p hp
    exact mul_ne_zero (mul_ne_zero (by norm_num) pi_ne_zero) (ht p hp)
  have he : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => exp (-p.2 ^ 2 / (4 * p.1)))
      (Ioi 0 ×ˢ univ) :=
    ((contDiff_snd.contDiffOn.pow 2).neg.div h₄
      (fun p hp => mul_ne_zero (by norm_num) (ht p hp))).exp
  exact ((hn.mul he).mul hm).congr (fun p hp => heatSolution_eq_gaussianMoment f hp.1 p.2)


/-- Exponentially growing continuous data recover their pointwise initial value. -/
theorem heatSolution_tendsto_zero_of_exp_growth {f : ℝ → ℝ} (hf : Continuous f)
    (hg : HasExpGrowth f) (x : ℝ) :
    Tendsto (fun t => heatSolution f t x) (𝓝[>] 0) (𝓝 (f x)) := by
  obtain ⟨A, c, _, _, h⟩ := hg.affine_bound |x| 1
  have hlim : Tendsto (fun t : ℝ => ∫ y, heatKernel ℝ 1 y * f (x - sqrt t * y))
      (𝓝 0) (𝓝 (∫ y, heatKernel ℝ 1 y * f x)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y => (heatKernel ℝ 1 y * exp (c * |y|)) * A) ?_ ?_
      ((integrable_heatKernel_exp_abs one_pos c).mul_const A) ?_
    · filter_upwards with t
      exact ((heatKernel_contDiff 1).continuous.mul
        (hf.comp (continuous_const.sub (continuous_const.mul continuous_id)))).aestronglyMeasurable
    · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with t ht
      have ht' : |t| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
      have hs : |sqrt t| ≤ 1 := by
        rw [abs_of_nonneg (sqrt_nonneg _)]
        exact sqrt_le_one.mpr ((le_abs_self t).trans ht'.le)
      filter_upwards with y
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (heatKernel_pos one_pos y)]
      calc
        _ ≤ heatKernel ℝ 1 y * (A * exp (c * |y|)) :=
          mul_le_mul_of_nonneg_left (h x (sqrt t) y le_rfl hs) (heatKernel_pos one_pos y).le
        _ = _ := by ring
    · filter_upwards with y
      have hc : ContinuousAt (fun t : ℝ => heatKernel ℝ 1 y * f (x - sqrt t * y)) 0 :=
        continuousAt_const.mul (hf.continuousAt.comp
          (continuousAt_const.sub (continuous_sqrt.continuousAt.mul continuousAt_const)))
      simpa only [sqrt_zero, zero_mul, sub_zero] using hc.tendsto
  rw [integral_mul_const, integral_heatKernel one_pos, one_mul] at hlim
  have he : (fun t => heatSolution f t x) =ᶠ[𝓝[>] 0]
      (fun t => ∫ y, heatKernel ℝ 1 y * f (x - sqrt t * y)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact heatSolution_rescaled f ht x
  exact (tendsto_congr' he).2 (hlim.mono_left inf_le_left)

private theorem hasDerivAt_rescaled_growth {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : HasExpGrowth f) (hdg : HasExpGrowth (deriv f)) (t x : ℝ) :
    HasDerivAt (fun z => ∫ y, heatKernel ℝ 1 y * f (z - sqrt t * y))
      (∫ y, heatKernel ℝ 1 y * deriv f (x - sqrt t * y)) x := by
  obtain ⟨A, c, _, _, h⟩ := hdg.affine_bound (|x| + 1) |sqrt t|
  have hfc (z : ℝ) : Continuous (fun y => f (z - sqrt t * y)) :=
    hf.continuous.comp (continuous_const.sub (continuous_const.mul continuous_id))
  have hdc (z : ℝ) : Continuous (fun y => deriv f (z - sqrt t * y)) :=
    hf.continuous_deriv_one.comp (continuous_const.sub (continuous_const.mul continuous_id))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z y => heatKernel ℝ 1 y * f (z - sqrt t * y))
    (F' := fun z y => heatKernel ℝ 1 y * deriv f (z - sqrt t * y))
    (s := Metric.ball x 1) (bound := fun y => (heatKernel ℝ 1 y * exp (c * |y|)) * A)
    (Metric.ball_mem_nhds x (by norm_num)) ?_
    (integrable_heatKernel_mul_affine hf.continuous hg x (sqrt t)) ?_ ?_
    ((integrable_heatKernel_exp_abs one_pos c).mul_const A) ?_).2
  · exact Eventually.of_forall (fun z =>
      ((heatKernel_contDiff 1).continuous.mul (hfc z)).aestronglyMeasurable)
  · exact ((heatKernel_contDiff 1).continuous.mul (hdc x)).aestronglyMeasurable
  · filter_upwards with y z hz
    have hz' : |z - x| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hz
    have hzR : |z| ≤ |x| + 1 := by
      have hh := abs_add_le (z - x) x
      rw [sub_add_cancel] at hh
      linarith
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (heatKernel_pos one_pos y)]
    calc
      _ ≤ heatKernel ℝ 1 y * (A * exp (c * |y|)) :=
        mul_le_mul_of_nonneg_left (h z (sqrt t) y hzR le_rfl) (heatKernel_pos one_pos y).le
      _ = _ := by ring
  · filter_upwards with y z _
    simpa using! (((hf.differentiable (by norm_num)) (z - sqrt t * y)).hasDerivAt.comp z
      ((hasDerivAt_id' z).sub_const (sqrt t * y))).const_mul (heatKernel ℝ 1 y)

/-- Spatial differentiation commutes with heat evolution for exponentially growing
`C¹` data whose derivative also has exponential growth, including the time extension. -/
theorem heatSolution_hasDerivAt_deriv_of_exp_growth {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : HasExpGrowth f) (hdg : HasExpGrowth (deriv f)) (t x : ℝ) :
    HasDerivAt (heatSolution f t) (heatSolution (deriv f) t x) x := by
  by_cases ht : 0 < t
  · have he : heatSolution f t = fun z => ∫ y, heatKernel ℝ 1 y * f (z - sqrt t * y) :=
      funext (heatSolution_rescaled f ht)
    rw [he, heatSolution_rescaled (deriv f) ht]
    exact hasDerivAt_rescaled_growth hf hg hdg t x
  · have he : heatSolution f t = f := funext (heatSolution_of_nonpos f (le_of_not_gt ht))
    rw [he, heatSolution_of_nonpos _ (le_of_not_gt ht)]
    exact (hf.differentiable (by norm_num) x).hasDerivAt

/-- The spatial derivative recovers the initial derivative for exponential growth. -/
theorem heatSolution_deriv_tendsto_zero_of_exp_growth {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : HasExpGrowth f) (hdg : HasExpGrowth (deriv f)) (x : ℝ) :
    Tendsto (fun t => deriv (heatSolution f t) x) (𝓝[>] 0) (𝓝 (deriv f x)) := by
  simp_rw [(heatSolution_hasDerivAt_deriv_of_exp_growth hf hg hdg _ _).deriv]
  exact heatSolution_tendsto_zero_of_exp_growth hf.continuous_deriv_one hdg x

/-- Strictly positive exponentially growing continuous data remain positive. -/
theorem heatSolution_pos_of_exp_growth {f : ℝ → ℝ} (hf : Continuous f)
    (hg : HasExpGrowth f) (hp : ∀ x, 0 < f x) (t x : ℝ) : 0 < heatSolution f t x := by
  by_cases ht : 0 < t
  · rw [heatSolution_of_pos _ ht]
    have hpos (y : ℝ) : 0 < heatKernel ℝ t (x - y) * f y :=
      mul_pos (heatKernel_pos ht _) (hp y)
    rw [integral_pos_iff_support_of_nonneg (fun y => (hpos y).le)
      (integrable_heatKernel_mul_of_exp_growth hf.aestronglyMeasurable hg ht x)]
    have hs : Function.support (fun y => heatKernel ℝ t (x - y) * f y) = univ :=
      eq_univ_of_forall (fun y => ne_of_gt (hpos y))
    rw [hs]
    simp
  · simpa only [heatSolution_of_nonpos _ (le_of_not_gt ht)] using hp x

private noncomputable def heatMoment (f : ℝ → ℝ) (n : ℕ) (t x : ℝ) : ℝ :=
  heatKernel ℝ t x * gaussianMoment f n (1 / (4 * t), x / (2 * t))

private theorem heatMoment_zero (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatMoment f 0 t x = heatSolution f t x := by
  rw [heatSolution_eq_gaussianMoment f ht, heatMoment, heatKernel_real]

private theorem heatMoment_hasDerivAt_space {f : ℝ → ℝ} (hf : AEStronglyMeasurable f)
    (hg : HasExpGrowth f) (n : ℕ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (heatMoment f n t)
      (-x / (2 * t) * heatMoment f n t x + heatMoment f (n + 1) t x / (2 * t)) x := by
  have hp : HasDerivAt (fun z : ℝ => (1 / (4 * t), z / (2 * t))) (0, 1 / (2 * t)) x := by
    simpa using! (hasDerivAt_const x (1 / (4 * t))).prodMk
      ((hasDerivAt_id' x).div_const (2 * t))
  have hd : HasDerivAt (fun z : ℝ => gaussianMoment f n (1 / (4 * t), z / (2 * t)))
      (gaussianMoment f (n + 1) (1 / (4 * t), x / (2 * t)) / (2 * t)) x := by
    simpa [Function.comp_def, div_eq_mul_inv, mul_assoc] using!
      (gaussianMoment_hasFDerivAt_of_exp_growth hf hg n
      (p := (1 / (4 * t), x / (2 * t))) (by dsimp; positivity)).comp_hasDerivAt x hp
  convert (hasDerivAt_heatKernel_space t x).mul hd using 1
  · rfl
  · dsimp [heatMoment, heatKernelDx]
    ring

private theorem heatMoment_hasDerivAt_time {f : ℝ → ℝ} (hf : AEStronglyMeasurable f)
    (hg : HasExpGrowth f) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => heatMoment f 0 s x)
      ((x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * heatMoment f 0 t x -
        x / (2 * t ^ 2) * heatMoment f 1 t x + heatMoment f 2 t x / (4 * t ^ 2)) t := by
  have ha : HasDerivAt (fun s : ℝ => 1 / (4 * s)) (-1 / (4 * t ^ 2)) t := by
    convert (hasDerivAt_const t (1 : ℝ)).div ((hasDerivAt_id' t).const_mul 4)
      (by positivity : (4 : ℝ) * t ≠ 0) using 1
    ring
  have hb : HasDerivAt (fun s : ℝ => x / (2 * s)) (-x / (2 * t ^ 2)) t := by
    convert (hasDerivAt_const t x).div ((hasDerivAt_id' t).const_mul 2)
      (by positivity : (2 : ℝ) * t ≠ 0) using 1
    ring
  have hp : HasDerivAt (fun s : ℝ => (1 / (4 * s), x / (2 * s)))
      (-1 / (4 * t ^ 2), -x / (2 * t ^ 2)) t := by simpa using! ha.prodMk hb
  have hd : HasDerivAt (fun s : ℝ => gaussianMoment f 0 (1 / (4 * s), x / (2 * s)))
      (gaussianMoment f 2 (1 / (4 * t), x / (2 * t)) / (4 * t ^ 2) -
        x / (2 * t ^ 2) * gaussianMoment f 1 (1 / (4 * t), x / (2 * t))) t := by
    convert (gaussianMoment_hasFDerivAt_of_exp_growth hf hg 0
      (p := (1 / (4 * t), x / (2 * t))) (by dsimp; positivity)).comp_hasDerivAt t hp using 1
    · rfl
    · simp
      ring
  convert (hasDerivAt_heatKernel_time_dxx ht x).mul hd using 1
  · rfl
  · dsimp [heatMoment, heatKernelDxx]
    ring

/-- Actual first spatial derivative for exponentially growing measurable data. -/
theorem heatSolution_hasDerivAt_space_of_exp_growth {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f) (hg : HasExpGrowth f) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (heatSolution f t)
      (-x / (2 * t) * heatSolution f t x +
        heatKernel ℝ t x * gaussianMoment f 1 (1 / (4 * t), x / (2 * t)) / (2 * t)) x := by
  have he : heatMoment f 0 t = heatSolution f t := funext (heatMoment_zero f ht)
  change HasDerivAt (heatSolution f t)
    (-x / (2 * t) * heatSolution f t x + heatMoment f 1 t x / (2 * t)) x
  simpa only [he, Nat.zero_add] using heatMoment_hasDerivAt_space hf hg 0 ht x

/-- The actual time derivative equals the actual second spatial derivative for
exponentially growing measurable data at every positive time. -/
theorem heatSolution_hasDerivAt_time_of_exp_growth {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f) (hg : HasExpGrowth f) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => heatSolution f s x) (deriv (deriv (heatSolution f t)) x) t := by
  have he : heatMoment f 0 t = heatSolution f t := funext (heatMoment_zero f ht)
  have hdx : deriv (heatSolution f t) = fun z =>
      -z / (2 * t) * heatMoment f 0 t z + heatMoment f 1 t z / (2 * t) := by
    funext z
    rw [← he]
    exact (heatMoment_hasDerivAt_space hf hg 0 ht z).deriv
  have hxx := (((hasDerivAt_id' x).neg.div_const (2 * t)).mul
    (heatMoment_hasDerivAt_space hf hg 0 ht x)).add
      ((heatMoment_hasDerivAt_space hf hg 1 ht x).div_const (2 * t))
  change HasDerivAt (fun z => -z / (2 * t) * heatMoment f 0 t z +
    heatMoment f 1 t z / (2 * t)) _ x at hxx
  rw [hdx, hxx.deriv]
  have hd := heatMoment_hasDerivAt_time hf hg ht x
  have heq : (fun s => heatMoment f 0 s x) =ᶠ[𝓝 t] (fun s => heatSolution f s x) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact heatMoment_zero f hs x
  convert hd.congr_of_eventuallyEq heq.symm using 1
  simp only [Nat.reduceAdd, Pi.neg_apply]
  field_simp
  ring

/-- Positive viscosity rescales the actual time derivative by that viscosity. -/
theorem heatSolution_hasDerivAt_time_scaled_of_exp_growth {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f) (hg : HasExpGrowth f) {ν t : ℝ}
    (hν : 0 < ν) (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => heatSolution f (ν * s) x)
      (ν * deriv (deriv (heatSolution f (ν * t))) x) t := by
  simpa only [Function.comp_def, mul_one, mul_comm] using!
    (heatSolution_hasDerivAt_time_of_exp_growth hf hg (mul_pos hν ht) x).comp t
      ((hasDerivAt_id' t).const_mul ν)

/-- Positive diffusivity preserves joint smoothness for exponentially growing data. -/
theorem heatSolution_contDiffOn_scaled_of_exp_growth {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f) (hg : HasExpGrowth f) {ν : ℝ} (hν : 0 < ν) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => heatSolution f (ν * p.1) p.2) (Ioi 0 ×ˢ univ) :=
  (heatSolution_contDiffOn_of_exp_growth hf hg).comp
    ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd).contDiffOn
    (fun _ hp => ⟨mul_pos hν hp.1, mem_univ _⟩)

private theorem tendsto_pos_mul_zero {ν : ℝ} (hν : 0 < ν) :
    Tendsto (fun t : ℝ => ν * t) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : ContinuousAt (fun t : ℝ => ν * t) 0 := continuousAt_const.mul continuousAt_id
    simpa only [mul_zero] using! hc.tendsto.mono_left (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_pos hν ht

/-- Positive time scaling preserves the initial trace for exponential growth. -/
theorem heatSolution_tendsto_zero_scaled_of_exp_growth {f : ℝ → ℝ} (hf : Continuous f)
    (hg : HasExpGrowth f) {ν : ℝ} (hν : 0 < ν) (x : ℝ) :
    Tendsto (fun t => heatSolution f (ν * t) x) (𝓝[>] 0) (𝓝 (f x)) :=
  (heatSolution_tendsto_zero_of_exp_growth hf hg x).comp (tendsto_pos_mul_zero hν)

/-- Positive time scaling preserves the derivative initial trace for exponential growth. -/
theorem heatSolution_deriv_tendsto_zero_scaled_of_exp_growth {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : HasExpGrowth f) (hdg : HasExpGrowth (deriv f))
    {ν : ℝ} (hν : 0 < ν) (x : ℝ) :
    Tendsto (fun t => deriv (heatSolution f (ν * t)) x) (𝓝[>] 0) (𝓝 (deriv f x)) :=
  (heatSolution_deriv_tendsto_zero_of_exp_growth hf hg hdg x).comp (tendsto_pos_mul_zero hν)

end MathlibExt.Analysis.PDE.HeatKernel
