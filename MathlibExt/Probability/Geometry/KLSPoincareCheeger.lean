/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Geometry.KLS
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.UniformSpace.HeineCantor
import MathlibExt.Probability.Quantile

/-!
# Cheeger's inequality

The main result, `smoothPoincareConstant_le_four_mul_inverseCheegerConstant_sq`, is Cheeger's
inequality: the smooth Poincaré constant of a probability measure on $\mathbb{R}^n$ is at most four
times the square of its inverse Cheeger constant. Its special case `poincare_cheeger_upper_bound`
states it for isotropic log-concave probability measures.

A coarea inequality for compactly supported $C^1$ functions $g$, obtained from the definition of
the outer Minkowski boundary measure, Fatou's lemma and Tonelli's theorem, bounds
$\int_{\mathbb{R}} \mu^+(\{g > t\}) \, dt$ by $\int \lVert \nabla g \rVert \, d\mu$. With the
isoperimetric inequality behind the Cheeger coefficient $h$ and the layer-cake formula this gives
$h \int g \, d\mu \le \int \lVert \nabla g \rVert \, d\mu$ for nonnegative $g$ whose support has
measure at most $1/2$; cutoff functions remove the compact support assumption. Applied to the
squares of the positive and negative parts of $f - m$, for a median $m$ of $f$ (the value at
$1/2$ of the quantile function of the law of $f$), it gives
$h^2 \int (f - m)^2 \, d\mu \le 4 \int \lVert \nabla f \rVert^2 \, d\mu$, and the variance of $f$
is at most $\int (f - m)^2 \, d\mu$.

Klartag, arXiv:2303.14938v1, Introduction, inequality (4), attributes the inequality to Cheeger.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal ContDiff
open MathlibExt.Probability.ThinShell

namespace MathlibExt.Probability.KLS

/-! ### A coarea inequality -/

/-- A mean value bound: if the derivative of `g` stays within `η` of its value at `x` on the ball
of radius `δ` about `x`, then `g y ≤ g x + (‖g'(x)‖ + η) dist(y, x)` on that ball. -/
private theorem le_add_mul_dist_of_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} (hg : Differentiable ℝ g) {x y : E} {δ η : ℝ}
    (hδ : ∀ z, dist z x < δ → ‖fderiv ℝ g z - fderiv ℝ g x‖ ≤ η) (hy : dist y x < δ) :
    g y ≤ g x + (‖fderiv ℝ g x‖ + η) * dist y x := by
  have hδ0 : 0 < δ := lt_of_le_of_lt dist_nonneg hy
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℝ) (f := g) (s := ball x δ)
    (x := x) (y := y) (φ := fderiv ℝ g x) (fun z _ => hg z) (fun z hz => hδ z hz)
    (convex_ball x δ) (mem_ball_self hδ0) hy
  have h2 : fderiv ℝ g x (y - x) ≤ ‖fderiv ℝ g x‖ * ‖y - x‖ :=
    (le_abs_self _).trans ((fderiv ℝ g x).le_opNorm (y - x))
  have h3 : g y - g x - fderiv ℝ g x (y - x) ≤ η * ‖y - x‖ :=
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h)
  rw [dist_eq_norm]
  nlinarith

/-- If the derivative of `g` is uniformly `η`-close to itself at scale `δ` and `0 ≤ ε < δ`, then
every point of the closed `ε`-neighbourhood of `{g > t}` satisfies
`t ≤ g x + ε (‖g'(x)‖ + η)`. -/
private theorem le_add_of_mem_cthickening {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} (hg : Differentiable ℝ g) {δ η ε t : ℝ} (hη : 0 < η)
    (hδ : ∀ x z : E, dist z x < δ → ‖fderiv ℝ g z - fderiv ℝ g x‖ ≤ η)
    (hε : 0 ≤ ε) (hεδ : ε < δ) {x : E} (hx : x ∈ cthickening ε {y | t < g y}) :
    t ≤ g x + ε * (‖fderiv ℝ g x‖ + η) := by
  by_contra hlt
  rw [not_le] at hlt
  set L := ‖fderiv ℝ g x‖ + η with hL
  have hL0 : 0 < L := by positivity
  set d := min ((t - g x) / L) δ with hd
  have hεd : ε < d := by
    refine lt_min ?_ hεδ
    rw [lt_div_iff₀ hL0]
    linarith
  have hle : ENNReal.ofReal d ≤ infEDist x {y | t < g y} := by
    rw [Metric.le_infEDist]
    intro y hy
    rw [edist_dist, dist_comm]
    apply ENNReal.ofReal_le_ofReal
    rcases lt_or_ge (dist y x) δ with hyx | hyx
    · have hmv := le_add_mul_dist_of_fderiv hg (hδ x) hyx
      have hty : t < g y := hy
      have : (t - g x) / L ≤ dist y x := by
        rw [div_le_iff₀ hL0]
        linarith
      exact (min_le_left _ _).trans this
    · exact (min_le_right _ _).trans hyx
  rw [mem_cthickening_iff] at hx
  have := (ENNReal.ofReal_le_ofReal_iff hε).mp (hle.trans hx)
  linarith

/-- Tonelli's theorem for a band: integrating over `t` the measure of
`{x | g x ≤ t ≤ g x + c x}` gives `∫ c dμ`. -/
private theorem lintegral_measure_band {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [SFinite μ] {g c : E → ℝ} (hg : Measurable g) (hc : Measurable c) :
    ∫⁻ t, μ {x | g x ≤ t ∧ t ≤ g x + c x} = ∫⁻ x, ENNReal.ofReal (c x) ∂μ := by
  set S : Set (E × ℝ) := {p | g p.1 ≤ p.2 ∧ p.2 ≤ g p.1 + c p.1} with hS_def
  have hS : MeasurableSet S :=
    (measurableSet_le (hg.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd ((hg.comp measurable_fst).add (hc.comp measurable_fst)))
  calc ∫⁻ t, μ {x | g x ≤ t ∧ t ≤ g x + c x}
      = (μ.prod volume) S := (Measure.prod_apply_symm hS).symm
    _ = ∫⁻ x, volume (Prod.mk x ⁻¹' S) ∂μ := Measure.prod_apply hS
    _ = ∫⁻ x, ENNReal.ofReal (c x) ∂μ := by
        refine lintegral_congr fun x => ?_
        have : Prod.mk x ⁻¹' S = Icc (g x) (g x + c x) := by
          ext t
          simp [S]
        rw [this, Real.volume_Icc]
        congr 1
        ring

/-- The coarea inequality for a compactly supported `C¹` function `g` and a probability measure:
`∫ μ⁺({g > t}) dt ≤ ∫ ‖∇g‖ dμ`, where `μ⁺` is the outer Minkowski boundary measure. -/
private theorem lintegral_outerMinkowskiBoundary_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {g : E → ℝ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    ∫⁻ t, outerMinkowskiBoundary μ {x | t < g x} ≤
      ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ g x‖ ∂μ := by
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hcont : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hunif : UniformContinuous (fderiv ℝ g) :=
    (hgc.fderiv ℝ).uniformContinuous_of_continuous hcont
  have hgm : Measurable g := hg.continuous.measurable
  have hGm : Measurable fun x => ‖fderiv ℝ g x‖ := hcont.norm.measurable
  set φ : ℝ → ℝ → ℝ≥0∞ := fun ε t =>
    (μ (cthickening ε {x | t < g x}) - μ {x | t < g x}) / ENNReal.ofReal ε with hφ
  have hφm : ∀ ε, Measurable (φ ε) := by
    intro ε
    have h1 : Antitone fun t : ℝ => μ (cthickening ε {x | t < g x}) := fun s t hst =>
      measure_mono (cthickening_subset_of_subset ε fun x (hx : t < g x) => lt_of_le_of_lt hst hx)
    have h2 : Antitone fun t : ℝ => μ {x | t < g x} := fun s t hst =>
      measure_mono fun x (hx : t < g x) => lt_of_le_of_lt hst hx
    exact (h1.measurable.sub h2.measurable).div_const _
  calc ∫⁻ t, outerMinkowskiBoundary μ {x | t < g x}
      = ∫⁻ t, liminf (fun ε => φ ε t) (𝓝[>] 0) := rfl
    _ ≤ liminf (fun ε => ∫⁻ t, φ ε t) (𝓝[>] 0) := lintegral_liminf_le hφm
    _ ≤ ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ g x‖ ∂μ := by
      refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
      have hη' : (0 : ℝ) < η := hη
      obtain ⟨δ, hδ, hδη⟩ := Metric.uniformContinuous_iff.mp hunif η hη'
      have hδ' : ∀ x z : E, dist z x < δ → ‖fderiv ℝ g z - fderiv ℝ g x‖ ≤ η := by
        intro x z hzx
        rw [← dist_eq_norm]
        exact (hδη hzx).le
      apply liminf_le_of_frequently_le'
      apply Eventually.frequently
      filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
      obtain ⟨hε0, hεδ⟩ := hε
      have hband : ∀ t, φ ε t ≤
          μ {x | g x ≤ t ∧ t ≤ g x + ε * (‖fderiv ℝ g x‖ + η)} / ENNReal.ofReal ε := by
        intro t
        apply ENNReal.div_le_div_right
        refine le_measure_sdiff.trans (measure_mono ?_)
        rintro x ⟨hx, hxA⟩
        exact ⟨not_lt.mp hxA, le_add_of_mem_cthickening hdiff hη' hδ' hε0.le hεδ hx⟩
      calc ∫⁻ t, φ ε t
          ≤ ∫⁻ t, μ {x | g x ≤ t ∧ t ≤ g x + ε * (‖fderiv ℝ g x‖ + η)} *
              (ENNReal.ofReal ε)⁻¹ := lintegral_mono fun t => by
            simpa only [div_eq_mul_inv] using hband t
        _ = (∫⁻ x, ENNReal.ofReal (ε * (‖fderiv ℝ g x‖ + η)) ∂μ) * (ENNReal.ofReal ε)⁻¹ := by
            rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr (by simpa using hε0)),
              lintegral_measure_band μ hgm ((hGm.add_const (η : ℝ)).const_mul ε)]
        _ = ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ g x‖ + η) ∂μ := by
            simp_rw [ENNReal.ofReal_mul hε0.le]
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_comm, ← mul_assoc,
              ENNReal.inv_mul_cancel (by simpa using hε0) ENNReal.ofReal_ne_top, one_mul]
        _ = ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ g x‖ ∂μ + η := by
            simp_rw [ENNReal.ofReal_add (norm_nonneg _) hη'.le]
            rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
              ENNReal.ofReal_coe_nnreal]

/-! ### The L¹ form of Cheeger's inequality -/

/-- The L¹ Cheeger inequality for a compactly supported `C¹` function `g ≥ 0` whose support has
measure at most `1/2`: `c ∫ g dμ ≤ ∫ ‖∇g‖ dμ`, when `c μ(A) ≤ μ⁺(A)` for every measurable `A`
with `0 < μ(A) ≤ 1/2`. -/
private theorem cheeger_lintegral_le_of_hasCompactSupport {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {c : ℝ} (hc : ∀ A : Set E, MeasurableSet A → 0 < μ A → μ A ≤ 2⁻¹ →
      ENNReal.ofReal c * μ A ≤ outerMinkowskiBoundary μ A)
    {g : E → ℝ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (hg0 : ∀ x, 0 ≤ g x)
    (hsupp : μ {x | 0 < g x} ≤ 2⁻¹) :
    ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (g x) ∂μ ≤
      ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ g x‖ ∂μ := by
  rw [lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall hg0) hg.continuous.aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ∫⁻ t in Ioi 0, ENNReal.ofReal c * μ {x | t < g x}
      ≤ ∫⁻ t in Ioi 0, outerMinkowskiBoundary μ {x | t < g x} := by
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        rcases eq_or_ne (μ {x | t < g x}) 0 with h0 | h0
        · rw [h0, mul_zero]
          exact bot_le
        · refine hc _ (measurableSet_lt measurable_const hg.continuous.measurable)
            (pos_iff_ne_zero.mpr h0) ((measure_mono ?_).trans hsupp)
          intro x hx
          exact lt_trans (show (0 : ℝ) < t from ht) hx
    _ ≤ ∫⁻ t, outerMinkowskiBoundary μ {x | t < g x} := setLIntegral_le_lintegral _ _
    _ ≤ _ := lintegral_outerMinkowskiBoundary_le μ hg hgc

/-- The L¹ Cheeger inequality for a `C¹` function `g ≥ 0` with `∫ g dμ < ∞` whose support has
measure at most `1/2`, obtained from the compactly supported case with cutoff functions. -/
private theorem cheeger_lintegral_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {c : ℝ} (hc : ∀ A : Set E, MeasurableSet A → 0 < μ A → μ A ≤ 2⁻¹ →
      ENNReal.ofReal c * μ A ≤ outerMinkowskiBoundary μ A)
    {g : E → ℝ} (hg : ContDiff ℝ 1 g) (hg0 : ∀ x, 0 ≤ g x)
    (hsupp : μ {x | 0 < g x} ≤ 2⁻¹) (hgi : ∫⁻ x, ENNReal.ofReal (g x) ∂μ ≠ ⊤) :
    ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (g x) ∂μ ≤
      ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ g x‖ ∂μ := by
  let b : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  have hb : ContDiff ℝ 1 (b : E → ℝ) := b.contDiff (n := 1)
  obtain ⟨M, hM⟩ := (b.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hb.continuous_fderiv one_ne_zero)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set a : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with ha
  have ha0 : ∀ k, 0 < a k := fun k => by positivity
  -- the cutoff `χ k` equals `1` on the ball of radius `k + 1` and has gradient at most `M a k`
  set χ : ℕ → E → ℝ := fun k x => b (a k • x) with hχ
  have hχd : ∀ k x, HasFDerivAt (χ k)
      ((fderiv ℝ b (a k • x)).comp (a k • ContinuousLinearMap.id ℝ E)) x := by
    intro k x
    exact ((hb.differentiable one_ne_zero) (a k • x)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul (a k))
  have hχd_le : ∀ k x, ‖(fderiv ℝ b (a k • x)).comp (a k • ContinuousLinearMap.id ℝ E)‖ ≤
      M * a k := by
    intro k x
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine mul_le_mul (hM _) ?_ (norm_nonneg _) hM0
    refine (norm_smul_le (a k) (ContinuousLinearMap.id ℝ E)).trans ?_
    rw [Real.norm_eq_abs, abs_of_pos (ha0 k)]
    exact mul_le_of_le_one_right (ha0 k).le ContinuousLinearMap.norm_id_le
  set gk : ℕ → E → ℝ := fun k x => χ k x * g x with hgk
  have hgk_cd : ∀ k, ContDiff ℝ 1 (gk k) := fun k =>
    (hb.comp (contDiff_const_smul (a k))).mul hg
  have hgk_cs : ∀ k, HasCompactSupport (gk k) := fun k =>
    (b.hasCompactSupport.comp_smul (ha0 k).ne').mul_right
  have hgk0 : ∀ k x, 0 ≤ gk k x := fun k x => mul_nonneg b.nonneg (hg0 x)
  have hgk_le : ∀ k x, gk k x ≤ g x := fun k x => mul_le_of_le_one_left (hg0 x) b.le_one
  have hgk_supp : ∀ k, μ {x | 0 < gk k x} ≤ 2⁻¹ := by
    intro k
    refine (measure_mono ?_).trans hsupp
    intro x hx
    refine lt_of_le_of_ne (hg0 x) fun h => ?_
    simp [gk, ← h] at hx
  have hgk_deriv : ∀ k x, ‖fderiv ℝ (gk k) x‖ ≤ ‖fderiv ℝ g x‖ + M * a k * g x := by
    intro k x
    have hd : HasFDerivAt (fun y => χ k y * g y) _ x :=
      (hχd k x).mul ((hg.differentiable one_ne_zero) x).hasFDerivAt
    rw [show gk k = fun y => χ k y * g y from rfl, hd.fderiv]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_smul_le (χ k x) (fderiv ℝ g x)).trans ?_
      rw [Real.norm_eq_abs, abs_of_nonneg b.nonneg]
      exact mul_le_of_le_one_left (norm_nonneg _) b.le_one
    · refine (norm_smul_le (g x) ((fderiv ℝ b (a k • x)).comp
        (a k • ContinuousLinearMap.id ℝ E))).trans ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x), mul_comm]
      exact mul_le_mul_of_nonneg_right (hχd_le k x) (hg0 x)
  have hbound : ∀ k, ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (gk k x) ∂μ ≤
      ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ g x‖ ∂μ +
        ENNReal.ofReal (M * a k) * ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
    intro k
    refine (cheeger_lintegral_le_of_hasCompactSupport μ hc (hgk_cd k) (hgk_cs k) (hgk0 k)
      (hgk_supp k)).trans ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_add_left (hg.continuous_fderiv one_ne_zero).norm.measurable.ennreal_ofReal]
    refine lintegral_mono fun x => ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (norm_nonneg _)
      (by have := ha0 k; have := hg0 x; positivity)]
    exact ENNReal.ofReal_le_ofReal (hgk_deriv k x)
  have hlim_left : Tendsto (fun k => ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (gk k x) ∂μ)
      atTop (𝓝 (ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (g x) ∂μ)) := by
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr ENNReal.ofReal_ne_top)
    refine tendsto_lintegral_of_dominated_convergence (fun x => ENNReal.ofReal (g x))
      (fun k => ((hgk_cd k).continuous.measurable).ennreal_ofReal)
      (fun k => Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (hgk_le k x)) hgi
      (Eventually.of_forall fun x => ?_)
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
    filter_upwards [eventually_ge_atTop N] with k hk
    have h1 : χ k x = 1 := by
      apply b.one_of_mem_closedBall
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (ha0 k)]
      change 1 / ((k : ℝ) + 1) * ‖x‖ ≤ 1
      rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      have : (N : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    simp [gk, h1]
  have hlim_right : Tendsto (fun k => ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ g x‖ ∂μ +
      ENNReal.ofReal (M * a k) * ∫⁻ x, ENNReal.ofReal (g x) ∂μ) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal ‖fderiv ℝ g x‖ ∂μ)) := by
    have h0 : Tendsto (fun k : ℕ => ENNReal.ofReal (M * a k)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul M
      rw [mul_zero] at this
      have := ENNReal.tendsto_ofReal this
      rwa [ENNReal.ofReal_zero] at this
    have := tendsto_const_nhds (x := ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ g x‖ ∂μ)
      |>.add (ENNReal.Tendsto.mul_const h0 (Or.inr hgi))
    rwa [zero_mul, add_zero] at this
  exact le_of_tendsto_of_tendsto' hlim_left hlim_right hbound

/-! ### From the L¹ form to the Poincaré inequality -/

/-- The derivative of `s ↦ max s 0 ^ 2` is `s ↦ 2 max s 0`. -/
private theorem hasDerivAt_max_zero_sq (s : ℝ) :
    HasDerivAt (fun s : ℝ => max s 0 ^ 2) (2 * max s 0) s := by
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · have h : (fun s : ℝ => max s 0 ^ 2) =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hs] with y hy
      simp [max_eq_right (le_of_lt (mem_Iio.mp hy))]
    rw [max_eq_right hs.le, mul_zero]
    exact (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq h
  · have h1 : HasDerivWithinAt (fun s : ℝ => max s 0 ^ 2) 0 (Iic 0) 0 := by
      refine (hasDerivWithinAt_const (0 : ℝ) (Iic 0) (0 : ℝ)).congr (fun y hy => ?_) (by simp)
      simp [max_eq_right (show y ≤ 0 from hy)]
    have h2 : HasDerivWithinAt (fun s : ℝ => max s 0 ^ 2) 0 (Ici 0) 0 := by
      have := (hasDerivAt_pow 2 (0 : ℝ)).hasDerivWithinAt (s := Ici 0)
      norm_num at this
      refine this.congr (fun y hy => ?_) (by simp)
      simp [max_eq_left (show 0 ≤ y from hy)]
    have := h1.union h2
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at this
    simpa using this
  · have h : (fun s : ℝ => max s 0 ^ 2) =ᶠ[𝓝 s] fun y => y ^ 2 := by
      filter_upwards [Ioi_mem_nhds hs] with y hy
      simp [max_eq_left (le_of_lt (mem_Ioi.mp hy))]
    rw [max_eq_left hs.le]
    simpa using (hasDerivAt_pow 2 s).congr_of_eventuallyEq h

/-- The function `s ↦ max s 0 ^ 2` is `C¹`. -/
private theorem contDiff_max_zero_sq : ContDiff ℝ 1 fun s : ℝ => max s 0 ^ 2 := by
  refine contDiff_one_iff_deriv.mpr ⟨fun s => (hasDerivAt_max_zero_sq s).differentiableAt, ?_⟩
  rw [show deriv (fun s : ℝ => max s 0 ^ 2) = fun s => 2 * max s 0 from
    funext fun s => (hasDerivAt_max_zero_sq s).deriv]
  fun_prop

/-- Every measurable real function on a probability space has a median `m`:
`μ {m < f} ≤ 1/2` and `μ {f < m} ≤ 1/2`. The value at `1/2` of the quantile function of the law
of `f` is one. -/
private theorem exists_median {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {f : E → ℝ} (hf : Measurable f) :
    ∃ m : ℝ, μ {x | m < f x} ≤ 2⁻¹ ∧ μ {x | f x < m} ≤ 2⁻¹ := by
  have hu : (2⁻¹ : ℝ) ∈ Ioo 0 1 := by norm_num
  -- `t ↦ μ {f ≤ t}` is the cdf of the law of `f`
  have hF : ∀ t, μ {x | f x ≤ t} = ENNReal.ofReal (ProbabilityTheory.cdf (μ.map f) t) := by
    intro t
    rw [ProbabilityTheory.ofReal_cdf, Measure.map_apply hf measurableSet_Iic]
    rfl
  have hhalf : ENNReal.ofReal 2⁻¹ = 2⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  set m := ProbabilityTheory.cdfQuantile (μ.map f) 2⁻¹
  refine ⟨m, ?_, ?_⟩
  · have hcompl : μ {x | m < f x} = 1 - μ {x | f x ≤ m} := by
      rw [← prob_compl_eq_one_sub (measurableSet_le hf measurable_const)]
      congr 1
      ext x
      simp [not_le]
    have hFm : 2⁻¹ ≤ μ {x | f x ≤ m} := by
      rw [hF, ← hhalf]
      exact ENNReal.ofReal_le_ofReal (ProbabilityTheory.cdfQuantile_mem (μ.map f) hu)
    rw [hcompl, tsub_le_iff_right]
    calc (1 : ℝ≥0∞) = 2⁻¹ + 2⁻¹ := ENNReal.inv_two_add_inv_two.symm
      _ ≤ 2⁻¹ + μ {x | f x ≤ m} := by gcongr
  · have hlow : ∀ t, t < m → μ {x | f x ≤ t} ≤ 2⁻¹ := by
      intro t ht
      rw [hF, ← hhalf]
      refine ENNReal.ofReal_le_ofReal (le_of_lt ?_)
      rw [← not_le, ← ProbabilityTheory.cdfQuantile_le_iff (μ.map f) hu, not_le]
      exact ht
    -- `μ {f < m} ≤ 1/2` by continuity from below
    have h := tendsto_measure_iUnion_atTop (μ := μ)
      (s := fun k : ℕ => {x | f x ≤ m - 1 / ((k : ℝ) + 1)})
      (fun i j hij x (hx : f x ≤ m - 1 / ((i : ℝ) + 1)) => hx.trans (by
        have : (i : ℝ) ≤ j := by exact_mod_cast hij
        gcongr))
    have hsub : {x | f x < m} ⊆ ⋃ k : ℕ, {x | f x ≤ m - 1 / ((k : ℝ) + 1)} := by
      intro x (hx : f x < m)
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
      exact mem_iUnion.mpr ⟨k, show f x ≤ m - 1 / ((k : ℝ) + 1) by linarith⟩
    refine (measure_mono hsub).trans (le_of_tendsto' h fun k => hlow _ ?_)
    exact sub_lt_self _ (by positivity)

/-- The elementary inequality
`2 max(a - m, 0) b + 2 max(m - a, 0) b ≤ (c/2)(a - m)² + (2/c) b²` for `c > 0`. -/
private theorem two_mul_abs_mul_le {c a m b : ℝ} (hc : 0 < c) :
    2 * max (a - m) 0 * b + 2 * max (m - a) 0 * b ≤ c / 2 * (a - m) ^ 2 + 2 / c * b ^ 2 := by
  have habs : max (a - m) 0 + max (m - a) 0 = |a - m| := by
    rcases le_total (a - m) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]
      ring
    · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h, add_zero]
  have h1 : 0 ≤ (c * |a - m| - 2 * b) ^ 2 / (2 * c) := by positivity
  have h2 : (c * |a - m| - 2 * b) ^ 2 / (2 * c) =
      c / 2 * (a - m) ^ 2 + 2 / c * b ^ 2 - 2 * |a - m| * b := by
    rw [← sq_abs (a - m)]
    field_simp
    ring
  have h3 : 2 * max (a - m) 0 * b + 2 * max (m - a) 0 * b = 2 * |a - m| * b := by
    rw [← habs]
    ring
  linarith

/-- The L² step: for a `C¹` function `f` and a median `m` of `f`,
`c² ∫ (f - m)² dμ ≤ 4 ∫ ‖∇f‖² dμ`. -/
private theorem sq_mul_lintegral_sub_median_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] {c : ℝ} (hc0 : 0 < c)
    (hc : ∀ A : Set E, MeasurableSet A → 0 < μ A → μ A ≤ 2⁻¹ →
      ENNReal.ofReal c * μ A ≤ outerMinkowskiBoundary μ A)
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) {m : ℝ} (hm1 : μ {x | m < f x} ≤ 2⁻¹)
    (hm2 : μ {x | f x < m} ≤ 2⁻¹) (hI : ∫⁻ x, ENNReal.ofReal ((f x - m) ^ 2) ∂μ ≠ ⊤) :
    ENNReal.ofReal (c ^ 2) * ∫⁻ x, ENNReal.ofReal ((f x - m) ^ 2) ∂μ ≤
      4 * ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2) ∂μ := by
  set I := ∫⁻ x, ENNReal.ofReal ((f x - m) ^ 2) ∂μ with hIdef
  set J := ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2) ∂μ with hJdef
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  set gp : E → ℝ := fun x => max (f x - m) 0 ^ 2 with hgp
  set gn : E → ℝ := fun x => max (m - f x) 0 ^ 2 with hgn
  have hgp_cd : ContDiff ℝ 1 gp := contDiff_max_zero_sq.comp (hf.sub contDiff_const)
  have hgn_cd : ContDiff ℝ 1 gn := contDiff_max_zero_sq.comp (contDiff_const.sub hf)
  have hgp_d : ∀ x, ‖fderiv ℝ gp x‖ = 2 * max (f x - m) 0 * ‖fderiv ℝ f x‖ := by
    intro x
    have h := (hasDerivAt_max_zero_sq (f x - m)).comp_hasFDerivAt x
      ((hfd x).hasFDerivAt.sub_const m)
    rw [show gp = (fun s : ℝ => max s 0 ^ 2) ∘ fun y => f y - m from rfl, h.fderiv, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hgn_d : ∀ x, ‖fderiv ℝ gn x‖ = 2 * max (m - f x) 0 * ‖fderiv ℝ f x‖ := by
    intro x
    have h := (hasDerivAt_max_zero_sq (m - f x)).comp_hasFDerivAt x
      ((hfd x).hasFDerivAt.const_sub m)
    rw [show gn = (fun s : ℝ => max s 0 ^ 2) ∘ fun y => m - f y from rfl, h.fderiv, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_neg]
  have hgp_supp : μ {x | 0 < gp x} ≤ 2⁻¹ := by
    refine (measure_mono ?_).trans hm1
    intro x hx
    by_contra h
    have h' : f x - m ≤ 0 := by
      have : ¬ m < f x := h
      linarith
    have hx' : 0 < max (f x - m) 0 ^ 2 := hx
    rw [max_eq_right h'] at hx'
    simp at hx'
  have hgn_supp : μ {x | 0 < gn x} ≤ 2⁻¹ := by
    refine (measure_mono ?_).trans hm2
    intro x hx
    by_contra h
    have h' : m - f x ≤ 0 := by
      have : ¬ f x < m := h
      linarith
    have hx' : 0 < max (m - f x) 0 ^ 2 := hx
    rw [max_eq_right h'] at hx'
    simp at hx'
  have hsplit : ∀ x, (f x - m) ^ 2 = gp x + gn x := by
    intro x
    simp only [gp, gn]
    rcases le_total (f x - m) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
  have hgp_le : ∀ x, gp x ≤ (f x - m) ^ 2 := fun x => by
    rw [hsplit x]
    exact le_add_of_nonneg_right (by positivity)
  have hgn_le : ∀ x, gn x ≤ (f x - m) ^ 2 := fun x => by
    rw [hsplit x]
    exact le_add_of_nonneg_left (by positivity)
  have hgp_i : ∫⁻ x, ENNReal.ofReal (gp x) ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top hI (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hgp_le x))
  have hgn_i : ∫⁻ x, ENNReal.ofReal (gn x) ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top hI (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hgn_le x))
  have hp := cheeger_lintegral_le μ hc hgp_cd (fun x => by positivity) hgp_supp hgp_i
  have hn := cheeger_lintegral_le μ hc hgn_cd (fun x => by positivity) hgn_supp hgn_i
  have hgp_m : Measurable fun x => ENNReal.ofReal (gp x) :=
    hgp_cd.continuous.measurable.ennreal_ofReal
  have hdp_m : Measurable fun x => ENNReal.ofReal ‖fderiv ℝ gp x‖ :=
    (hgp_cd.continuous_fderiv one_ne_zero).norm.measurable.ennreal_ofReal
  have hsq_m : Measurable fun x => ENNReal.ofReal ((f x - m) ^ 2) :=
    ((hf.continuous.sub continuous_const).pow 2).measurable.ennreal_ofReal
  have hsum : ENNReal.ofReal c * I ≤
      ENNReal.ofReal (c / 2) * I + ENNReal.ofReal (2 / c) * J := by
    calc ENNReal.ofReal c * I
        = ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (gp x) ∂μ +
            ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (gn x) ∂μ := by
          rw [← mul_add, ← lintegral_add_left hgp_m]
          congr 1
          refine lintegral_congr fun x => ?_
          rw [hsplit x, ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ gp x‖ ∂μ +
            ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ gn x‖ ∂μ := add_le_add hp hn
      _ = ∫⁻ x, (ENNReal.ofReal ‖fderiv ℝ gp x‖ + ENNReal.ofReal ‖fderiv ℝ gn x‖) ∂μ :=
          (lintegral_add_left hdp_m _).symm
      _ ≤ ∫⁻ x, (ENNReal.ofReal (c / 2) * ENNReal.ofReal ((f x - m) ^ 2) +
            ENNReal.ofReal (2 / c) * ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2)) ∂μ := by
          refine lintegral_mono fun x => ?_
          rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ← ENNReal.ofReal_mul
            (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add
            (by positivity) (by positivity), hgp_d, hgn_d]
          exact ENNReal.ofReal_le_ofReal (two_mul_abs_mul_le hc0)
      _ = ENNReal.ofReal (c / 2) * I + ENNReal.ofReal (2 / c) * J := by
          rw [lintegral_add_left (hsq_m.const_mul _), lintegral_const_mul _ hsq_m,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hhalf : ENNReal.ofReal c * I =
      ENNReal.ofReal (c / 2) * I + ENNReal.ofReal (c / 2) * I := by
    rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]
  rw [hhalf] at hsum
  have hcancel : ENNReal.ofReal (c / 2) * I ≤ ENNReal.ofReal (2 / c) * J :=
    (ENNReal.add_le_add_iff_left (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI)).mp hsum
  calc ENNReal.ofReal (c ^ 2) * I = ENNReal.ofReal (2 * c) * (ENNReal.ofReal (c / 2) * I) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring
    _ ≤ ENNReal.ofReal (2 * c) * (ENNReal.ofReal (2 / c) * J) := by gcongr
    _ = 4 * J := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        rw [show 2 * c * (2 / c) = (4 : ℝ) by field_simp; ring, ENNReal.ofReal_ofNat]

/-- If `f` and `f²` are integrable for a finite measure, so is `(f - a)²`. -/
private theorem integrable_sub_sq {E : Type*} [MeasurableSpace E] {μ : Measure E}
    [IsFiniteMeasure μ] {f : E → ℝ} (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) (a : ℝ) :
    Integrable (fun x => (f x - a) ^ 2) μ := by
  have : (fun x => (f x - a) ^ 2) = fun x => f x ^ 2 - 2 * a * f x + a ^ 2 := by
    ext x
    ring
  rw [this]
  exact (hf2.sub (hf.const_mul _)).add (integrable_const _)

/-- The variance is the least mean square deviation: `∫ (f - E f)² dμ ≤ ∫ (f - m)² dμ`. -/
private theorem lintegral_sub_integral_sq_le {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {f : E → ℝ} (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) (m : ℝ) :
    ∫⁻ x, ENNReal.ofReal ((f x - ∫ y, f y ∂μ) ^ 2) ∂μ ≤
      ∫⁻ x, ENNReal.ofReal ((f x - m) ^ 2) ∂μ := by
  have hval : ∀ a : ℝ, ∫ x, (f x - a) ^ 2 ∂μ =
      ∫ x, f x ^ 2 ∂μ - 2 * a * ∫ x, f x ∂μ + a ^ 2 := by
    intro a
    have : (fun x => (f x - a) ^ 2) = fun x => f x ^ 2 - 2 * a * f x + a ^ 2 := by
      ext x
      ring
    have hi1 : Integrable (fun x => f x ^ 2 - 2 * a * f x) μ := hf2.sub (hf.const_mul _)
    have hi2 : Integrable (fun x => 2 * a * f x) μ := hf.const_mul _
    rw [this, integral_add hi1 (integrable_const _), integral_sub hf2 hi2, integral_const_mul,
      integral_const]
    simp
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_sub_sq hf hf2 _)
      (Eventually.of_forall fun x => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal (integrable_sub_sq hf hf2 _)
      (Eventually.of_forall fun x => sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  rw [hval, hval]
  nlinarith [sq_nonneg (∫ x, f x ∂μ - m)]

/-! ### Cheeger's inequality -/

/-- **Cheeger's inequality.** Let $\mu$ be a probability measure on $\mathbb{R}^n$ and let
$\psi_\mu \in [0, \infty]$ be the inverse Cheeger constant of $\mu$. Then the smooth Poincaré
constant of $\mu$ is at most $4 \psi_\mu^2$.

Source: Klartag, arXiv:2303.14938v1, Introduction, inequality (4), which attributes the
inequality to Cheeger and states it for log-concave measures. -/
public theorem smoothPoincareConstant_le_four_mul_inverseCheegerConstant_sq {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ] :
    smoothPoincareConstant μ ≤ 4 * inverseCheegerConstant μ ^ 2 := by
  by_cases hψ : inverseCheegerConstant μ = ⊤
  · rw [hψ]
    simp
  have hh0 : cheegerCoefficient μ ≠ 0 := fun h => hψ (by simp [inverseCheegerConstant, h])
  apply smoothPoincareConstant_le_of_bound
  intro f hf hfi hf2 hdf
  set V := ∫⁻ x, ENNReal.ofReal ((f x - ∫ y, f y ∂μ) ^ 2) ∂μ with hV
  set J := ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2) ∂μ with hJ
  have hJtop : J ≠ ⊤ := by
    rw [hJ, ← ofReal_integral_eq_lintegral_ofReal hdf
      (Eventually.of_forall fun x => sq_nonneg _)]
    exact ENNReal.ofReal_ne_top
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast le_top)
  obtain ⟨m, hm1, hm2⟩ := exists_median μ hf1.continuous.measurable
  have hItop : ∫⁻ x, ENNReal.ofReal ((f x - m) ^ 2) ∂μ ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_sub_sq hfi hf2 m)
      (Eventually.of_forall fun x => sq_nonneg _)]
    exact ENNReal.ofReal_ne_top
  -- For every `0 < c ≤ h`, Cheeger's isoperimetric inequality gives `c² Var f ≤ 4 ∫ ‖∇f‖²`.
  have key : ∀ c : ℝ, 0 < c → ENNReal.ofReal c ≤ cheegerCoefficient μ →
      ENNReal.ofReal (c ^ 2) * V ≤ 4 * J := by
    intro c hc hch
    have hcA : ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A → 0 < μ A →
        μ A ≤ 2⁻¹ → ENNReal.ofReal c * μ A ≤ outerMinkowskiBoundary μ A := by
      intro A hA h0 h12
      have hlt : μ A < 1 := h12.trans_lt (ENNReal.inv_lt_one.mpr (by norm_num))
      have hmin : min (μ A) (1 - μ A) = μ A := by
        refine min_eq_left (ENNReal.le_sub_of_add_le_left (measure_ne_top μ A) ?_)
        calc μ A + μ A ≤ 2⁻¹ + 2⁻¹ := add_le_add h12 h12
          _ = 1 := ENNReal.inv_two_add_inv_two
      have h := hch.trans (sInf_le ⟨A, hA, h0, hlt, rfl⟩ : cheegerCoefficient μ ≤ _)
      rw [hmin] at h
      exact (ENNReal.le_div_iff_mul_le (Or.inl h0.ne') (Or.inl (measure_ne_top μ A))).mp h
    calc ENNReal.ofReal (c ^ 2) * V
        ≤ ENNReal.ofReal (c ^ 2) * ∫⁻ x, ENNReal.ofReal ((f x - m) ^ 2) ∂μ := by
          gcongr
          exact lintegral_sub_integral_sq_le μ hfi hf2 m
      _ ≤ 4 * J := sq_mul_lintegral_sub_median_le μ hc hcA hf1 hm1 hm2 hItop
  rcases eq_or_ne (cheegerCoefficient μ) ⊤ with htop | htop
  · -- An infinite Cheeger coefficient forces the variance to vanish.
    have hψ0 : inverseCheegerConstant μ = 0 := by simp [inverseCheegerConstant, htop]
    rw [hψ0, zero_pow two_ne_zero, mul_zero, zero_mul]
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    rw [zero_add]
    have hε' : (0 : ℝ) < ε := hε
    set c : ℝ := 4 * J.toReal / ε + 1 with hc
    have hc1 : 1 ≤ c := by
      have : 0 ≤ 4 * J.toReal / ε := by positivity
      linarith
    have hc0 : 0 < c := by linarith
    have hkey := key c hc0 (by rw [htop]; exact le_top)
    have hcε : 4 * J.toReal ≤ c ^ 2 * ε := by
      have h1 : c * ε = 4 * J.toReal + ε := by
        rw [hc, add_mul, div_mul_cancel₀ _ hε'.ne', one_mul]
      have h2 : c ^ 2 * ε = c * (4 * J.toReal + ε) := by
        rw [← h1]
        ring
      have h3 : 4 * J.toReal + ε ≤ c * (4 * J.toReal + ε) :=
        le_mul_of_one_le_left (by positivity) hc1
      linarith
    have h4J : 4 * J ≤ ENNReal.ofReal (c ^ 2) * ε := by
      rw [← ENNReal.ofReal_toReal hJtop, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul
        (by positivity), ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal hcε
    have hc2 : ENNReal.ofReal (c ^ 2) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    exact (ENNReal.mul_le_mul_iff_right hc2 ENNReal.ofReal_ne_top).mp (hkey.trans h4J)
  · -- Otherwise apply the bound with `c = h`.
    set c := (cheegerCoefficient μ).toReal with hc_def
    have hc : 0 < c := ENNReal.toReal_pos hh0 htop
    have hcc : ENNReal.ofReal c = cheegerCoefficient μ := ENNReal.ofReal_toReal htop
    have h1 := key c hc hcc.le
    have hψc : inverseCheegerConstant μ = (ENNReal.ofReal c)⁻¹ := by
      rw [hcc]
      rfl
    have hc2 : ENNReal.ofReal (c ^ 2) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    calc V = (ENNReal.ofReal (c ^ 2))⁻¹ * (ENNReal.ofReal (c ^ 2) * V) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hc2 ENNReal.ofReal_ne_top, one_mul]
      _ ≤ (ENNReal.ofReal (c ^ 2))⁻¹ * (4 * J) := by gcongr
      _ = 4 * inverseCheegerConstant μ ^ 2 * J := by
          rw [hψc, ← ENNReal.inv_pow, ← ENNReal.ofReal_pow hc.le]
          ring

set_option linter.unusedVariables false in
/-- **Cheeger's inequality for isotropic log-concave measures.** Let $n \ge 1$, let $\mu$ be an
isotropic log-concave probability measure on $\mathbb{R}^n$, and let $\psi_\mu \in [0, \infty]$ be
the inverse Cheeger constant of $\mu$. Then the smooth Poincaré constant of $\mu$ is at most
$4 \psi_\mu^2$.

Source: optimizationproblems `constants/20c.md`, comparison display, and
Klartag, arXiv:2303.14938v1, Introduction. -/
public theorem poincare_cheeger_upper_bound {n : ℕ} (hn : 0 < n)
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hμ : IsIsotropicLogConcave μ) :
    smoothPoincareConstant μ ≤ 4 * inverseCheegerConstant μ ^ 2 := by
  have : IsProbabilityMeasure μ := hμ.1
  exact smoothPoincareConstant_le_four_mul_inverseCheegerConstant_sq μ

end MathlibExt.Probability.KLS
