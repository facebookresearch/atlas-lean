/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Polynomial density passes to dominating functions in the Dirichlet space

This file proves `conjecture_holds`: if `f` and `g` lie in the Dirichlet space `𝒟` of the unit
disc, the polynomial multiples of `g` are dense in `𝒟` in the Dirichlet norm, and
`|g(z)| ≤ |f(z)|` for all `|z| < 1`, then the polynomial multiples of `f` are dense in `𝒟` as
well. This answers Hayman's Problem 8.11 positively, as Richter and Sundberg and, independently,
Aleman showed for the Dirichlet-type spaces `𝒟(μ)` (see the remark after Theorem 5.12 of
arXiv:2406.06182).

## Proof outline

The proof is elementary: it works with the area integral defining the Dirichlet norm and does not
use boundary values or the local Dirichlet integral.

* Since `|g| ≤ |f|`, removable singularities give a holomorphic `φ` with `|φ| ≤ 1` and
  `g = φ f` on the disc. Given `u ∈ 𝒟`, density of `Pg` gives a polynomial `q` with `q g` close
  to `u`, and `q g = ψ f` with `ψ = q φ` bounded and holomorphic. It remains to approximate
  `ψ f`, which lies in `𝒟`, by polynomial multiples of `f`.
* For `0 < r < 1`, the dilation `ψ_r(z) = ψ (r z)` is holomorphic on a disc of radius `> 1`, so
  its Taylor polynomials converge to it uniformly on the unit disc together with their
  derivatives (Cauchy estimates), and `p f → ψ_r f` in `𝒟` because `f` is square integrable on
  the disc.
* `ψ_r f → ψ f` in `𝒟` as `r → 1`. On the disc,
  `(ψ_r f)' - (ψ f)' = (ψ_r - ψ) f' + r ψ'(r z) (f(z) - f(r z)) + (T_r F - F)`, where
  `F = f ψ' = (ψ f)' - ψ f'` is square integrable and `T_r F(z) = r F(r z)`. The first term
  tends to `0` by dominated convergence, and the last by continuity of dilations on `L²` of the
  disc. For the middle term, the Cauchy estimate `|ψ'(w)| ≤ 2 sup |ψ| / (1 - |w|)` is combined
  with the bound `∫ |k(z) - k(r z)|² ≤ ((1 - r) / r)² ∫ |k'|²` (integrate `k'` along radii)
  applied to `k = f - f_s`, and with dominated convergence for the dilation `f_s(z) = f(s z)`,
  whose derivative is bounded on the disc.

## Source record

Clause list for [AMR-022-8011] Problem 8.11:
(a) functions analytic in |z| < 1; (b) finite Dirichlet integral;
(c) g is in D; (d) Pg (as defined in Problem 8.10) is dense in D;
(e) f is in D; (f) |f(z)| >= |g(z)| for all |z| < 1;
question: is Pf necessarily dense in D.
Density is in the Dirichlet norm
`‖u‖² = |u 0|² + ∫_{|z|<1} |u'(z)|²`, stated explicitly below rather
than via a topology on the subtype of all functions `ℂ → ℂ` (whose
inherited product topology would be the wrong one, and would make
values outside the disc matter). Membership `h ∈ Pg` likewise only
constrains values on the disc.
Context-only evidence (analogues in H^2 and A^2, Shields g = 1 case,
status/rights/difficulty metadata) is not formalized.

## References

* E. Fricain and R. Lebreton, *Cyclicity of the shift operator through Bezout identities*,
  arXiv:2406.06182 (2024), Theorem 5.12 and the remark after it, which attributes the result for
  `f, g ∈ 𝒟(μ)` to Richter and Sundberg (Michigan Math. J. 38 (1991) 355-379) and to Aleman.
-/

@[expose] public section

namespace MathlibExt.Analysis.DirichletSpacePolynomialDensityWanted

/-- **The Dirichlet space.** The Dirichlet space $\mathcal{D}$ consists of the functions
$f : \mathbb{C} \to \mathbb{C}$ that are analytic on the open unit disc $\{z : |z| < 1\}$ and have
finite Dirichlet integral: $|f'|^2$ is integrable on the disc with respect to Lebesgue (area)
measure. The values of $f$ outside the disc are unconstrained.

Source: `AMR-022-8011` (Hayman, Research Problems in Function Theory (2018), Problem 8.11,
https://arxiv.org/abs/1809.07200). -/
abbrev DirichletSpace := { f : ℂ → ℂ // AnalyticOn ℂ f (Metric.ball (0 : ℂ) 1) ∧
  MeasureTheory.IntegrableOn (fun z => ‖deriv f z‖ ^ 2) (Metric.ball (0 : ℂ) 1)
    MeasureTheory.volume }

/-- **Polynomial multiples of a function in the Dirichlet space.** For $g$ in the Dirichlet
space $\mathcal{D}$, the set $Pg$ consists of the functions $h \in \mathcal{D}$ for which there is
a polynomial $p$ with complex coefficients such that $h(z) = p(z) g(z)$ for all $|z| < 1$; only
values on the open unit disc are compared.

Source: `AMR-022-8011` (Hayman, Research Problems in Function Theory (2018), Problem 8.11, with
$Pg$ as defined in Problem 8.10), https://arxiv.org/abs/1809.07200. -/
def polyTimes (g : DirichletSpace) : Set DirichletSpace :=
  { h | ∃ p : Polynomial ℂ, ∀ z : ℂ, ‖z‖ < 1 → h.val z = p.eval z * g.val z }

/-- **Density in the Dirichlet norm.** A set $S$ of elements of the Dirichlet space $\mathcal{D}$
is dense in the Dirichlet norm when for every $u \in \mathcal{D}$ and every real $\varepsilon > 0$
there is $h \in S$ with
$$|h(0) - u(0)|^2 + \int_{|z| < 1} |h'(z) - u'(z)|^2 \, dA(z) < \varepsilon,$$
where $A$ is Lebesgue (area) measure on $\mathbb{C}$. -/
def IsDirichletDense (S : Set DirichletSpace) : Prop :=
  ∀ u : DirichletSpace, ∀ ε : ℝ, 0 < ε →
    ∃ h ∈ S, ‖h.val 0 - u.val 0‖ ^ 2 +
      (∫ z in Metric.ball (0 : ℂ) 1, ‖deriv h.val z - deriv u.val z‖ ^ 2
        ∂MeasureTheory.volume) < ε

/-- **Hayman's Problem 8.11: polynomial density under domination.** The statement that for all
$f$ and $g$ in the Dirichlet space $\mathcal{D}$: if the polynomial multiples $Pg$ are dense in
$\mathcal{D}$ in the Dirichlet norm and $|g(z)| \le |f(z)|$ for all $|z| < 1$, then the
polynomial multiples $Pf$ are also dense in $\mathcal{D}$ in the Dirichlet norm.

Source: the open question of `AMR-022-8011` (Hayman, Research Problems in Function Theory
(2018), Problem 8.11, https://arxiv.org/abs/1809.07200). -/
def conjecture : Prop :=
  ∀ (g f : DirichletSpace), IsDirichletDense (polyTimes g) →
    (∀ z : ℂ, ‖z‖ < 1 → ‖g.val z‖ ≤ ‖f.val z‖) → IsDirichletDense (polyTimes f)

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

/-- Change of variables `z ↦ r z` in a lower integral over `ℂ`. -/
private lemma lintegral_comp_real_smul (F : ℂ → ℝ≥0∞) {r : ℝ} (hr : r ≠ 0) :
    ∫⁻ z, F (r • z) = ENNReal.ofReal ((r ^ 2)⁻¹) * ∫⁻ z, F z := by
  have h1 := Measure.map_addHaar_smul (volume : Measure ℂ) hr
  rw [Complex.finrank_real_complex] at h1
  have h2 : |(r ^ 2)⁻¹| = (r ^ 2)⁻¹ := abs_of_nonneg (by positivity)
  rw [h2] at h1
  rw [← smul_eq_mul, ← lintegral_smul_measure, ← h1]
  exact (lintegral_map_equiv F (MeasurableEquiv.smul₀ r hr)).symm

/-- Cauchy–Schwarz for lower Lebesgue integrals against the constant `1`. -/
private lemma sq_lintegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {G : α → ℝ≥0∞}
    (hG : AEMeasurable G μ) : (∫⁻ a, G a ∂μ) ^ 2 ≤ μ univ * ∫⁻ a, G a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hG
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at h
  have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / (2 : ℝ))) ^ 2 = x := by
    intro x
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc (∫⁻ a, G a ∂μ) ^ 2
      ≤ ((∫⁻ a, G a ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * μ univ ^ (1 / (2 : ℝ))) ^ 2 := by
        gcongr
    _ = μ univ * ∫⁻ a, G a ^ 2 ∂μ := by
        rw [mul_pow, hsq, hsq, mul_comm]
        congr 1
        refine lintegral_congr fun a => ?_
        rw [← ENNReal.rpow_natCast]
        norm_num

/-- The crude bound: `∫_𝔻 |k(z) - k(rz)|² ≤ ((1-r)/r)² ∫_𝔻 |k'|²`. -/
private lemma lintegral_sub_dilate_le {k : ℂ → ℂ} (hk : DifferentiableOn ℂ k (ball 0 1)) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    ∫⁻ z in ball (0 : ℂ) 1, ‖k z - k (r * z)‖ₑ ^ 2 ≤
      ENNReal.ofReal (((1 - r) / r) ^ 2) * ∫⁻ z in ball (0 : ℂ) 1, ‖deriv k z‖ₑ ^ 2 := by
  set I := ∫⁻ z in ball (0 : ℂ) 1, ‖deriv k z‖ₑ ^ 2 with hI
  have hkd : DifferentiableOn ℂ (deriv k) (ball 0 1) := hk.deriv isOpen_ball
  have hmeas : Measurable fun p : ℂ × ℝ => ‖deriv k ((p.2 : ℂ) * p.1)‖ₑ ^ 2 :=
    (((measurable_deriv k).comp ((Complex.continuous_ofReal.comp continuous_snd).mul
      continuous_fst).measurable).eNorm).pow_const 2
  -- pointwise bound
  have hpt : ∀ z ∈ ball (0 : ℂ) 1, ‖k z - k (r * z)‖ₑ ^ 2 ≤
      ENNReal.ofReal (1 - r) * ∫⁻ t in Ioc r 1, ‖deriv k ((t : ℂ) * z)‖ₑ ^ 2 := by
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hmem : ∀ t ∈ uIcc r 1, (t : ℂ) * z ∈ ball (0 : ℂ) 1 := by
      intro t ht
      rw [uIcc_of_le hr1.le] at ht
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hr0.le.trans ht.1)]
      calc t * ‖z‖ ≤ 1 * ‖z‖ := by gcongr; exact ht.2
        _ < 1 := by simpa using hz1
    have hderiv : ∀ t ∈ uIcc r 1, HasDerivAt (fun t : ℝ => k ((t : ℂ) * z))
        (deriv k ((t : ℂ) * z) * z) t := by
      intro t ht
      have hkt : HasDerivAt k (deriv k ((t : ℂ) * z)) ((t : ℂ) * z) :=
        (hk.differentiableAt (isOpen_ball.mem_nhds (hmem t ht))).hasDerivAt
      have h2 : HasDerivAt (fun w : ℂ => k (w * z)) (deriv k ((t : ℂ) * z) * z) (t : ℂ) := by
        have := hkt.comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).mul_const z)
        simpa [Function.comp_def] using this
      exact h2.comp_ofReal
    have hcont : ContinuousOn (fun t : ℝ => deriv k ((t : ℂ) * z) * z) (uIcc r 1) := by
      refine ContinuousOn.mul ?_ continuousOn_const
      refine hkd.continuousOn.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn
        ?_
      intro t ht
      exact hmem t ht
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)
    simp only [Complex.ofReal_one, one_mul] at hftc
    have h1 : ‖k z - k (r * z)‖ₑ ≤ ∫⁻ t in Ioc r 1, ‖deriv k ((t : ℂ) * z)‖ₑ := by
      rw [← hftc, intervalIntegral.integral_of_le hr1.le]
      refine (eNorm_integral_le_lintegral_eNorm _).trans ?_
      refine lintegral_mono fun t => ?_
      rw [eNorm_mul]
      calc ‖deriv k ((t : ℂ) * z)‖ₑ * ‖z‖ₑ ≤ ‖deriv k ((t : ℂ) * z)‖ₑ * 1 := by
            gcongr
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_one.mpr hz1.le
        _ = _ := mul_one _
    have hG : AEMeasurable (fun t : ℝ => ‖deriv k ((t : ℂ) * z)‖ₑ)
        (volume.restrict (Ioc r 1)) :=
      ((measurable_deriv k).comp (Complex.continuous_ofReal.mul
        continuous_const).measurable).eNorm.aemeasurable
    calc ‖k z - k (r * z)‖ₑ ^ 2 ≤ (∫⁻ t in Ioc r 1, ‖deriv k ((t : ℂ) * z)‖ₑ) ^ 2 := by
          gcongr
      _ ≤ (volume.restrict (Ioc r 1)) univ *
            ∫⁻ t in Ioc r 1, ‖deriv k ((t : ℂ) * z)‖ₑ ^ 2 := sq_lintegral_le _ hG
      _ = ENNReal.ofReal (1 - r) * ∫⁻ t in Ioc r 1, ‖deriv k ((t : ℂ) * z)‖ₑ ^ 2 := by
          rw [Measure.restrict_apply_univ, Real.volume_Ioc]
  -- scaling bound
  have hscale : ∀ t ∈ Ioc r 1, ∫⁻ z in ball (0 : ℂ) 1, ‖deriv k ((t : ℂ) * z)‖ₑ ^ 2 ≤
      ENNReal.ofReal ((r ^ 2)⁻¹) * I := by
    intro t ht
    have ht0 : 0 < t := hr0.trans ht.1
    rw [← lintegral_indicator measurableSet_ball]
    calc ∫⁻ z, (ball (0 : ℂ) 1).indicator (fun z => ‖deriv k ((t : ℂ) * z)‖ₑ ^ 2) z
        ≤ ∫⁻ z, (ball (0 : ℂ) 1).indicator (fun w => ‖deriv k w‖ₑ ^ 2) (t • z) := by
          refine lintegral_mono fun z => ?_
          by_cases hz : z ∈ ball (0 : ℂ) 1
          · have htz : t • z ∈ ball (0 : ℂ) 1 := by
              rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
              calc t * ‖z‖ ≤ 1 * ‖z‖ := by gcongr; exact ht.2
                _ < 1 := by simpa using mem_ball_zero_iff.mp hz
            rw [indicator_of_mem hz, indicator_of_mem htz, Complex.real_smul]
          · rw [indicator_of_notMem hz]
            exact zero_le
      _ = ENNReal.ofReal ((t ^ 2)⁻¹) * I := by
          rw [lintegral_comp_real_smul _ ht0.ne', lintegral_indicator measurableSet_ball]
      _ ≤ ENNReal.ofReal ((r ^ 2)⁻¹) * I := by
          gcongr
          exact ht.1.le
  calc ∫⁻ z in ball (0 : ℂ) 1, ‖k z - k (r * z)‖ₑ ^ 2
      ≤ ∫⁻ z in ball (0 : ℂ) 1,
          ENNReal.ofReal (1 - r) * ∫⁻ t in Ioc r 1, ‖deriv k ((t : ℂ) * z)‖ₑ ^ 2 :=
        setLIntegral_mono' measurableSet_ball hpt
    _ = ENNReal.ofReal (1 - r) *
          ∫⁻ t in Ioc r 1, ∫⁻ z in ball (0 : ℂ) 1, ‖deriv k ((t : ℂ) * z)‖ₑ ^ 2 := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        apply lintegral_lintegral_swap
        exact hmeas.aemeasurable
    _ ≤ ENNReal.ofReal (1 - r) * ∫⁻ t in Ioc r 1, ENNReal.ofReal ((r ^ 2)⁻¹) * I := by
        exact mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Ioc hscale)
    _ = ENNReal.ofReal (((1 - r) / r) ^ 2) * I := by
        rw [setLIntegral_const, Real.volume_Ioc]
        have h1r : (0 : ℝ) ≤ 1 - r := by linarith
        calc ENNReal.ofReal (1 - r) * (ENNReal.ofReal ((r ^ 2)⁻¹) * I * ENNReal.ofReal (1 - r))
            = (ENNReal.ofReal (1 - r) * ENNReal.ofReal (1 - r) * ENNReal.ofReal ((r ^ 2)⁻¹))
                * I := by ring
          _ = ENNReal.ofReal (((1 - r) / r) ^ 2) * I := by
            rw [← ENNReal.ofReal_mul h1r, ← ENNReal.ofReal_mul (by positivity)]
            congr 2
            field_simp

/-- `‖a + b‖² ≤ 2 ‖a‖² + 2 ‖b‖²` for extended norms. -/
private lemma enorm_add_sq_le {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a + b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  have h2 := ENNReal.rpow_add_le_mul_rpow_add_rpow ‖a‖ₑ ‖b‖ₑ (p := 2) (by norm_num)
  norm_num at h2
  calc ‖a + b‖ₑ ^ 2 ≤ (‖a‖ₑ + ‖b‖ₑ) ^ 2 := by gcongr; exact eNorm_add_le a b
    _ ≤ 2 * (‖a‖ₑ ^ 2 + ‖b‖ₑ ^ 2) := by exact_mod_cast h2
    _ = 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := mul_add _ _ _

/-- Functions in the Dirichlet space are square integrable on the disc. -/
private lemma lintegral_norm_sq_lt_top {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hf' : ∫⁻ z in ball (0 : ℂ) 1, ‖deriv f z‖ₑ ^ 2 < ∞) :
    ∫⁻ z in ball (0 : ℂ) 1, ‖f z‖ₑ ^ 2 < ∞ := by
  obtain ⟨B, hB⟩ : ∃ B, ∀ w ∈ closedBall (0 : ℂ) (1 / 2), ‖f w‖ ≤ B :=
    (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_bound_of_continuousOn
      (hf.continuousOn.mono (closedBall_subset_ball (by norm_num)))
  have hcrude := lintegral_sub_dilate_le hf (r := 1 / 2) (by norm_num) (by norm_num)
  have hpt : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ₑ ^ 2 ≤
      2 * ‖f z - f (((1 / 2 : ℝ) : ℂ) * z)‖ₑ ^ 2 + 2 * ENNReal.ofReal B ^ 2 := by
    intro z hz
    have hz' : ((1 / 2 : ℝ) : ℂ) * z ∈ closedBall (0 : ℂ) (1 / 2) := by
      rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have := (mem_ball_zero_iff.mp hz).le
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      nlinarith
    have h1 := enorm_add_sq_le (f z - f (((1 / 2 : ℝ) : ℂ) * z)) (f (((1 / 2 : ℝ) : ℂ) * z))
    rw [sub_add_cancel] at h1
    refine h1.trans ?_
    gcongr
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hB _ hz')
  calc ∫⁻ z in ball (0 : ℂ) 1, ‖f z‖ₑ ^ 2
      ≤ ∫⁻ z in ball (0 : ℂ) 1,
          (2 * ‖f z - f (((1 / 2 : ℝ) : ℂ) * z)‖ₑ ^ 2 + 2 * ENNReal.ofReal B ^ 2) :=
        setLIntegral_mono' measurableSet_ball hpt
    _ = 2 * (∫⁻ z in ball (0 : ℂ) 1, ‖f z - f (((1 / 2 : ℝ) : ℂ) * z)‖ₑ ^ 2) +
          2 * ENNReal.ofReal B ^ 2 * volume (ball (0 : ℂ) 1) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by norm_num),
          setLIntegral_const]
    _ < ∞ := by
        have h2 : (2 : ℝ≥0∞) < ∞ := by simp
        refine ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top h2 ?_, ?_⟩
        · exact hcrude.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf')
        · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top h2
            (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)) measure_ball_lt_top

/-- A positive extended real `η` with `c * η ≤ ε`. -/
private lemma exists_small (ε : ℝ≥0∞) (hε : 0 < ε) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    ∃ η : ℝ≥0∞, 0 < η ∧ η ≠ ∞ ∧ c * η ≤ ε := by
  refine ⟨min 1 (ε / c), lt_min one_pos (ENNReal.div_pos hε.ne' hc), ?_, ?_⟩
  · exact (lt_of_le_of_lt (min_le_left _ _) ENNReal.one_lt_top).ne
  · calc c * min 1 (ε / c) ≤ c * (ε / c) := by gcongr; exact min_le_right _ _
      _ = ε := ENNReal.mul_div_cancel hc0 hc

/-- The squared extended norm of a real multiple. -/
private lemma enorm_ofReal_mul_sq (r : ℝ) (x : ℂ) :
    ‖(r : ℂ) * x‖ₑ ^ 2 = ENNReal.ofReal (r ^ 2) * ‖x‖ₑ ^ 2 := by
  rw [eNorm_mul, mul_pow, ← ofReal_norm (r : ℂ), Complex.norm_real, Real.norm_eq_abs,
    ← ENNReal.ofReal_pow (abs_nonneg r), sq_abs]

/-- Dilations are continuous on `L²` of the disc. -/
private lemma tendsto_lintegral_dilate {F : ℂ → ℂ} (hFm : Measurable F)
    (hF : ∫⁻ z in ball (0 : ℂ) 1, ‖F z‖ₑ ^ 2 < ∞) :
    Tendsto (fun r : ℝ => ∫⁻ z in ball (0 : ℂ) 1, ‖(r : ℂ) * F (r * z) - F z‖ₑ ^ 2)
      (𝓝[<] 1) (𝓝 0) := by
  set G := (ball (0 : ℂ) 1).indicator F with hGdef
  have hGm : Measurable G := hFm.indicator measurableSet_ball
  have hGint : ∫⁻ z, ‖G z‖ₑ ^ 2 = ∫⁻ z in ball (0 : ℂ) 1, ‖F z‖ₑ ^ 2 := by
    rw [← lintegral_indicator measurableSet_ball]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ ball (0 : ℂ) 1 <;> simp [G, hz]
  have hGLp : MemLp G 2 volume := by
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero
      ENNReal.ofNat_ne_top hGm.aestronglyMeasurable]
    simpa [hGint] using hF
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨η, hη0, hηtop, hηε⟩ := exists_small ε hε 10 (by norm_num) (by norm_num)
  have hsqrt : (η ^ (1 / (2 : ℝ))) ≠ 0 := (ENNReal.rpow_pos hη0 hηtop).ne'
  obtain ⟨H, hHsupp, hGH, hHcont, -⟩ :=
    hGLp.exists_hasCompactSupport_eLpNorm_sub_le ENNReal.ofNat_ne_top hsqrt
  have hGH' : ∫⁻ z, ‖G z - H z‖ₑ ^ 2 ≤ η := by
    have h := eLpNorm_nnreal_pow_eq_lintegral (p := 2) (μ := volume) (f := G - H)
      two_ne_zero (hGm.aestronglyMeasurable.sub hHcont.aestronglyMeasurable)
    have h2 : ((2 : ℝ≥0) : ℝ≥0∞) = 2 := rfl
    simp only [h2, NNReal.coe_ofNat, Pi.sub_apply] at h
    have h3 : ∫⁻ z, ‖G z - H z‖ₑ ^ 2 = ∫⁻ z, ‖G z - H z‖ₑ ^ (2 : ℝ) := by
      refine lintegral_congr fun z => ?_
      rw [← ENNReal.rpow_natCast]
      norm_num
    rw [h3, ← h]
    calc eLpNorm (G - H) 2 volume ^ (2 : ℝ) ≤ (η ^ (1 / (2 : ℝ))) ^ (2 : ℝ) := by
          gcongr
      _ = η := by rw [← ENNReal.rpow_mul]; norm_num
  obtain ⟨C, hC⟩ := hHcont.bounded_above_of_compact_support hHsupp
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hDCT : Tendsto (fun r : ℝ => ∫⁻ z in ball (0 : ℂ) 1, ‖(r : ℂ) * H (r * z) - H z‖ₑ ^ 2)
      (𝓝[<] 1) (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence
      (μ := volume.restrict (ball (0 : ℂ) 1)) (l := 𝓝[<] (1 : ℝ))
      (F := fun r : ℝ => fun z => ‖(r : ℂ) * H (r * z) - H z‖ₑ ^ 2) (f := fun _ => 0)
      (fun _ => ENNReal.ofReal ((2 * C) ^ 2)) ?_ ?_ ?_ ?_
    · simpa using h
    · refine Eventually.of_forall fun r => ?_
      exact ((measurable_const.mul (hHcont.measurable.comp
        (measurable_const.mul measurable_id))).sub hHcont.measurable).eNorm.pow_const 2
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
      refine Eventually.of_forall fun z => ?_
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : ‖(r : ℂ) * H (r * z) - H z‖ ≤ 2 * C := by
        calc ‖(r : ℂ) * H (r * z) - H z‖ ≤ ‖(r : ℂ) * H (r * z)‖ + ‖H z‖ := norm_sub_le _ _
          _ ≤ 1 * C + C := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
              gcongr
              · exact hr.2.le
              · exact hC _
              · exact hC _
          _ = 2 * C := by ring
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    · rw [setLIntegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
    · refine Eventually.of_forall fun z => ?_
      have hc : Continuous fun r : ℝ => ‖(r : ℂ) * H (r * z) - H z‖ₑ ^ 2 :=
        (ENNReal.continuous_pow 2).comp ((Complex.continuous_ofReal.mul (hHcont.comp
          (Complex.continuous_ofReal.mul continuous_const))).sub continuous_const).eNorm
      have := hc.tendsto 1
      simp only [Complex.ofReal_one, one_mul, sub_self, eNorm_zero] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa using this)
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hDCT) η hη0,
    Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hrH hr
  have hr0 : r ≠ 0 := hr.1.ne'
  have hpt : ∀ z ∈ ball (0 : ℂ) 1, ‖(r : ℂ) * F (r * z) - F z‖ₑ ^ 2 ≤
      2 * ‖(r : ℂ) * (G (r * z) - H (r * z))‖ₑ ^ 2 +
        (4 * ‖(r : ℂ) * H (r * z) - H z‖ₑ ^ 2 + 4 * ‖G z - H z‖ₑ ^ 2) := by
    intro z hz
    have hrz : (r : ℂ) * z ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
      calc r * ‖z‖ ≤ 1 * ‖z‖ := by gcongr; exact hr.2.le
        _ < 1 := by simpa using mem_ball_zero_iff.mp hz
    have hFG1 : F (r * z) = G (r * z) := by simp [G, hrz]
    have hFG2 : F z = G z := by simp [G, hz]
    have heq : (r : ℂ) * F (r * z) - F z = (r : ℂ) * (G (r * z) - H (r * z)) +
        (((r : ℂ) * H (r * z) - H z) + (H z - G z)) := by
      rw [hFG1, hFG2]; ring
    rw [heq]
    refine (enorm_add_sq_le _ _).trans ?_
    gcongr
    have hb : ‖H z - G z‖ₑ = ‖G z - H z‖ₑ := by rw [← eNorm_neg, neg_sub]
    calc 2 * ‖(r : ℂ) * H (r * z) - H z + (H z - G z)‖ₑ ^ 2
        ≤ 2 * (2 * ‖(r : ℂ) * H (r * z) - H z‖ₑ ^ 2 + 2 * ‖H z - G z‖ₑ ^ 2) := by
          gcongr; exact enorm_add_sq_le _ _
      _ = 4 * ‖(r : ℂ) * H (r * z) - H z‖ₑ ^ 2 + 4 * ‖G z - H z‖ₑ ^ 2 := by rw [hb]; ring
  have hm1 : Measurable fun z : ℂ => ‖(r : ℂ) * (G (r * z) - H (r * z))‖ₑ ^ 2 :=
    ((measurable_const.mul ((hGm.comp (measurable_const.mul measurable_id)).sub
      (hHcont.measurable.comp (measurable_const.mul measurable_id)))).eNorm).pow_const 2
  have hm2 : Measurable fun z : ℂ => ‖(r : ℂ) * H (r * z) - H z‖ₑ ^ 2 :=
    ((measurable_const.mul (hHcont.measurable.comp (measurable_const.mul measurable_id))).sub
      hHcont.measurable).eNorm.pow_const 2
  have hm3 : Measurable fun z : ℂ => ‖G z - H z‖ₑ ^ 2 :=
    (hGm.sub hHcont.measurable).eNorm.pow_const 2
  have hA : ∫⁻ z in ball (0 : ℂ) 1, ‖(r : ℂ) * (G (r * z) - H (r * z))‖ₑ ^ 2 ≤ η := by
    refine (setLIntegral_le_lintegral _ _).trans ?_
    calc ∫⁻ z, ‖(r : ℂ) * (G (r * z) - H (r * z))‖ₑ ^ 2
        = ∫⁻ z, ENNReal.ofReal (r ^ 2) * ‖G (r • z) - H (r • z)‖ₑ ^ 2 := by
          refine lintegral_congr fun z => ?_
          rw [enorm_ofReal_mul_sq, Complex.real_smul]
      _ = ENNReal.ofReal (r ^ 2) * (ENNReal.ofReal ((r ^ 2)⁻¹) *
            ∫⁻ z, ‖G z - H z‖ₑ ^ 2) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_comp_real_smul (fun z => ‖G z - H z‖ₑ ^ 2) hr0]
      _ = ∫⁻ z, ‖G z - H z‖ₑ ^ 2 := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity),
            ENNReal.ofReal_one, one_mul]
      _ ≤ η := hGH'
  have hC3 : ∫⁻ z in ball (0 : ℂ) 1, ‖G z - H z‖ₑ ^ 2 ≤ η :=
    (setLIntegral_le_lintegral _ _).trans hGH'
  calc ∫⁻ z in ball (0 : ℂ) 1, ‖(r : ℂ) * F (r * z) - F z‖ₑ ^ 2
      ≤ ∫⁻ z in ball (0 : ℂ) 1, (2 * ‖(r : ℂ) * (G (r * z) - H (r * z))‖ₑ ^ 2 +
          (4 * ‖(r : ℂ) * H (r * z) - H z‖ₑ ^ 2 + 4 * ‖G z - H z‖ₑ ^ 2)) :=
        setLIntegral_mono' measurableSet_ball hpt
    _ = 2 * (∫⁻ z in ball (0 : ℂ) 1, ‖(r : ℂ) * (G (r * z) - H (r * z))‖ₑ ^ 2) +
          (4 * (∫⁻ z in ball (0 : ℂ) 1, ‖(r : ℂ) * H (r * z) - H z‖ₑ ^ 2) +
            4 * (∫⁻ z in ball (0 : ℂ) 1, ‖G z - H z‖ₑ ^ 2)) := by
        rw [lintegral_add_left (hm1.const_mul 2), lintegral_add_left (hm2.const_mul 4),
          lintegral_const_mul _ hm1, lintegral_const_mul _ hm2, lintegral_const_mul _ hm3]
    _ ≤ 2 * η + (4 * η + 4 * η) := by gcongr
    _ = 10 * η := by ring
    _ ≤ ε := hηε

/-- Cauchy estimate with a factor 2. -/
private lemma norm_deriv_le_of_bound {h : ℂ → ℂ} {c : ℂ} {R C : ℝ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ h (ball c R)) (hb : ∀ w ∈ ball c R, ‖h w‖ ≤ C) :
    ‖deriv h c‖ ≤ 2 * C / R := by
  have hR2 : 0 < R / 2 := half_pos hR
  have hsub : closedBall c (R / 2) ⊆ ball c R := closedBall_subset_ball (by linarith)
  have hdc : DiffContOnCl ℂ h (ball c (R / 2)) :=
    (hd.mono (closure_ball_subset_closedBall.trans hsub)).diffContOnCl
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR2 hdc
    (fun z hz => hb z (hsub (sphere_subset_closedBall hz)))
  calc ‖deriv h c‖ ≤ C / (R / 2) := this
    _ = 2 * C / R := by field_simp

/-- A function dominated by an analytic function on the disc is an analytic multiple of it. -/
private lemma exists_bounded_quotient {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hgf : ∀ z ∈ ball (0 : ℂ) 1, ‖g z‖ ≤ ‖f z‖) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ (ball 0 1) ∧ (∀ z ∈ ball (0 : ℂ) 1, ‖φ z‖ ≤ 1) ∧
      ∀ z ∈ ball (0 : ℂ) 1, g z = φ z * f z := by
  by_cases h0 : ∀ z ∈ ball (0 : ℂ) 1, f z = 0
  · refine ⟨0, differentiableOn_const 0, fun z _ => by simp, fun z hz => ?_⟩
    have := hgf z hz
    rw [h0 z hz, norm_zero] at this
    simpa using norm_le_zero_iff.mp this
  push Not at h0
  obtain ⟨z₀, hz₀, hfz₀⟩ := h0
  have hfa : AnalyticOnNhd ℂ f (ball 0 1) := hf.analyticOnNhd isOpen_ball
  -- zeros of `f` are isolated in the disc
  have hiso : ∀ z ∈ ball (0 : ℂ) 1, ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 := by
    intro z hz
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    simp only [ne_eq, not_not] at hcon
    exact hfz₀ (hfa.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (convex_ball (0 : ℂ) 1).isPreconnected hz hcon hz₀)
  set q : ℂ → ℂ := fun w => g w / f w with hq
  have hqd : ∀ w ∈ ball (0 : ℂ) 1, f w ≠ 0 → DifferentiableAt ℂ q w := fun w hw hfw =>
    ((hg.differentiableAt (isOpen_ball.mem_nhds hw)).div
      (hf.differentiableAt (isOpen_ball.mem_nhds hw)) hfw)
  have hqb : ∀ w ∈ ball (0 : ℂ) 1, f w ≠ 0 → ‖q w‖ ≤ 1 := fun w hw hfw => by
    rw [hq, norm_div]
    exact div_le_one_of_le₀ (hgf w hw) (norm_nonneg _)
  refine ⟨fun z => limUnder (𝓝[≠] z) q, ?_, ?_, ?_⟩
  · -- differentiability
    intro z hz
    -- a punctured neighbourhood of `z` inside the disc on which `f ≠ 0`
    obtain ⟨ε, hε0, hε⟩ : ∃ ε > 0, ball z ε ⊆ ball (0 : ℂ) 1 ∧
        ∀ w ∈ ball z ε, w ≠ z → f w ≠ 0 := by
      have h1 := hiso z hz
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at h1
      obtain ⟨ε₁, hε₁, h1⟩ := h1
      obtain ⟨ε₂, hε₂, h2⟩ := Metric.isOpen_iff.1 isOpen_ball z hz
      refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (ball_subset_ball (min_le_right _ _)).trans h2,
        fun w hw hwz => h1 w (ball_subset_ball (min_le_left _ _) hw) hwz⟩
    have hd : DifferentiableOn ℂ q (ball z ε \ {z}) := fun w hw =>
      (hqd w (hε.1 hw.1) (hε.2 w hw.1 hw.2)).differentiableWithinAt
    have hb : BddAbove (norm ∘ q '' (ball z ε \ {z})) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨w, hw, rfl⟩
      exact hqb w (hε.1 hw.1) (hε.2 w hw.1 hw.2)
    have hU := Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds z hε0) hd hb
    have hloc : (Function.update q z (limUnder (𝓝[≠] z) q)) =ᶠ[𝓝 z]
        fun z' => limUnder (𝓝[≠] z') q := by
      filter_upwards [ball_mem_nhds z hε0] with w hw
      by_cases hwz : w = z
      · subst hwz; simp
      · rw [Function.update_of_ne hwz]
        have hfw := hε.2 w hw hwz
        have hcont : ContinuousAt q w := (hqd w (hε.1 hw) hfw).continuousAt
        exact (hcont.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq.symm
    exact ((hU.differentiableAt (ball_mem_nhds z hε0)).congr_of_eventuallyEq
      hloc.symm).differentiableWithinAt
  · -- bound
    intro z hz
    by_cases hfz : f z ≠ 0
    · have hcont : ContinuousAt q z := (hqd z hz hfz).continuousAt
      change ‖limUnder (𝓝[≠] z) q‖ ≤ 1
      rw [(hcont.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq]
      exact hqb z hz hfz
    · push Not at hfz
      have hd : ∀ᶠ w in 𝓝[≠] z, DifferentiableAt ℂ q w := by
        filter_upwards [hiso z hz, nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz)] with w hw hw'
        exact hqd w hw' hw
      have hbd : ∀ᶠ w in 𝓝[≠] z, ‖q w‖ ≤ 1 := by
        filter_upwards [hiso z hz, nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz)] with w hw hw'
        exact hqb w hw' hw
      have hlim := Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under
        hd ⟨1 + ‖q z‖, eventually_map.2 (by
          filter_upwards [hbd] with w hw
          exact (norm_sub_le _ _).trans (by linarith))⟩
      exact le_of_tendsto hlim.norm hbd
  · -- factorisation
    intro z hz
    by_cases hfz : f z ≠ 0
    · have hcont : ContinuousAt q z := (hqd z hz hfz).continuousAt
      simp only
      rw [(hcont.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq, hq]
      field_simp
    · push Not at hfz
      have := hgf z hz
      rw [hfz, norm_zero] at this
      rw [norm_le_zero_iff.mp this, hfz, mul_zero]

/-- Taylor polynomials approximate a dilation `ψ (r ·)` and its derivative uniformly on the
disc. -/
private lemma exists_poly_approx {ψ : ℂ → ℂ} (hψ : DifferentiableOn ℂ ψ (ball 0 1)) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : Polynomial ℂ, ∀ z ∈ ball (0 : ℂ) 1, ‖p.eval z - ψ (r * z)‖ ≤ δ ∧
      ‖deriv (fun w => p.eval w - ψ (r * w)) z‖ ≤ δ := by
  set ρ : ℝ≥0 := ⟨(1 + r) / 2, by positivity⟩ with hρdef
  have hρv : (ρ : ℝ) = (1 + r) / 2 := rfl
  have hρ1 : (ρ : ℝ) < 1 := by rw [hρv]; linarith
  have hρr : r < (ρ : ℝ) := by rw [hρv]; linarith
  have hρ0 : 0 < ρ := by rw [← NNReal.coe_pos, hρv]; linarith
  have hps := (hψ.mono (closedBall_subset_ball hρ1)).hasFPowerSeriesOnBall hρ0
  set P := cauchyPowerSeries ψ 0 ρ
  set ρ' : ℝ≥0 := ⟨(r + ρ) / 2, by positivity⟩ with hρ'def
  have hρ'v : (ρ' : ℝ) = (r + ρ) / 2 := rfl
  have hρ'ρ : (ρ' : ℝ) < ρ := by rw [hρ'v]; linarith
  have hρ'r : r < (ρ' : ℝ) := by rw [hρ'v]; linarith
  have hunif := hps.tendstoUniformlyOn (r' := ρ') (by exact_mod_cast hρ'ρ)
  set R : ℝ := ρ' / r with hRdef
  have hR1 : 1 < R := by rw [hRdef, one_lt_div hr0]; exact hρ'r
  set η : ℝ := min δ (δ * (R - 1) / 2) with hηdef
  have hη0 : 0 < η := lt_min hδ (by nlinarith)
  have hηR : η ≤ δ * (R - 1) / 2 := min_le_right _ _
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.1 hunif η hη0).exists
  set p : Polynomial ℂ := ∑ k ∈ Finset.range n,
    Polynomial.C (P.coeff k * (r : ℂ) ^ k) * Polynomial.X ^ k with hpdef
  have hpeval : ∀ z, p.eval z = P.partialSum n ((r : ℂ) * z) := by
    intro z
    rw [hpdef, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      FormalMultilinearSeries.partialSum, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  -- the bound on the disc of radius `R`
  have hbound : ∀ w ∈ ball (0 : ℂ) R, ‖p.eval w - ψ (r * w)‖ ≤ η := by
    intro w hw
    have hrw : (r : ℂ) * w ∈ ball (0 : ℂ) ρ' := by
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      have := mem_ball_zero_iff.mp hw
      calc r * ‖w‖ < r * R := by gcongr
        _ = ρ' := by rw [hRdef]; field_simp
    have := hn _ hrw
    rw [dist_comm, dist_eq_norm, zero_add] at this
    rw [hpeval]
    exact this.le
  refine ⟨p, fun z hz => ⟨?_, ?_⟩⟩
  · have hz' : z ∈ ball (0 : ℂ) R :=
      ball_subset_ball hR1.le hz
    exact (hbound z hz').trans (min_le_left _ _)
  · have hsub : ball z (R - 1) ⊆ ball (0 : ℂ) R := by
      intro w hw
      rw [mem_ball_zero_iff]
      have h1 := mem_ball_zero_iff.mp hz
      have h2 : ‖w - z‖ < R - 1 := by rw [← dist_eq_norm]; exact hw
      calc ‖w‖ = ‖(w - z) + z‖ := by ring_nf
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        _ < R := by linarith
    have hdiff : DifferentiableOn ℂ (fun w => p.eval w - ψ (r * w)) (ball z (R - 1)) := by
      intro w hw
      have hw' := hsub hw
      have hrw : (r : ℂ) * w ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
        have := mem_ball_zero_iff.mp hw'
        calc r * ‖w‖ < r * R := by gcongr
          _ = ρ' := by rw [hRdef]; field_simp
          _ < 1 := hρ'ρ.trans hρ1
      refine ((Polynomial.differentiable p).differentiableAt.sub ?_).differentiableWithinAt
      exact (hψ.differentiableAt (isOpen_ball.mem_nhds hrw)).comp w
        ((differentiableAt_id).const_mul (r : ℂ))
    have hC := norm_deriv_le_of_bound (by linarith) hdiff (fun w hw => hbound w (hsub hw))
    calc ‖deriv (fun w => p.eval w - ψ (r * w)) z‖ ≤ 2 * η / (R - 1) := hC
      _ ≤ 2 * (δ * (R - 1) / 2) / (R - 1) := by
          apply div_le_div_of_nonneg_right _ (by linarith)
          linarith
      _ = δ := by field_simp

/-- Multiplication by `t ∈ [0, 1]` maps the unit disc into itself. -/
private lemma mapsTo_mul_ball {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    MapsTo (fun z : ℂ => (t : ℂ) * z) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  intro z hz
  simp only [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht0] at hz ⊢
  calc t * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
    _ < 1 := by simpa using hz

/-- Continuity on the disc is preserved by the dilation `z ↦ t z`, `t ∈ [0, 1]`. -/
private lemma continuousOn_comp_mul {g : ℂ → ℂ} {t : ℝ} (hg : ContinuousOn g (ball (0 : ℂ) 1))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ContinuousOn (fun z => g ((t : ℂ) * z)) (ball (0 : ℂ) 1) :=
  hg.comp (continuous_const.mul continuous_id).continuousOn (mapsTo_mul_ball ht0 ht1)

/-- Cauchy estimate for a bounded holomorphic function at `r z`. -/
private lemma norm_mul_deriv_le {ψ : ℂ → ℂ} {M : ℝ} (hψ : DifferentiableOn ℂ ψ (ball 0 1))
    (hM : ∀ z ∈ ball (0 : ℂ) 1, ‖ψ z‖ ≤ M) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    ‖(r : ℂ) * deriv ψ (r * z)‖ ≤ 2 * M / (1 - r * ‖z‖) := by
  have hz1 := mem_ball_zero_iff.mp hz
  have hrz : ‖(r : ℂ) * z‖ = r * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hpos : 0 < 1 - r * ‖z‖ := by nlinarith [norm_nonneg z]
  have hsub : ball ((r : ℂ) * z) (1 - r * ‖z‖) ⊆ ball 0 1 := by
    intro w hw
    rw [mem_ball_zero_iff]
    rw [mem_ball, dist_eq_norm] at hw
    calc ‖w‖ = ‖(w - r * z) + r * z‖ := by ring_nf
      _ ≤ ‖w - r * z‖ + ‖(r : ℂ) * z‖ := norm_add_le _ _
      _ < 1 := by rw [hrz]; linarith
  have hC := norm_deriv_le_of_bound hpos (hψ.mono hsub) (fun w hw => hM w (hsub hw))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (mem_ball_self one_pos))
  calc ‖(r : ℂ) * deriv ψ (r * z)‖ = r * ‖deriv ψ (r * z)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    _ ≤ 1 * (2 * M / (1 - r * ‖z‖)) := by
        gcongr
    _ = 2 * M / (1 - r * ‖z‖) := one_mul _

/-- The dilations `ψ (r ·) * f` converge to `ψ * f` in the Dirichlet seminorm. -/
private lemma tendsto_dilate_mul {f ψ h : ℂ → ℂ} {M : ℝ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hf' : ∫⁻ z in ball (0 : ℂ) 1, ‖deriv f z‖ₑ ^ 2 < ∞)
    (hψ : DifferentiableOn ℂ ψ (ball 0 1)) (hM : ∀ z ∈ ball (0 : ℂ) 1, ‖ψ z‖ ≤ M)
    (hh : ∀ z ∈ ball (0 : ℂ) 1, h z = ψ z * f z)
    (hh' : ∫⁻ z in ball (0 : ℂ) 1, ‖deriv h z‖ₑ ^ 2 < ∞) :
    Tendsto (fun r : ℝ => ∫⁻ z in ball (0 : ℂ) 1,
      ‖deriv (fun w => ψ (r * w) * f w) z - deriv h z‖ₑ ^ 2) (𝓝[<] 1) (𝓝 0) := by
  classical
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (mem_ball_self one_pos))
  have hfc : ContinuousOn f (ball 0 1) := hf.continuousOn
  have hψc : ContinuousOn ψ (ball 0 1) := hψ.continuousOn
  have hf'c : ContinuousOn (deriv f) (ball 0 1) := (hf.deriv isOpen_ball).continuousOn
  have hψ'c : ContinuousOn (deriv ψ) (ball 0 1) := (hψ.deriv isOpen_ball).continuousOn
  have hdh : ∀ z ∈ ball (0 : ℂ) 1, deriv h z = deriv ψ z * f z + ψ z * deriv f z := by
    intro z hz
    have heq : h =ᶠ[𝓝 z] fun w => ψ w * f w :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) hh
    rw [heq.deriv_eq]
    exact ((hψ.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.mul
      (hf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt).deriv
  have hdu : ∀ r : ℝ, 0 < r → r < 1 → ∀ z ∈ ball (0 : ℂ) 1,
      deriv (fun w => ψ (r * w) * f w) z =
        (r : ℂ) * deriv ψ (r * z) * f z + ψ (r * z) * deriv f z := by
    intro r hr0 hr1 z hz
    have hrz := mapsTo_mul_ball hr0.le hr1.le hz
    have h1 : HasDerivAt (fun w => ψ ((r : ℂ) * w)) (deriv ψ (r * z) * ((r : ℂ) * 1)) z := by
      have := (hψ.differentiableAt (isOpen_ball.mem_nhds hrz)).hasDerivAt.comp z
        ((hasDerivAt_id z).const_mul (r : ℂ))
      simpa [Function.comp_def] using this
    have h2 : HasDerivAt (fun w => ψ ((r : ℂ) * w) * f w)
        (deriv ψ (r * z) * ((r : ℂ) * 1) * f z + ψ (r * z) * deriv f z) z :=
      h1.mul (hf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    rw [h2.deriv]
    ring
  -- the auxiliary function `F = f ψ'` on the disc
  set F : ℂ → ℂ := (ball (0 : ℂ) 1).indicator (fun z => f z * deriv ψ z) with hFdef
  have hFm : Measurable F := by
    have := ContinuousOn.measurable_piecewise (hfc.mul hψ'c)
      (continuousOn_const (c := (0 : ℂ)) (s := (ball (0 : ℂ) 1)ᶜ)) measurableSet_ball
    convert this using 1
    ext z
    by_cases hz : z ∈ ball (0 : ℂ) 1 <;> simp [F, hz]
  have hFeq : ∀ z ∈ ball (0 : ℂ) 1, F z = f z * deriv ψ z := fun z hz => indicator_of_mem hz _
  have hFint : ∫⁻ z in ball (0 : ℂ) 1, ‖F z‖ₑ ^ 2 < ∞ := by
    have hpt : ∀ z ∈ ball (0 : ℂ) 1, ‖F z‖ₑ ^ 2 ≤
        2 * ‖deriv h z‖ₑ ^ 2 + 2 * (ENNReal.ofReal (M ^ 2) * ‖deriv f z‖ₑ ^ 2) := by
      intro z hz
      have heq : F z = deriv h z + (-(ψ z * deriv f z)) := by rw [hFeq z hz, hdh z hz]; ring
      rw [heq]
      refine (enorm_add_sq_le _ _).trans ?_
      gcongr
      rw [eNorm_neg, eNorm_mul, mul_pow, ← ofReal_norm (ψ z),
        ← ENNReal.ofReal_pow (norm_nonneg _)]
      gcongr
      exact hM z hz
    have hmh : Measurable fun z => ‖deriv h z‖ₑ ^ 2 := (measurable_deriv h).eNorm.pow_const 2
    calc ∫⁻ z in ball (0 : ℂ) 1, ‖F z‖ₑ ^ 2
        ≤ ∫⁻ z in ball (0 : ℂ) 1,
            (2 * ‖deriv h z‖ₑ ^ 2 + 2 * (ENNReal.ofReal (M ^ 2) * ‖deriv f z‖ₑ ^ 2)) :=
          setLIntegral_mono' measurableSet_ball hpt
      _ = 2 * (∫⁻ z in ball (0 : ℂ) 1, ‖deriv h z‖ₑ ^ 2) +
            2 * (ENNReal.ofReal (M ^ 2) * ∫⁻ z in ball (0 : ℂ) 1, ‖deriv f z‖ₑ ^ 2) := by
          rw [lintegral_add_left (hmh.const_mul 2), lintegral_const_mul _ hmh,
            lintegral_const_mul' _ _ (by norm_num),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ < ∞ := by
          have h2 : (2 : ℝ≥0∞) < ∞ := by simp
          exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top h2 hh',
            ENNReal.mul_lt_top h2 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf')⟩
  have hT3 := tendsto_lintegral_dilate hFm hFint
  have hA := tendsto_lintegral_dilate (measurable_deriv f) hf'
  -- first term: dominated convergence
  have hT1 : Tendsto (fun r : ℝ => ∫⁻ z in ball (0 : ℂ) 1,
      ‖(ψ (r * z) - ψ z) * deriv f z‖ₑ ^ 2) (𝓝[<] 1) (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence'
      (μ := volume.restrict (ball (0 : ℂ) 1)) (l := 𝓝[<] (1 : ℝ))
      (F := fun r : ℝ => fun z => ‖(ψ (r * z) - ψ z) * deriv f z‖ₑ ^ 2) (f := fun _ => 0)
      (fun z => ENNReal.ofReal ((2 * M) ^ 2) * ‖deriv f z‖ₑ ^ 2) ?_ ?_ ?_ ?_
    · simpa using h
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
      exact ((((continuousOn_comp_mul hψc hr.1.le hr.2.le).sub hψc).mul hf'c).aemeasurable
        measurableSet_ball).eNorm.pow_const 2
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
      refine (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun z hz => ?_)
      rw [eNorm_mul, mul_pow]
      gcongr
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
      calc ‖ψ (r * z) - ψ z‖ ≤ ‖ψ (r * z)‖ + ‖ψ z‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add (hM _ (mapsTo_mul_ball hr.1.le hr.2.le hz)) (hM z hz)
        _ = 2 * M := by ring
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf'.ne
    · refine (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun z hz => ?_)
      have hψz : ContinuousAt (fun r : ℝ => ψ ((r : ℂ) * z)) 1 :=
        (hψc.continuousAt (isOpen_ball.mem_nhds hz)).comp_of_eq
          (Complex.continuous_ofReal.mul continuous_const).continuousAt (by simp)
      have hc : ContinuousAt (fun r : ℝ => ‖(ψ (r * z) - ψ z) * deriv f z‖ₑ ^ 2) 1 :=
        (ENNReal.continuous_pow 2).continuousAt.comp
          (continuous_eNorm.continuousAt.comp ((hψz.sub continuousAt_const).mul
            continuousAt_const))
      have := hc.tendsto
      simp only [Complex.ofReal_one, one_mul, sub_self, zero_mul, eNorm_zero] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa using this)
  -- second term, smooth part
  have hT2b : ∀ s : ℝ, 0 < s → s < 1 → Tendsto (fun r : ℝ => ∫⁻ z in ball (0 : ℂ) 1,
      ‖(r : ℂ) * deriv ψ (r * z) * (f (s * z) - f (s * (r * z)))‖ₑ ^ 2) (𝓝[<] 1) (𝓝 0) := by
    intro s hs0 hs1
    obtain ⟨B, hB⟩ : ∃ B, ∀ w ∈ closedBall (0 : ℂ) s, ‖deriv f w‖ ≤ B :=
      (isCompact_closedBall (0 : ℂ) s).exists_bound_of_continuousOn
        (hf'c.mono (closedBall_subset_ball hs1))
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (mem_closedBall_self hs0.le))
    have hmvt : ∀ z ∈ ball (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r < 1 →
        ‖f (s * z) - f (s * (r * z))‖ ≤ B * (1 - r) := by
      intro z hz r hr0 hr1
      have hz1 := mem_ball_zero_iff.mp hz
      have hx : (s : ℂ) * ((r : ℂ) * z) ∈ closedBall (0 : ℂ) s := by
        rw [mem_closedBall_zero_iff, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hs0, abs_of_pos hr0]
        calc s * (r * ‖z‖) ≤ s * (1 * 1) := by gcongr
          _ = s := by ring
      have hy : (s : ℂ) * z ∈ closedBall (0 : ℂ) s := by
        rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hs0]
        calc s * ‖z‖ ≤ s * 1 := by gcongr
          _ = s := by ring
      have := (convex_closedBall (0 : ℂ) s).norm_image_sub_le_of_norm_deriv_le (f := f)
        (fun w hw => hf.differentiableAt (isOpen_ball.mem_nhds (closedBall_subset_ball hs1 hw)))
        hB hx hy
      have hdiff : (s : ℂ) * z - (s : ℂ) * ((r : ℂ) * z) = ((s * (1 - r) : ℝ) : ℂ) * z := by
        push_cast; ring
      calc ‖f (s * z) - f (s * (r * z))‖ ≤ B * ‖(s : ℂ) * z - (s : ℂ) * ((r : ℂ) * z)‖ := this
        _ = B * (s * (1 - r) * ‖z‖) := by
            rw [hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (by nlinarith)]
        _ ≤ B * (1 - r) := by
            gcongr
            calc s * (1 - r) * ‖z‖ ≤ 1 * (1 - r) * 1 := by
                  gcongr
              _ = 1 - r := by ring
    have h := tendsto_lintegral_filter_of_dominated_convergence'
      (μ := volume.restrict (ball (0 : ℂ) 1)) (l := 𝓝[<] (1 : ℝ))
      (F := fun r : ℝ => fun z =>
        ‖(r : ℂ) * deriv ψ (r * z) * (f (s * z) - f (s * (r * z)))‖ₑ ^ 2) (f := fun _ => 0)
      (fun _ => ENNReal.ofReal ((2 * M * B) ^ 2)) ?_ ?_ ?_ ?_
    · simpa using h
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
      have c1 : ContinuousOn (fun z => (r : ℂ) * deriv ψ (r * z)) (ball 0 1) :=
        continuousOn_const.mul (continuousOn_comp_mul hψ'c hr.1.le hr.2.le)
      have c2 : ContinuousOn (fun z => f (s * z) - f (s * (r * z))) (ball 0 1) :=
        (continuousOn_comp_mul hfc hs0.le hs1.le).sub
          ((continuousOn_comp_mul hfc hs0.le hs1.le).comp
            (continuous_const.mul continuous_id).continuousOn (mapsTo_mul_ball hr.1.le hr.2.le))
      exact ((c1.mul c2).aemeasurable measurableSet_ball).eNorm.pow_const 2
    · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
      refine (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun z hz => ?_)
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
      have hz1 := mem_ball_zero_iff.mp hz
      have hpos : 0 < 1 - r * ‖z‖ := by nlinarith [norm_nonneg z, hr.1, hr.2]
      rw [norm_mul]
      calc ‖(r : ℂ) * deriv ψ (r * z)‖ * ‖f (s * z) - f (s * (r * z))‖
          ≤ (2 * M / (1 - r * ‖z‖)) * (B * (1 - r)) :=
            mul_le_mul (norm_mul_deriv_le hψ hM hz hr.1 hr.2) (hmvt z hz r hr.1 hr.2)
              (norm_nonneg _) (by positivity)
        _ ≤ 2 * M * B := by
            rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
            have : 1 - r ≤ 1 - r * ‖z‖ := by nlinarith [norm_nonneg z, hr.1, hr.2]
            have hMB : 0 ≤ 2 * M * B := by positivity
            nlinarith
    · rw [setLIntegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
    · refine (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun z hz => ?_)
      have hsz : (s : ℂ) * z ∈ ball (0 : ℂ) 1 := mapsTo_mul_ball hs0.le hs1.le hz
      have hψ'z : ContinuousAt (fun r : ℝ => deriv ψ ((r : ℂ) * z)) 1 :=
        (hψ'c.continuousAt (isOpen_ball.mem_nhds hz)).comp_of_eq
          (Complex.continuous_ofReal.mul continuous_const).continuousAt (by simp)
      have hfz : ContinuousAt (fun r : ℝ => f ((s : ℂ) * ((r : ℂ) * z))) 1 :=
        (hfc.continuousAt (isOpen_ball.mem_nhds hsz)).comp_of_eq
          (continuous_const.mul (Complex.continuous_ofReal.mul continuous_const)).continuousAt
          (by simp)
      have hc : ContinuousAt (fun r : ℝ =>
          ‖(r : ℂ) * deriv ψ (r * z) * (f (s * z) - f (s * (r * z)))‖ₑ ^ 2) 1 :=
        (ENNReal.continuous_pow 2).continuousAt.comp
          (continuous_eNorm.continuousAt.comp
            ((Complex.continuous_ofReal.continuousAt.mul hψ'z).mul
              (continuousAt_const.sub hfz)))
      have := hc.tendsto
      simp only [Complex.ofReal_one, one_mul, sub_self, mul_zero, eNorm_zero] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa using this)
  -- second term, rough part: the crude bound
  have hT2a : ∀ s : ℝ, 0 < s → s < 1 → ∀ r : ℝ, 1 / 2 ≤ r → r < 1 →
      ∫⁻ z in ball (0 : ℂ) 1, ‖(r : ℂ) * deriv ψ (r * z) *
          ((f z - f (s * z)) - (f (r * z) - f (s * (r * z))))‖ₑ ^ 2 ≤
        ENNReal.ofReal (16 * M ^ 2) *
          ∫⁻ z in ball (0 : ℂ) 1, ‖(s : ℂ) * deriv f (s * z) - deriv f z‖ₑ ^ 2 := by
    intro s hs0 hs1 r hr hr1
    have hr0 : 0 < r := by linarith
    set k : ℂ → ℂ := fun z => f z - f (s * z) with hkdef
    have hfs : DifferentiableOn ℂ (fun z => f ((s : ℂ) * z)) (ball 0 1) := fun z hz =>
      ((hf.differentiableAt (isOpen_ball.mem_nhds (mapsTo_mul_ball hs0.le hs1.le hz))).comp z
        ((differentiableAt_id).const_mul (s : ℂ))).differentiableWithinAt
    have hk : DifferentiableOn ℂ k (ball 0 1) := hf.sub hfs
    have hdk : ∀ z ∈ ball (0 : ℂ) 1, deriv k z = deriv f z - s * deriv f (s * z) := by
      intro z hz
      have hsz := mapsTo_mul_ball hs0.le hs1.le hz
      have h1 : HasDerivAt (fun w => f ((s : ℂ) * w)) (deriv f (s * z) * ((s : ℂ) * 1)) z := by
        have := (hf.differentiableAt (isOpen_ball.mem_nhds hsz)).hasDerivAt.comp z
          ((hasDerivAt_id z).const_mul (s : ℂ))
        simpa [Function.comp_def] using this
      have h2 : HasDerivAt k (deriv f z - deriv f (s * z) * ((s : ℂ) * 1)) z :=
        (hf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.sub h1
      rw [h2.deriv]
      ring
    have hcrude := lintegral_sub_dilate_le hk hr0 hr1
    have hpt : ∀ z ∈ ball (0 : ℂ) 1, ‖(r : ℂ) * deriv ψ (r * z) *
          ((f z - f (s * z)) - (f (r * z) - f (s * (r * z))))‖ₑ ^ 2 ≤
        ENNReal.ofReal ((2 * M / (1 - r)) ^ 2) * ‖k z - k (r * z)‖ₑ ^ 2 := by
      intro z hz
      have hz1 := mem_ball_zero_iff.mp hz
      rw [eNorm_mul, mul_pow]
      gcongr
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
      refine (norm_mul_deriv_le hψ hM hz hr0 hr1).trans ?_
      have h1 : 0 < 1 - r := by linarith
      have h2 : 1 - r ≤ 1 - r * ‖z‖ := by nlinarith [norm_nonneg z]
      exact div_le_div_of_nonneg_left (by positivity) h1 h2
    have hint : ∫⁻ z in ball (0 : ℂ) 1, ‖deriv k z‖ₑ ^ 2 =
        ∫⁻ z in ball (0 : ℂ) 1, ‖(s : ℂ) * deriv f (s * z) - deriv f z‖ₑ ^ 2 := by
      refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
      rw [hdk z hz, ← eNorm_neg, neg_sub]
    calc ∫⁻ z in ball (0 : ℂ) 1, ‖(r : ℂ) * deriv ψ (r * z) *
          ((f z - f (s * z)) - (f (r * z) - f (s * (r * z))))‖ₑ ^ 2
        ≤ ∫⁻ z in ball (0 : ℂ) 1,
            ENNReal.ofReal ((2 * M / (1 - r)) ^ 2) * ‖k z - k (r * z)‖ₑ ^ 2 :=
          setLIntegral_mono' measurableSet_ball hpt
      _ = ENNReal.ofReal ((2 * M / (1 - r)) ^ 2) *
            ∫⁻ z in ball (0 : ℂ) 1, ‖k z - k (r * z)‖ₑ ^ 2 :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((2 * M / (1 - r)) ^ 2) * (ENNReal.ofReal (((1 - r) / r) ^ 2) *
            ∫⁻ z in ball (0 : ℂ) 1, ‖deriv k z‖ₑ ^ 2) := by gcongr
      _ = ENNReal.ofReal ((2 * M / r) ^ 2) * ∫⁻ z in ball (0 : ℂ) 1, ‖deriv k z‖ₑ ^ 2 := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          have h1 : 1 - r ≠ 0 := (by linarith : (0 : ℝ) < 1 - r).ne'
          field_simp
      _ ≤ ENNReal.ofReal (16 * M ^ 2) *
            ∫⁻ z in ball (0 : ℂ) 1, ‖(s : ℂ) * deriv f (s * z) - deriv f z‖ₑ ^ 2 := by
          rw [hint]
          gcongr
          rw [div_pow, div_le_iff₀ (by positivity)]
          calc (2 * M) ^ 2 = 16 * M ^ 2 * (1 / 2) ^ 2 := by ring
            _ ≤ 16 * M ^ 2 * r ^ 2 := by gcongr
  -- assemble
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨η, hη0, -, hηε⟩ := exists_small ε hε 16 (by norm_num) (by norm_num)
  obtain ⟨η', hη'0, -, hη'η⟩ := exists_small η hη0 (ENNReal.ofReal (16 * M ^ 2) + 1)
    (lt_of_lt_of_le one_pos le_add_self).ne'
    (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩)
  obtain ⟨s, hsA, hs⟩ := ((ENNReal.tendsto_nhds_zero.1 hA η' hη'0).and
    (Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num))).exists
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hT1 η hη0,
    ENNReal.tendsto_nhds_zero.1 (hT2b s hs.1 hs.2) η hη0,
    ENNReal.tendsto_nhds_zero.1 hT3 η hη0,
    Ioo_mem_nhdsLT (show (1 / 2 : ℝ) < 1 by norm_num)] with r h1 h2b h3 hr
  have hr0 : 0 < r := by linarith [hr.1]
  have h2a := hT2a s hs.1 hs.2 r hr.1.le hr.2
  have hpt : ∀ z ∈ ball (0 : ℂ) 1,
      ‖deriv (fun w => ψ (r * w) * f w) z - deriv h z‖ₑ ^ 2 ≤
        4 * ‖(ψ (r * z) - ψ z) * deriv f z‖ₑ ^ 2 +
        4 * ‖(r : ℂ) * deriv ψ (r * z) *
          ((f z - f (s * z)) - (f (r * z) - f (s * (r * z))))‖ₑ ^ 2 +
        4 * ‖(r : ℂ) * deriv ψ (r * z) * (f (s * z) - f (s * (r * z)))‖ₑ ^ 2 +
        4 * ‖(r : ℂ) * F (r * z) - F z‖ₑ ^ 2 := by
    intro z hz
    have hrz := mapsTo_mul_ball hr0.le hr.2.le hz
    have heq : deriv (fun w => ψ (r * w) * f w) z - deriv h z =
        ((ψ (r * z) - ψ z) * deriv f z + (r : ℂ) * deriv ψ (r * z) *
          ((f z - f (s * z)) - (f (r * z) - f (s * (r * z))))) +
        ((r : ℂ) * deriv ψ (r * z) * (f (s * z) - f (s * (r * z))) +
          ((r : ℂ) * F (r * z) - F z)) := by
      rw [hdu r hr0 hr.2 z hz, hdh z hz, hFeq _ hrz, hFeq z hz]
      ring
    rw [heq]
    refine (enorm_add_sq_le _ _).trans ?_
    calc 2 * ‖(ψ (r * z) - ψ z) * deriv f z + (r : ℂ) * deriv ψ (r * z) *
            ((f z - f (s * z)) - (f (r * z) - f (s * (r * z))))‖ₑ ^ 2 +
          2 * ‖(r : ℂ) * deriv ψ (r * z) * (f (s * z) - f (s * (r * z))) +
            ((r : ℂ) * F (r * z) - F z)‖ₑ ^ 2
        ≤ 2 * (2 * ‖(ψ (r * z) - ψ z) * deriv f z‖ₑ ^ 2 + 2 * ‖(r : ℂ) * deriv ψ (r * z) *
            ((f z - f (s * z)) - (f (r * z) - f (s * (r * z))))‖ₑ ^ 2) +
          2 * (2 * ‖(r : ℂ) * deriv ψ (r * z) * (f (s * z) - f (s * (r * z)))‖ₑ ^ 2 +
            2 * ‖(r : ℂ) * F (r * z) - F z‖ₑ ^ 2) := by
          gcongr <;> exact enorm_add_sq_le _ _
      _ = _ := by ring
  -- measurability of the pieces
  have hc2a : ContinuousOn (fun z => (r : ℂ) * deriv ψ (r * z) *
      ((f z - f (s * z)) - (f (r * z) - f (s * (r * z))))) (ball 0 1) := by
    have hfs := continuousOn_comp_mul hfc hs.1.le hs.2.le
    exact (continuousOn_const.mul (continuousOn_comp_mul hψ'c hr0.le hr.2.le)).mul
      ((hfc.sub hfs).sub ((continuousOn_comp_mul hfc hr0.le hr.2.le).sub
        (hfs.comp (continuous_const.mul continuous_id).continuousOn
          (mapsTo_mul_ball hr0.le hr.2.le))))
  have hc2b : ContinuousOn (fun z => (r : ℂ) * deriv ψ (r * z) *
      (f (s * z) - f (s * (r * z)))) (ball 0 1) := by
    have hfs := continuousOn_comp_mul hfc hs.1.le hs.2.le
    exact (continuousOn_const.mul (continuousOn_comp_mul hψ'c hr0.le hr.2.le)).mul
      (hfs.sub (hfs.comp (continuous_const.mul continuous_id).continuousOn
          (mapsTo_mul_ball hr0.le hr.2.le)))
  have hm2a := ((hc2a.aemeasurable (μ := volume) measurableSet_ball).eNorm.pow_const 2).const_mul 4
  have hm2b := ((hc2b.aemeasurable (μ := volume) measurableSet_ball).eNorm.pow_const 2).const_mul 4
  have hm3 : AEMeasurable (fun z => 4 * ‖(r : ℂ) * F (r * z) - F z‖ₑ ^ 2)
      (volume.restrict (ball (0 : ℂ) 1)) :=
    ((((measurable_const.mul (hFm.comp (measurable_const.mul measurable_id))).sub
      hFm).eNorm.pow_const 2).const_mul 4).aemeasurable
  calc ∫⁻ z in ball (0 : ℂ) 1, ‖deriv (fun w => ψ (r * w) * f w) z - deriv h z‖ₑ ^ 2
      ≤ ∫⁻ z in ball (0 : ℂ) 1, (4 * ‖(ψ (r * z) - ψ z) * deriv f z‖ₑ ^ 2 +
        4 * ‖(r : ℂ) * deriv ψ (r * z) *
          ((f z - f (s * z)) - (f (r * z) - f (s * (r * z))))‖ₑ ^ 2 +
        4 * ‖(r : ℂ) * deriv ψ (r * z) * (f (s * z) - f (s * (r * z)))‖ₑ ^ 2 +
        4 * ‖(r : ℂ) * F (r * z) - F z‖ₑ ^ 2) :=
        setLIntegral_mono' measurableSet_ball hpt
    _ = 4 * (∫⁻ z in ball (0 : ℂ) 1, ‖(ψ (r * z) - ψ z) * deriv f z‖ₑ ^ 2) +
        4 * (∫⁻ z in ball (0 : ℂ) 1, ‖(r : ℂ) * deriv ψ (r * z) *
          ((f z - f (s * z)) - (f (r * z) - f (s * (r * z))))‖ₑ ^ 2) +
        4 * (∫⁻ z in ball (0 : ℂ) 1,
          ‖(r : ℂ) * deriv ψ (r * z) * (f (s * z) - f (s * (r * z)))‖ₑ ^ 2) +
        4 * (∫⁻ z in ball (0 : ℂ) 1, ‖(r : ℂ) * F (r * z) - F z‖ₑ ^ 2) := by
        rw [lintegral_add_right' _ hm3, lintegral_add_right' _ hm2b,
          lintegral_add_right' _ hm2a, lintegral_const_mul' _ _ (by norm_num),
          lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num),
          lintegral_const_mul' _ _ (by norm_num)]
    _ ≤ 4 * η + 4 * η + 4 * η + 4 * η := by
        gcongr
        calc _ ≤ _ := h2a
          _ ≤ ENNReal.ofReal (16 * M ^ 2) * η' := by gcongr
          _ ≤ (ENNReal.ofReal (16 * M ^ 2) + 1) * η' := by gcongr; exact le_self_add
          _ ≤ η := hη'η
    _ = 16 * η := by ring
    _ ≤ ε := hηε

/-- The extended norm of `‖x‖ ^ 2` is `‖x‖ₑ ^ 2`. -/
private lemma enorm_norm_sq (x : ℂ) : ‖(‖x‖ ^ 2 : ℝ)‖ₑ = ‖x‖ₑ ^ 2 := by
  rw [Real.eNorm_of_nonneg (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- Integrability of `‖G‖²` on the disc gives a finite lower integral of `‖G‖ₑ²`. -/
private lemma lintegral_lt_top_of_integrableOn {G : ℂ → ℂ}
    (h : IntegrableOn (fun z => ‖G z‖ ^ 2) (ball (0 : ℂ) 1)) :
    ∫⁻ z in ball (0 : ℂ) 1, ‖G z‖ₑ ^ 2 < ∞ := by
  have := h.2
  rw [hasFiniteIntegral_iff_eNorm] at this
  simpa [enorm_norm_sq] using this

/-- A measurable `G` with finite lower integral of `‖G‖ₑ²` has `‖G‖²` integrable on the disc.
-/
private lemma integrableOn_of_lintegral_lt_top {G : ℂ → ℂ} (hG : Measurable G)
    (h : ∫⁻ z in ball (0 : ℂ) 1, ‖G z‖ₑ ^ 2 < ∞) :
    IntegrableOn (fun z => ‖G z‖ ^ 2) (ball (0 : ℂ) 1) := by
  refine ⟨(hG.norm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_eNorm]
  simpa [enorm_norm_sq] using h

/-- `‖x - w‖² ≤ 2 ‖x - y‖² + 2 ‖y - w‖²` for extended norms. -/
private lemma enorm_sub_sq_le (x y w : ℂ) : ‖x - w‖ₑ ^ 2 ≤ 2 * ‖x - y‖ₑ ^ 2 + 2 * ‖y - w‖ₑ ^ 2 := by
  have := enorm_add_sq_le (x - y) (y - w)
  rwa [sub_add_sub_cancel] at this

/-- The triangle inequality, with constant `2`, for the squared `L²` distance of derivatives. -/
private lemma lintegral_sub_sq_le (a b c : ℂ → ℂ) :
    ∫⁻ z in ball (0 : ℂ) 1, ‖deriv a z - deriv c z‖ₑ ^ 2 ≤
      2 * (∫⁻ z in ball (0 : ℂ) 1, ‖deriv a z - deriv b z‖ₑ ^ 2) +
        2 * ∫⁻ z in ball (0 : ℂ) 1, ‖deriv b z - deriv c z‖ₑ ^ 2 := by
  have hm : Measurable fun z => ‖deriv a z - deriv b z‖ₑ ^ 2 :=
    ((measurable_deriv a).sub (measurable_deriv b)).eNorm.pow_const 2
  calc ∫⁻ z in ball (0 : ℂ) 1, ‖deriv a z - deriv c z‖ₑ ^ 2
      ≤ ∫⁻ z in ball (0 : ℂ) 1,
          (2 * ‖deriv a z - deriv b z‖ₑ ^ 2 + 2 * ‖deriv b z - deriv c z‖ₑ ^ 2) :=
        lintegral_mono fun z => enorm_sub_sq_le _ _ _
    _ = _ := by
        rw [lintegral_add_left (hm.const_mul 2), lintegral_const_mul' _ _ (by norm_num),
          lintegral_const_mul' _ _ (by norm_num)]

/-- The triangle inequality for the squared Dirichlet distance, with constant `2`. -/
private lemma dist_sq_le (a b c : ℂ → ℂ) :
    ‖a 0 - c 0‖ₑ ^ 2 + ∫⁻ z in ball (0 : ℂ) 1, ‖deriv a z - deriv c z‖ₑ ^ 2 ≤
      2 * (‖a 0 - b 0‖ₑ ^ 2 + ∫⁻ z in ball (0 : ℂ) 1, ‖deriv a z - deriv b z‖ₑ ^ 2) +
      2 * (‖b 0 - c 0‖ₑ ^ 2 + ∫⁻ z in ball (0 : ℂ) 1, ‖deriv b z - deriv c z‖ₑ ^ 2) := by
  calc _ ≤ (2 * ‖a 0 - b 0‖ₑ ^ 2 + 2 * ‖b 0 - c 0‖ₑ ^ 2) +
        (2 * (∫⁻ z in ball (0 : ℂ) 1, ‖deriv a z - deriv b z‖ₑ ^ 2) +
          2 * ∫⁻ z in ball (0 : ℂ) 1, ‖deriv b z - deriv c z‖ₑ ^ 2) :=
        add_le_add (enorm_sub_sq_le _ _ _) (lintegral_sub_sq_le a b c)
    _ = _ := by ring

/-- The squared Dirichlet distance as a real number and as an extended real. -/
private lemma ofReal_dist_sq_eq {a b : ℂ → ℂ}
    (ha : IntegrableOn (fun z => ‖deriv a z‖ ^ 2) (ball (0 : ℂ) 1))
    (hb : IntegrableOn (fun z => ‖deriv b z‖ ^ 2) (ball (0 : ℂ) 1)) :
    ENNReal.ofReal (‖a 0 - b 0‖ ^ 2 + ∫ z in ball (0 : ℂ) 1, ‖deriv a z - deriv b z‖ ^ 2) =
      ‖a 0 - b 0‖ₑ ^ 2 + ∫⁻ z in ball (0 : ℂ) 1, ‖deriv a z - deriv b z‖ₑ ^ 2 := by
  have hint : IntegrableOn (fun z => ‖deriv a z - deriv b z‖ ^ 2) (ball (0 : ℂ) 1) := by
    refine integrableOn_of_lintegral_lt_top ((measurable_deriv a).sub (measurable_deriv b)) ?_
    have h1 := lintegral_lt_top_of_integrableOn ha
    have h2 := lintegral_lt_top_of_integrableOn hb
    have hm : Measurable fun z => ‖deriv a z‖ₑ ^ 2 := (measurable_deriv a).eNorm.pow_const 2
    calc ∫⁻ z in ball (0 : ℂ) 1, ‖deriv a z - deriv b z‖ₑ ^ 2
        ≤ ∫⁻ z in ball (0 : ℂ) 1, (2 * ‖deriv a z‖ₑ ^ 2 + 2 * ‖deriv b z‖ₑ ^ 2) := by
          refine lintegral_mono fun z => ?_
          have := enorm_sub_sq_le (deriv a z) 0 (deriv b z)
          simpa using this
      _ = 2 * (∫⁻ z in ball (0 : ℂ) 1, ‖deriv a z‖ₑ ^ 2) +
            2 * ∫⁻ z in ball (0 : ℂ) 1, ‖deriv b z‖ₑ ^ 2 := by
          rw [lintegral_add_left (hm.const_mul 2), lintegral_const_mul' _ _ (by norm_num),
            lintegral_const_mul' _ _ (by norm_num)]
      _ < ∞ := by
          have h2' : (2 : ℝ≥0∞) < ∞ := by simp
          exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top h2' h1, ENNReal.mul_lt_top h2' h2⟩
  rw [ENNReal.ofReal_add (by positivity)
      (setIntegral_nonneg measurableSet_ball fun _ _ => by positivity),
    ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => by positivity),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  congr 1
  refine lintegral_congr fun z => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- Approximation of `ψ * f` by polynomial multiples of `f` in the Dirichlet seminorm. -/
private lemma exists_poly_mul_approx {f ψ h : ℂ → ℂ} {M : ℝ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hf' : ∫⁻ z in ball (0 : ℂ) 1, ‖deriv f z‖ₑ ^ 2 < ∞)
    (hψ : DifferentiableOn ℂ ψ (ball 0 1)) (hM : ∀ z ∈ ball (0 : ℂ) 1, ‖ψ z‖ ≤ M)
    (hh : ∀ z ∈ ball (0 : ℂ) 1, h z = ψ z * f z)
    (hh' : ∫⁻ z in ball (0 : ℂ) 1, ‖deriv h z‖ₑ ^ 2 < ∞) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ‖p.eval 0 * f 0 - h 0‖ₑ ^ 2 +
      ∫⁻ z in ball (0 : ℂ) 1, ‖deriv (fun w => p.eval w * f w) z - deriv h z‖ₑ ^ 2 < ε := by
  obtain ⟨η, hη0, hηtop, hηε⟩ := exists_small ε hε 4 (by norm_num) (by norm_num)
  have hf2 := lintegral_norm_sq_lt_top hf hf'
  set I : ℝ≥0∞ := (∫⁻ z in ball (0 : ℂ) 1, ‖f z‖ₑ ^ 2) +
    ∫⁻ z in ball (0 : ℂ) 1, ‖deriv f z‖ₑ ^ 2 with hI
  set K : ℝ≥0∞ := ‖f 0‖ₑ ^ 2 + 4 * I with hK
  have hKtop : K ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.pow_ne_top eNorm_ne_top,
      ENNReal.mul_ne_top (by norm_num) (ENNReal.add_ne_top.2 ⟨hf2.ne, hf'.ne⟩)⟩
  obtain ⟨η'', hη''0, hη''top, hη''η⟩ := exists_small η hη0 (K + 1)
    (lt_of_lt_of_le one_pos le_add_self).ne' (ENNReal.add_ne_top.2 ⟨hKtop, ENNReal.one_ne_top⟩)
  obtain ⟨r, hrJ, hr⟩ := ((ENNReal.tendsto_nhds_zero.1
    (tendsto_dilate_mul hf hf' hψ hM hh hh') η hη0).and
    (Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num))).exists
  set δ : ℝ := Real.sqrt η''.toReal with hδ
  have hδ0 : 0 < δ := Real.sqrt_pos.2 (ENNReal.toReal_pos hη''0.ne' hη''top)
  have hδ2 : ENNReal.ofReal (δ ^ 2) = η'' := by
    rw [hδ, Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hη''top]
  obtain ⟨p, hp⟩ := exists_poly_approx hψ hr.1 hr.2 hδ0
  refine ⟨p, ?_⟩
  have hsq : ∀ x : ℂ, ‖x‖ ≤ δ → ‖x‖ₑ ^ 2 ≤ η'' := fun x hx => by
    rw [← hδ2, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hx 2)
  have hdp : ∀ z ∈ ball (0 : ℂ) 1, deriv (fun w => p.eval w * f w) z -
      deriv (fun w => ψ (r * w) * f w) z =
      deriv (fun w => p.eval w - ψ (r * w)) z * f z + (p.eval z - ψ (r * z)) * deriv f z := by
    intro z hz
    have hrz := mapsTo_mul_ball hr.1.le hr.2.le hz
    have hψr : HasDerivAt (fun w => ψ ((r : ℂ) * w)) (deriv ψ (r * z) * ((r : ℂ) * 1)) z := by
      have := (hψ.differentiableAt (isOpen_ball.mem_nhds hrz)).hasDerivAt.comp z
        ((hasDerivAt_id z).const_mul (r : ℂ))
      simpa [Function.comp_def] using this
    have hpd := ((Polynomial.differentiable p) z).hasDerivAt
    have hfd := (hf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have e1 : deriv (fun w => p.eval w * f w) z =
        deriv (fun w => p.eval w) z * f z + p.eval z * deriv f z := (hpd.mul hfd).deriv
    have e2 : deriv (fun w => ψ (r * w) * f w) z =
        deriv ψ (r * z) * ((r : ℂ) * 1) * f z + ψ (r * z) * deriv f z := (hψr.mul hfd).deriv
    have e3 : deriv (fun w => p.eval w - ψ (r * w)) z =
        deriv (fun w => p.eval w) z - deriv ψ (r * z) * ((r : ℂ) * 1) := (hpd.sub hψr).deriv
    rw [e1, e2, e3]
    ring
  have hpt : ∀ z ∈ ball (0 : ℂ) 1, ‖deriv (fun w => p.eval w * f w) z -
      deriv (fun w => ψ (r * w) * f w) z‖ₑ ^ 2 ≤
        2 * (η'' * ‖f z‖ₑ ^ 2) + 2 * (η'' * ‖deriv f z‖ₑ ^ 2) := by
    intro z hz
    rw [hdp z hz]
    refine (enorm_add_sq_le _ _).trans ?_
    obtain ⟨h1, h2⟩ := hp z hz
    rw [eNorm_mul, eNorm_mul, mul_pow, mul_pow]
    gcongr
    · exact hsq _ h2
    · exact hsq _ h1
  have h0 : ‖p.eval 0 * f 0 - h 0‖ₑ ^ 2 ≤ η'' * ‖f 0‖ₑ ^ 2 := by
    have : p.eval 0 * f 0 - h 0 = (p.eval 0 - ψ (r * 0)) * f 0 := by
      rw [hh 0 (mem_ball_self one_pos), mul_zero]; ring
    rw [this, eNorm_mul, mul_pow]
    gcongr
    exact hsq _ (hp 0 (mem_ball_self one_pos)).1
  have hmf : AEMeasurable (fun z => 2 * (η'' * ‖f z‖ₑ ^ 2)) (volume.restrict (ball (0 : ℂ) 1)) :=
    (((hf.continuousOn.aemeasurable measurableSet_ball).eNorm.pow_const 2).const_mul _).const_mul _
  have hI1 : ∫⁻ z in ball (0 : ℂ) 1, ‖deriv (fun w => p.eval w * f w) z -
      deriv (fun w => ψ (r * w) * f w) z‖ₑ ^ 2 ≤ 2 * η'' * I := by
    calc _ ≤ ∫⁻ z in ball (0 : ℂ) 1,
          (2 * (η'' * ‖f z‖ₑ ^ 2) + 2 * (η'' * ‖deriv f z‖ₑ ^ 2)) :=
          setLIntegral_mono' measurableSet_ball hpt
      _ = _ := by
          rw [lintegral_add_left' hmf, lintegral_const_mul' (2 : ℝ≥0∞) _ (by norm_num),
            lintegral_const_mul' (2 : ℝ≥0∞) _ (by norm_num), lintegral_const_mul' η'' _ hη''top,
            lintegral_const_mul' η'' _ hη''top, hI]
          ring
  have hsplit := lintegral_sub_sq_le (fun w => p.eval w * f w) (fun w => ψ (r * w) * f w) h
  calc ‖p.eval 0 * f 0 - h 0‖ₑ ^ 2 +
        ∫⁻ z in ball (0 : ℂ) 1, ‖deriv (fun w => p.eval w * f w) z - deriv h z‖ₑ ^ 2
      ≤ η'' * ‖f 0‖ₑ ^ 2 + (2 * (2 * η'' * I) + 2 * η) := by
        refine add_le_add h0 (hsplit.trans ?_)
        gcongr
    _ = η'' * K + 2 * η := by rw [hK]; ring
    _ ≤ η + 2 * η := by
        gcongr
        calc η'' * K ≤ (K + 1) * η'' := by rw [mul_comm]; gcongr; exact le_self_add
          _ ≤ η := hη''η
    _ < η + 2 * η + η := ENNReal.lt_add_right
        (ENNReal.add_ne_top.2 ⟨hηtop, ENNReal.mul_ne_top (by norm_num) hηtop⟩) hη0.ne'
    _ = 4 * η := by ring
    _ ≤ ε := hηε

/--
**Polynomial density passes to dominating functions in the Dirichlet space.** For all $f$ and $g$
in the Dirichlet space $\mathcal{D}$: if the polynomial multiples $Pg$ are dense in $\mathcal{D}$
in the Dirichlet norm and $|g(z)| \le |f(z)|$ for all $|z| < 1$, then the polynomial multiples
$Pf$ are dense in $\mathcal{D}$ in the Dirichlet norm. This answers Hayman's Problem 8.11
positively.

Resolved true: Richter and Sundberg (Michigan Math. J. 38 (1991) 355-379), and independently
Aleman, proved that in Dirichlet-type spaces $\mathcal{D}(\mu)$, including the classical Dirichlet
space, $|g| \le |f|$ with $g$ cyclic implies $f$ cyclic, where $g$ is cyclic when $Pg$ is dense
(restated in arXiv:2406.06182, Thm 5.12).

Source: Emmanuel
Fricain and Romain Lebreton, Cyclicity of the shift operator through Bezout identities,
arXiv:2406.06182 (2024), https://arxiv.org/abs/2406.06182. Moved from
`OpenConjectures/Analysis/DirichletSpacePolynomialDensity`.
-/
theorem conjecture_holds : conjecture := by
  intro g f hg hgf u ε hε
  have hfD : DifferentiableOn ℂ f.val (ball 0 1) := f.property.1.differentiableOn
  have hgD : DifferentiableOn ℂ g.val (ball 0 1) := g.property.1.differentiableOn
  have hf' := lintegral_lt_top_of_integrableOn f.property.2
  obtain ⟨h, ⟨q, hq⟩, hhu⟩ := hg u (ε / 4) (by positivity)
  obtain ⟨φ, hφd, hφb, hφ⟩ :=
    exists_bounded_quotient hfD hgD (fun z hz => hgf z (mem_ball_zero_iff.mp hz))
  obtain ⟨Mq, hMq⟩ : ∃ Mq, ∀ z ∈ closedBall (0 : ℂ) 1, ‖q.eval z‖ ≤ Mq :=
    (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
      (Polynomial.differentiable q).continuous.continuousOn
  have hψd : DifferentiableOn ℂ (fun z => q.eval z * φ z) (ball 0 1) :=
    (Polynomial.differentiable q).differentiableOn.mul hφd
  have hψM : ∀ z ∈ ball (0 : ℂ) 1, ‖q.eval z * φ z‖ ≤ Mq := by
    intro z hz
    have h1 := hMq z (ball_subset_closedBall hz)
    rw [norm_mul]
    calc ‖q.eval z‖ * ‖φ z‖ ≤ Mq * 1 :=
          mul_le_mul h1 (hφb z hz) (norm_nonneg _) ((norm_nonneg _).trans h1)
      _ = Mq := mul_one _
  have hhψ : ∀ z ∈ ball (0 : ℂ) 1, h.val z = (q.eval z * φ z) * f.val z := by
    intro z hz
    rw [hq z (mem_ball_zero_iff.mp hz), hφ z hz]
    ring
  have hh' := lintegral_lt_top_of_integrableOn h.property.2
  have hε4 : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 4) := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨p, hp⟩ := exists_poly_mul_approx hfD hf' hψd hψM hhψ hh' hε4
  -- the approximant `p f` lies in the Dirichlet space
  have hPd : DifferentiableOn ℂ (fun z => p.eval z * f.val z) (ball 0 1) :=
    (Polynomial.differentiable p).differentiableOn.mul hfD
  have hPint : ∫⁻ z in ball (0 : ℂ) 1, ‖deriv (fun w => p.eval w * f.val w) z‖ₑ ^ 2 < ∞ := by
    have h1 : ∫⁻ z in ball (0 : ℂ) 1,
        ‖deriv (fun w => p.eval w * f.val w) z - deriv h.val z‖ₑ ^ 2 < ∞ :=
      le_add_self.trans_lt (hp.trans ENNReal.ofReal_lt_top)
    have h2 := lintegral_sub_sq_le (fun w => p.eval w * f.val w) h.val (fun _ => 0)
    simp only [deriv_const', sub_zero] at h2
    have htwo : (2 : ℝ≥0∞) < ∞ := by simp
    exact h2.trans_lt (ENNReal.add_lt_top.2
      ⟨ENNReal.mul_lt_top htwo h1, ENNReal.mul_lt_top htwo hh'⟩)
  have hPI : IntegrableOn (fun z => ‖deriv (fun w => p.eval w * f.val w) z‖ ^ 2)
      (ball (0 : ℂ) 1) :=
    integrableOn_of_lintegral_lt_top (measurable_deriv _) hPint
  refine ⟨⟨fun z => p.eval z * f.val z, (hPd.analyticOnNhd isOpen_ball).analyticOn, hPI⟩,
    ⟨p, fun z _ => rfl⟩, ?_⟩
  change ‖p.eval 0 * f.val 0 - u.val 0‖ ^ 2 + ∫ z in ball (0 : ℂ) 1,
    ‖deriv (fun w => p.eval w * f.val w) z - deriv u.val z‖ ^ 2 < ε
  have hhu' : ‖h.val 0 - u.val 0‖ₑ ^ 2 +
      ∫⁻ z in ball (0 : ℂ) 1, ‖deriv h.val z - deriv u.val z‖ₑ ^ 2 <
        ENNReal.ofReal (ε / 4) := by
    rw [← ofReal_dist_sq_eq h.property.2 u.property.2]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hhu
  rw [← ENNReal.ofReal_lt_ofReal_iff hε, ofReal_dist_sq_eq hPI u.property.2]
  calc _ ≤ _ := dist_sq_le (fun w => p.eval w * f.val w) h.val u.val
    _ < 2 * ENNReal.ofReal (ε / 4) + 2 * ENNReal.ofReal (ε / 4) := by
        have h20 : (2 : ℝ≥0∞) ≠ 0 := two_ne_zero
        have h2t : (2 : ℝ≥0∞) ≠ ⊤ := by simp
        exact ENNReal.add_lt_add (ENNReal.mul_lt_mul_right h20 h2t hp)
          (ENNReal.mul_lt_mul_right h20 h2t hhu')
    _ = ENNReal.ofReal 4 * ENNReal.ofReal (ε / 4) := by rw [ENNReal.ofReal_ofNat]; ring
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

end MathlibExt.Analysis.DirichletSpacePolynomialDensityWanted
