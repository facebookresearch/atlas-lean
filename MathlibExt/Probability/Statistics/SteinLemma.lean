/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Probability.Moments.Variance
-- `Measure.pi` is `@[no_expose]` at this Mathlib pin, and `pi_gaussian_le_volume` must unfold it
-- to its outer measure.
import all Mathlib.MeasureTheory.Constructions.Pi

/-!
# Stein's lemma, Stein's unbiased risk estimate and the James–Stein estimator

For `X ~ N(μ, v)` and a function `g` that is differentiable everywhere with `E|g'(X)| < ∞`,
**Stein's lemma** says that `(X - μ) g(X)` is integrable and `E[(X - μ) g(X)] = v E[g'(X)]`.
Its coordinate form for `X ~ N(θ, I_p)` on `ℝ^p` gives `E[(Xᵢ - θᵢ) h(X)] = E[∂ᵢ h(X)]` when
almost every line parallel to the `i`-th axis carries a differentiable slice of `h`, `∂ᵢ h` is
integrable and `(Xᵢ - θᵢ) h(X)` is integrable (in dimension `p ≥ 2` the last condition does not
follow from the others).

Summing over coordinates gives **Stein's unbiased risk estimate** (SURE): for an estimator
`X + g(X)` with square-integrable `g`, the quadratic risk is
`E ∑ (Xᵢ + gᵢ(X) - θᵢ)² = p + E[∑ gᵢ(X)² + 2 ∑ ∂ᵢ gᵢ(X)]`.

For `p ≥ 3`, the **James–Stein estimator** `δ(x) = (1 - (p - 2)/‖x‖²) x` has risk
`p - (p - 2)² E[‖X‖⁻²]`, strictly below the risk `p` of the usual estimator `X`, for every `θ`.

Vectors live in `Fin p → ℝ`, and `‖x‖²` is written as `∑ j, x j ^ 2` (the norm on `Fin p → ℝ`
is the sup norm). At `x = 0` the James–Stein factor uses Lean's `a / 0 = 0`; this point has
probability zero.

Scope: Stein's lemma is stated for everywhere differentiable `g` (respectively, a.e. line
slices differentiable everywhere), which covers `C¹` functions and the James–Stein shrinkage
for `p ≥ 3`; the absolutely continuous ("almost differentiable") case of Stein (1981) is not
covered.

## Main results

* `integrable_and_integral_sub_mul_gaussianReal`: Stein's lemma on `ℝ`.
* `integral_sub_mul_pi_gaussianReal`: Stein's lemma, coordinate form on `ℝ^p`.
* `integral_sum_sq_sub_pi_gaussianReal`: the risk of `X` is `p`.
* `integral_sum_sq_add_sub_pi_gaussianReal`: SURE.
* `integrable_and_integral_jamesStein_risk`, `integral_jamesStein_risk_lt`: James–Stein.
* `integral_inv_sum_sq_pi_gaussianReal_zero`, `integral_jamesStein_factor_pi_gaussianReal`:
  `E‖X‖⁻² = 1/(p - 2)` at `θ = 0`, and the James–Stein factor estimates `1/V` without bias (the
  empirical Bayes reading of Efron and Morris).
* `jamesSteinGrandMean`, `integral_jamesSteinGrandMean_risk_lt`: shrinkage towards the grand mean
  dominates `X` for `N ≥ 4` and any known `σ² > 0` (Efron 2021, Theorem 1, credited there to James
  and Stein 1961).
* `jamesSteinPlus`: the positive-part estimator. Its risk comparison with James–Stein is proved in
  `MathlibExt.Probability.Statistics.JamesSteinPlus`.

## References

* C. Stein, *Inadmissibility of the usual estimator for the mean of a multivariate normal
  distribution*, Proc. Third Berkeley Symp. Math. Statist. Probab., Vol. 1, Univ. California
  Press (1956), 197–206.
* W. James and C. Stein, *Estimation with quadratic loss*, Proc. Fourth Berkeley Symp. Math.
  Statist. Probab., Vol. 1, Univ. California Press (1961), 361–379.
* C. M. Stein, *Estimation of the mean of a multivariate normal distribution*, Ann. Statist. 9
  (1981), 1135–1151.
* B. Efron, *Empirical Bayes: Concepts and Methods*, manuscript (2021), Theorem 1 and equations
  (3.1)–(3.14).
* I. M. Johnstone, *Gaussian estimation: Sequence and wavelet models*, draft of 16 September
  2019, Section 2.6.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ProbabilityTheory

private lemma stein_weighted_iff (μ : ℝ) (v : NNReal) (hv : v ≠ 0)
    (f : ℝ → ℝ) :
    Integrable f (gaussianReal μ v) ↔
      Integrable (fun x => f x * gaussianPDFReal μ v x) := by
  rw [gaussianReal_of_var_ne_zero μ hv]
  simpa only [toReal_gaussianPDF] using
    integrable_withDensity_iff (measurable_gaussianPDF μ v)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)

private lemma stein_pdf_deriv (μ : ℝ) (v : NNReal) (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal μ v)
      (-((x - μ) * gaussianPDFReal μ v x) / v) x := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have h := (((hasDerivAt_id x).sub_const μ).pow 2).neg.div_const (2 * (v : ℝ))
  have he := h.exp.const_mul (Real.sqrt (2 * Real.pi * v))⁻¹
  convert he using 1
  · ext y
    rfl
  · simp only [gaussianPDFReal, Pi.pow_apply, Pi.neg_apply, id_eq, Nat.cast_ofNat,
      Nat.add_one_sub_one, pow_one, mul_one]
    field_simp

/-- **Stein's lemma**: for `X ~ N(μ, v)` and an everywhere differentiable `g` with integrable
derivative, `(X - μ) g(X)` is integrable and `E[(X - μ) g(X)] = v E[g'(X)]`. For `v = 0` both
sides vanish. -/
theorem integrable_and_integral_sub_mul_gaussianReal (μ : ℝ) (v : NNReal) {g g' : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Integrable g' (gaussianReal μ v)) :
    Integrable (fun x => (x - μ) * g x) (gaussianReal μ v) ∧
      ∫ x, (x - μ) * g x ∂gaussianReal μ v = v * ∫ x, g' x ∂gaussianReal μ v := by
  by_cases hv : v = 0
  · subst v
    simp [integrable_dirac]
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hvpos : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  let φ := gaussianPDFReal μ v
  let q : ℝ → ℝ := fun x => (x - μ) * φ x
  have hφnn (x : ℝ) : 0 ≤ φ x := gaussianPDFReal_nonneg μ v x
  have hφ : ∀ x, HasDerivAt φ (-q x / v) x := stein_pdf_deriv μ v hv
  have hcφ : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hφ x).continuousAt
  have hgcont : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
  have hq : Integrable q := by
    have hi : Integrable (fun x : ℝ => x - μ) (gaussianReal μ v) :=
      (memLp_id_gaussianReal 1).integrable (by simp) |>.sub (integrable_const μ)
    exact (stein_weighted_iff μ v hv _).mp hi
  have hφi : Integrable φ := integrable_gaussianPDFReal μ v
  have hdφ : Integrable (fun x => -q x / v) := hq.neg.div_const v
  have htop : Tendsto φ atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := μ)
      (fun x _ => hφ x) hdφ.integrableOn hφi.integrableOn
  have hbot : Tendsto φ atBot (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := μ)
      (fun x _ => hφ x) hdφ.integrableOn hφi.integrableOn
  have hright (t : ℝ) : ∫ x in Ioi t, q x = v * φ t := by
    have ht := integral_Ioi_of_hasDerivAt_of_tendsto' (a := t)
      (fun x _ => hφ x) hdφ.integrableOn htop
    simp only [integral_div, integral_neg, zero_sub] at ht
    apply (div_eq_iff hv').mp at ht
    linarith
  have hleft (t : ℝ) : ∫ x in Iic t, -q x = v * φ t := by
    have ht := integral_Iic_of_hasDerivAt_of_tendsto' (a := t)
      (fun x _ => hφ x) hdφ.integrableOn hbot
    simp only [integral_div, sub_zero] at ht
    simpa only [mul_comm] using (div_eq_iff hv').mp ht
  have hwi : Integrable (fun x => g' x * φ x) :=
    (stein_weighted_iff μ v hv _).mp hg'
  have hg'local (a b : ℝ) : IntervalIntegrable g' volume a b := by
    have hinv : ContinuousOn (fun x => (φ x)⁻¹) (uIcc a b) :=
      hcφ.continuousOn.inv₀ fun x _ => (gaussianPDFReal_pos μ v x hv).ne'
    have hi := hwi.integrableOn.mul_continuousOn hinv isCompact_uIcc
    have hi' : IntegrableOn g' (uIcc a b) := by
      convert hi using 1
      ext x
      have hn : φ x ≠ 0 := (gaussianPDFReal_pos μ v x hv).ne'
      simp only [mul_assoc, mul_inv_cancel₀ hn, mul_one]
    exact hi'.intervalIntegrable
  have hgm : Measurable g' := by
    have he : g' = deriv g := funext fun x => (hg x).deriv.symm
    rw [he]
    exact measurable_deriv g
  let Kp : ℝ × ℝ → ℝ := fun z =>
    if μ ≤ z.2 ∧ z.2 ≤ z.1 then |g' z.2| * q z.1 else 0
  let Km : ℝ × ℝ → ℝ := fun z =>
    if z.1 ≤ z.2 ∧ z.2 ≤ μ then |g' z.2| * (-q z.1) else 0
  have hKpm : Measurable Kp := by
    apply Measurable.ite
      ((measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst))
    · dsimp [q]
      fun_prop
    · exact measurable_const
  have hKmm : Measurable Km := by
    apply Measurable.ite
      ((measurableSet_le measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const))
    · dsimp [q]
      fun_prop
    · exact measurable_const
  have hKpnn (z : ℝ × ℝ) : 0 ≤ Kp z := by
    dsimp [Kp]
    split_ifs with hz
    · exact mul_nonneg (abs_nonneg _) (mul_nonneg (sub_nonneg.mpr (hz.1.trans hz.2))
        (gaussianPDFReal_nonneg μ v z.1))
    · exact le_rfl
  have hKmnn (z : ℝ × ℝ) : 0 ≤ Km z := by
    dsimp [Km]
    split_ifs with hz
    · exact mul_nonneg (abs_nonneg _) (neg_nonneg.mpr
        (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hz.1.trans hz.2))
          (gaussianPDFReal_nonneg μ v z.1)))
    · exact le_rfl
  have hKpslice (t : ℝ) : Integrable (fun x => Kp (x, t)) := by
    by_cases ht : μ ≤ t
    · have he : (fun x => Kp (x, t)) =
          (Ici t).indicator (fun x => |g' t| * q x) := by
        ext x
        simp [Kp, ht, Set.indicator]
      rw [he]
      exact (hq.const_mul _).indicator measurableSet_Ici
    · simp [Kp, ht]
  have hKmslice (t : ℝ) : Integrable (fun x => Km (x, t)) := by
    by_cases ht : t ≤ μ
    · have he : (fun x => Km (x, t)) =
          (Iic t).indicator (fun x => |g' t| * (-q x)) := by
        ext x
        simp [Km, ht, Set.indicator]
      rw [he]
      exact (hq.neg.const_mul _).indicator measurableSet_Iic
    · simp [Km, ht]
  have hKpbound (t : ℝ) : ∫ x, ‖Kp (x, t)‖ ≤ v * (|g' t| * φ t) := by
    simp only [Real.norm_eq_abs, abs_of_nonneg (hKpnn _)]
    by_cases ht : μ ≤ t
    · have he : (fun x => Kp (x, t)) =
          (Ici t).indicator (fun x => |g' t| * q x) := by
        ext x
        simp [Kp, ht, Set.indicator]
      rw [he, integral_indicator measurableSet_Ici, integral_const_mul,
        integral_Ici_eq_integral_Ioi, hright]
      exact le_of_eq (by ring)
    · simp only [Kp, ht, false_and, ↓reduceIte, integral_zero]
      have := hφnn t
      positivity
  have hKmbound (t : ℝ) : ∫ x, ‖Km (x, t)‖ ≤ v * (|g' t| * φ t) := by
    simp only [Real.norm_eq_abs, abs_of_nonneg (hKmnn _)]
    by_cases ht : t ≤ μ
    · have he : (fun x => Km (x, t)) =
          (Iic t).indicator (fun x => |g' t| * (-q x)) := by
        ext x
        simp [Km, ht, Set.indicator]
      rw [he, integral_indicator measurableSet_Iic, integral_const_mul, hleft]
      exact le_of_eq (by ring)
    · simp only [Km, ht, and_false, ↓reduceIte, integral_zero]
      have := hφnn t
      positivity
  have hdom : Integrable (fun t => v * (|g' t| * φ t)) := by
    convert hwi.norm.const_mul (v : ℝ) using 1
    ext t
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hφnn t)]
  have hKpi : Integrable Kp (volume.prod volume) := by
    apply (integrable_prod_iff' hKpm.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ hKpslice, hdom.mono'
      hKpm.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable ?_⟩
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
    exact hKpbound t
  have hKmi : Integrable Km (volume.prod volume) := by
    apply (integrable_prod_iff' hKmm.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ hKmslice, hdom.mono'
      hKmm.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable ?_⟩
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
    exact hKmbound t
  have hbound (x : ℝ) : ‖q x * (g x - g μ)‖ ≤
      (∫ t, Kp (x, t)) + ∫ t, Km (x, t) := by
    by_cases hx : μ ≤ x
    · have hqn : 0 ≤ q x := mul_nonneg (sub_nonneg.mpr hx) (hφnn x)
      have he : (fun t => Kp (x, t)) =
          (Icc μ x).indicator (fun t => |g' t| * q x) := by
        ext t
        simp [Kp, Set.indicator]
      have hb : |g x - g μ| ≤ ∫ t in μ..x, |g' t| := by
        rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t _ => hg t) (hg'local μ x)]
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm (f := g') (μ := volume) hx
      calc
        ‖q x * (g x - g μ)‖ = q x * |g x - g μ| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hqn]
        _ ≤ q x * ∫ t in μ..x, |g' t| := mul_le_mul_of_nonneg_left hb hqn
        _ = ∫ t, Kp (x, t) := by
          rw [he, integral_indicator measurableSet_Icc, integral_mul_const,
            integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx]
          ring
        _ ≤ (∫ t, Kp (x, t)) + ∫ t, Km (x, t) :=
          le_add_of_nonneg_right (integral_nonneg fun t => hKmnn (x, t))
    · have hx' : x ≤ μ := le_of_not_ge hx
      have hqn : 0 ≤ -q x := neg_nonneg.mpr
        (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx') (hφnn x))
      have he : (fun t => Km (x, t)) =
          (Icc x μ).indicator (fun t => |g' t| * (-q x)) := by
        ext t
        simp [Km, Set.indicator]
      have hb : |g x - g μ| ≤ ∫ t in x..μ, |g' t| := by
        rw [abs_sub_comm, ← intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun t _ => hg t) (hg'local x μ)]
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm (f := g') (μ := volume) hx'
      calc
        ‖q x * (g x - g μ)‖ = (-q x) * |g x - g μ| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (neg_nonneg.mp hqn)]
        _ ≤ (-q x) * ∫ t in x..μ, |g' t| := mul_le_mul_of_nonneg_left hb hqn
        _ = ∫ t, Km (x, t) := by
          rw [he, integral_indicator measurableSet_Icc, integral_mul_const,
            integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx']
          ring
        _ ≤ (∫ t, Kp (x, t)) + ∫ t, Km (x, t) :=
          le_add_of_nonneg_left (integral_nonneg fun t => hKpnn (x, t))
  have hqdiff : Integrable (fun x => q x * (g x - g μ)) :=
    (hKpi.integral_prod_left.add hKmi.integral_prod_left).mono'
      (by dsimp [q]; fun_prop) (ae_of_all _ hbound)
  have hqg : Integrable (fun x => q x * g x) := by
    convert hqdiff.add (hq.mul_const (g μ)) using 1
    ext x
    dsimp
    ring
  have hgauss : Integrable (fun x => (x - μ) * g x) (gaussianReal μ v) := by
    apply (stein_weighted_iff μ v hv _).mpr
    convert hqg using 1
    ext x
    dsimp [q]
    ring
  have hgφcont : Continuous (fun x => g x * φ x) := hgcont.mul hcφ
  have hcompact : Integrable
      ((Icc (μ - 1) (μ + 1)).indicator (fun x => ‖g x * φ x‖)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr hgφcont.norm.integrableOn_Icc
  have hgφ : Integrable (fun x => g x * φ x) := by
    apply (hqg.norm.add hcompact).mono' hgφcont.aestronglyMeasurable
    filter_upwards with x
    by_cases hx : x ∈ Icc (μ - 1) (μ + 1)
    · simp only [Set.indicator_of_mem hx, Pi.add_apply]
      exact le_add_of_nonneg_left (norm_nonneg _)
    · simp only [Set.indicator_of_notMem hx, Pi.add_apply, add_zero]
      have hxabs : 1 ≤ |x - μ| := by
        by_contra hn
        have hsmall := abs_lt.mp (lt_of_not_ge hn)
        apply hx
        constructor <;> linarith
      calc
        ‖g x * φ x‖ ≤ |x - μ| * ‖g x * φ x‖ := by
          nlinarith [norm_nonneg (g x * φ x)]
        _ = ‖q x * g x‖ := by
          simp only [Real.norm_eq_abs, q, abs_mul]
          ring
  have hgdφ : Integrable (fun x => g x * (-q x / v)) := by
    convert hqg.neg.div_const v using 1
    ext x
    simp only [Pi.neg_apply]
    ring
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := g) (u' := g') (v := φ) (v' := fun x => -q x / v)
    (fun x _ => hg x) (fun x _ => hφ x) hgdφ hwi hgφ
  have hid : -(∫ x, q x * g x) / v = -(∫ x, g' x * φ x) := by
    rw [← integral_neg, ← integral_div]
    convert hibp using 1
    congr 1
    ext x
    ring
  have hresult : ∫ x, q x * g x = v * ∫ x, g' x * φ x := by
    apply (div_eq_iff hv').mp at hid
    linarith
  refine ⟨hgauss, ?_⟩
  simp only [integral_gaussianReal_eq_integral_smul hv, smul_eq_mul]
  simpa only [q, φ, mul_assoc, mul_left_comm, mul_comm] using hresult

/-- **Stein's lemma**, coordinate form: for `X ~ N(θ, I_p)` and a function `h` whose slices
along the `i`-th axis are differentiable everywhere (for almost every base point) with
integrable partial derivative `dh`, `E[(Xᵢ - θᵢ) h(X)] = E[dh(X)]` whenever `(Xᵢ - θᵢ) h(X)` is
integrable. Unlike the one-dimensional case, this integrability does not follow from that of
`dh`: `h(x) = exp(x₁²)` has `∂₀ h = 0` but `x₀ h(x)` is not integrable. -/
theorem integral_sub_mul_pi_gaussianReal {p : ℕ} (θ : Fin p → ℝ) (i : Fin p)
    {h dh : (Fin p → ℝ) → ℝ}
    (hd : ∀ᵐ x ∂(Measure.pi fun j => gaussianReal (θ j) 1),
      ∀ t, HasDerivAt (fun s => h (Function.update x i s)) (dh (Function.update x i t)) t)
    (hdi : Integrable dh (Measure.pi fun j => gaussianReal (θ j) 1))
    (hhi : Integrable (fun x => (x i - θ i) * h x) (Measure.pi fun j => gaussianReal (θ j) 1)) :
    ∫ x, (x i - θ i) * h x ∂(Measure.pi fun j => gaussianReal (θ j) 1) =
      ∫ x, dh x ∂(Measure.pi fun j => gaussianReal (θ j) 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := i.pos; omega⟩
  set P := Measure.pi fun j => gaussianReal (θ j) 1
  set ν := Measure.pi fun j : Fin n => gaussianReal (θ (i.succAbove j)) 1
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hmp : MeasurePreserving e P ((gaussianReal (θ i) 1).prod ν) :=
    measurePreserving_piFinSuccAbove (fun j => gaussianReal (θ j) 1) i
  have hs := hmp.symm
  have he : ∀ z : ℝ × (Fin n → ℝ), e.symm z = Fin.insertNth i z.1 z.2 := fun _ => rfl
  have hL := hs.integral_comp' (g := fun x => (x i - θ i) * h x)
  have hR := hs.integral_comp' (g := dh)
  have hLi := hs.integrable_comp_of_integrable hhi
  have hRi := hs.integrable_comp_of_integrable hdi
  simp only [Function.comp_def, he, Fin.insertNth_apply_same] at hL hR hLi hRi
  rw [← hL, ← hR, integral_prod_symm _ hLi, integral_prod_symm _ hRi]
  have hQ := hs.quasiMeasurePreserving.ae hd
  simp only [he, Fin.update_insertNth] at hQ
  obtain ⟨t₀, ht₀⟩ := (Measure.ae_ae_of_ae_prod hQ).exists
  refine integral_congr_ae ?_
  filter_upwards [ht₀, hRi.prod_left_ae] with y hy hyi
  have := (integrable_and_integral_sub_mul_gaussianReal (θ i) 1
    (g := fun t => h (Fin.insertNth i t y)) (g' := fun t => dh (Fin.insertNth i t y)) hy hyi).2
  simpa using this

private theorem integral_sq_sub_eval_pi {p : ℕ} (θ : Fin p → ℝ) (i : Fin p) :
    ∫ x, (x i - θ i) ^ 2 ∂(Measure.pi fun j => gaussianReal (θ j) 1) = 1 := by
  have hmap := (measurePreserving_eval (fun j => gaussianReal (θ j) 1) i).map_eq
  calc ∫ x, (x i - θ i) ^ 2 ∂(Measure.pi fun j => gaussianReal (θ j) 1)
      = ∫ y, (y - θ i) ^ 2 ∂((Measure.pi fun j => gaussianReal (θ j) 1).map fun x => x i) :=
        (integral_map (by fun_prop : Measurable fun x : Fin p → ℝ => x i).aemeasurable
          (by fun_prop : Measurable fun y : ℝ => (y - θ i) ^ 2).aestronglyMeasurable).symm
    _ = 1 := by
      rw [hmap]
      have h := variance_id_gaussianReal (μ := θ i) (v := 1)
      rw [variance_eq_integral aemeasurable_id] at h
      simpa [integral_id_gaussianReal] using h

private theorem integrable_sq_sub_eval_pi {p : ℕ} (θ : Fin p → ℝ) (i : Fin p) :
    Integrable (fun x : Fin p → ℝ => (x i - θ i) ^ 2)
      (Measure.pi fun j => gaussianReal (θ j) 1) := by
  have hmap := (measurePreserving_eval (fun j => gaussianReal (θ j) 1) i)
  have hint : Integrable (fun y : ℝ => (y - θ i) ^ 2) (gaussianReal (θ i) 1) := by
    have := ((memLp_id_gaussianReal (μ := θ i) (v := 1) 2).sub
      (memLp_const (θ i))).integrable_sq
    simpa using this
  exact hmap.integrable_comp_of_integrable hint

/-- The quadratic risk of the usual estimator `X` of the mean of `N(θ, I_p)` is `p`. -/
theorem integral_sum_sq_sub_pi_gaussianReal {p : ℕ} (θ : Fin p → ℝ) :
    ∫ x, ∑ i, (x i - θ i) ^ 2 ∂(Measure.pi fun j => gaussianReal (θ j) 1) = p := by
  rw [integral_finsetSum _ fun i _ => integrable_sq_sub_eval_pi θ i]
  simp [integral_sq_sub_eval_pi]

private theorem memLp_sub_eval_pi {p : ℕ} (θ : Fin p → ℝ) (i : Fin p) :
    MemLp (fun x : Fin p → ℝ => x i - θ i) 2 (Measure.pi fun j => gaussianReal (θ j) 1) := by
  have h := ((memLp_id_gaussianReal' (μ := θ i) (v := 1) 2 (by norm_num)).sub
    (memLp_const (θ i))).comp_measurePreserving
      (measurePreserving_eval (fun j => gaussianReal (θ j) 1) i)
  exact h

/-- **Stein's unbiased risk estimate**: for `X ~ N(θ, I_p)` and an estimator `X + g(X)` whose
coordinates `gᵢ` are square integrable and satisfy the hypotheses of Stein's lemma in the `i`-th
coordinate with partial derivative `dgᵢ`, the quadratic risk is
`p + E[∑ gᵢ(X)² + 2 ∑ dgᵢ(X)]`. -/
theorem integral_sum_sq_add_sub_pi_gaussianReal {p : ℕ} (θ : Fin p → ℝ)
    {g dg : Fin p → (Fin p → ℝ) → ℝ}
    (hd : ∀ i, ∀ᵐ x ∂(Measure.pi fun j => gaussianReal (θ j) 1),
      ∀ t, HasDerivAt (fun s => g i (Function.update x i s)) (dg i (Function.update x i t)) t)
    (hdi : ∀ i, Integrable (dg i) (Measure.pi fun j => gaussianReal (θ j) 1))
    (hg2 : ∀ i, MemLp (g i) 2 (Measure.pi fun j => gaussianReal (θ j) 1)) :
    ∫ x, ∑ i, (x i + g i x - θ i) ^ 2 ∂(Measure.pi fun j => gaussianReal (θ j) 1) =
      p + ∫ x, ∑ i, (g i x ^ 2 + 2 * dg i x) ∂(Measure.pi fun j => gaussianReal (θ j) 1) := by
  set P := Measure.pi fun j => gaussianReal (θ j) 1
  have hst : ∀ i, Integrable (fun x => (x i - θ i) * g i x) P ∧
      ∫ x, (x i - θ i) * g i x ∂P = ∫ x, dg i x ∂P := fun i => by
    have hint : Integrable (fun x => (x i - θ i) * g i x) P :=
      (memLp_sub_eval_pi θ i).integrable_mul (hg2 i)
    exact ⟨hint, integral_sub_mul_pi_gaussianReal θ i (hd i) (hdi i) hint⟩
  have hsq : ∀ i, Integrable (fun x => g i x ^ 2) P := fun i => (hg2 i).integrable_sq
  have hpt : ∀ x : Fin p → ℝ, ∑ i, (x i + g i x - θ i) ^ 2 =
      ∑ i, (x i - θ i) ^ 2 + ∑ i, (g i x ^ 2 + 2 * ((x i - θ i) * g i x)) := by
    intro x
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hA : ∀ i, Integrable (fun x => g i x ^ 2 + 2 * ((x i - θ i) * g i x)) P := fun i =>
    (hsq i).add ((hst i).1.const_mul 2)
  have hB : ∀ i, Integrable (fun x => g i x ^ 2 + 2 * dg i x) P := fun i =>
    (hsq i).add ((hdi i).const_mul 2)
  simp_rw [hpt]
  rw [integral_add (integrable_finsetSum _ fun i _ => integrable_sq_sub_eval_pi θ i)
      (integrable_finsetSum _ fun i _ => hA i),
    integral_sum_sq_sub_pi_gaussianReal, integral_finsetSum _ fun i _ => hA i,
    integral_finsetSum _ fun i _ => hB i]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_add (hsq i) ((hst i).1.const_mul 2), integral_add (hsq i) ((hdi i).const_mul 2),
    integral_const_mul, integral_const_mul, (hst i).2]

/-- The James–Stein estimator `δ(x) = (1 - (p - 2) / ‖x‖²) x` of the mean of `N(θ, I_p)`. At
`x = 0` the factor is `1` by Lean's `a / 0 = 0` convention, so `δ(0) = 0`. -/
noncomputable def jamesStein {p : ℕ} (x : Fin p → ℝ) : Fin p → ℝ :=
  fun i => (1 - ((p : ℝ) - 2) / ∑ j, x j ^ 2) * x i

private lemma gaussian_le_volume (θ : ℝ) : gaussianReal θ 1 ≤ volume := by
  rw [gaussianReal_of_var_ne_zero θ one_ne_zero]
  apply le_trans (b := volume.withDensity (fun _ : ℝ => 1)) ?_ (by simp)
  apply withDensity_mono
  exact Filter.Eventually.of_forall fun x => by
    change ENNReal.ofReal (gaussianPDFReal θ 1 x) ≤ 1
    apply ENNReal.ofReal_le_one.mpr
    have hs : 1 ≤ Real.sqrt (2 * Real.pi * (1 : ℝ)) := by
      apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
      nlinarith [Real.one_le_pi_div_two]
    have he : Real.exp (-(x - θ) ^ 2 / (2 * (1 : ℝ))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by norm_num)
    unfold gaussianPDFReal
    simp only [NNReal.coe_one]
    calc
      _ ≤ (Real.sqrt (2 * Real.pi * (1 : ℝ)))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ ≤ 1 := by simpa using (inv_le_one₀ (by positivity)).mpr hs

private lemma pi_gaussian_le_volume {p : ℕ} (θ : Fin p → ℝ) :
    (Measure.pi fun j => gaussianReal (θ j) 1) ≤ volume := by
  have ho : (OuterMeasure.pi fun i => (gaussianReal (θ i) 1).toOuterMeasure) ≤
      (OuterMeasure.pi fun _ : Fin p => (volume : Measure ℝ).toOuterMeasure) := by
    apply OuterMeasure.le_pi.mpr
    intro s _
    exact (OuterMeasure.pi_pi_le _ s).trans
      (Finset.prod_le_prod fun i _ => gaussian_le_volume (θ i) (s i))
  apply Measure.le_iff.mpr
  intro s hs
  rw [volume_pi, Measure.pi, Measure.pi,
    toMeasure_apply _ _ hs, toMeasure_apply _ _ hs]
  exact ho s

private lemma norm_sq_le_sum_sq {p : ℕ} (hp : 0 < p) (x : Fin p → ℝ) :
    ‖x‖ ^ 2 ≤ ∑ j, x j ^ 2 := by
  classical
  let : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  obtain ⟨⟨i, hi⟩, _⟩ := IsGreatest.pi_norm x
  rw [← hi]
  change ‖x i‖ ^ 2 ≤ _
  rw [Real.norm_eq_abs, sq_abs]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

private lemma integrable_reciprocal {p : ℕ} (hp : 3 ≤ p) (θ : Fin p → ℝ) :
    Integrable (fun x : Fin p → ℝ => (∑ j, x j ^ 2)⁻¹)
      (Measure.pi fun j => gaussianReal (θ j) 1) := by
  have hm : Measurable (fun x : Fin p → ℝ => (∑ j, x j ^ 2)⁻¹) := by fun_prop
  have hb : IntegrableOn (fun x : Fin p → ℝ => (∑ j, x j ^ 2)⁻¹)
      (Metric.ball 0 1) volume := by
    refine integrableOn_ball_of_norm_le_rpow
      (by simpa using (show 1 ≤ p by omega)) (C := 1) (α := 2) ?_ ?_
      hm.aestronglyMeasurable
    · simpa using (show (2 : ℝ) < p by exact_mod_cast (show 2 < p by omega))
    · apply Filter.Eventually.of_forall
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr
        (Finset.sum_nonneg fun i _ => sq_nonneg (x i))), one_mul,
        Real.rpow_neg (norm_nonneg _), Real.rpow_two]
      by_cases hx : x = 0
      · simp [hx]
      · exact inv_anti₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))
          (norm_sq_le_sum_sq (by omega) x)
  have hb' : IntegrableOn (fun x : Fin p → ℝ => (∑ j, x j ^ 2)⁻¹)
      (Metric.ball 0 1) (Measure.pi fun j => gaussianReal (θ j) 1) :=
    hb.mono_measure (pi_gaussian_le_volume θ)
  have hc : IntegrableOn (fun x : Fin p → ℝ => (∑ j, x j ^ 2)⁻¹)
      (Metric.ball 0 1)ᶜ (Measure.pi fun j => gaussianReal (θ j) 1) := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) hm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with x hx
    have hx' : 1 ≤ ‖x‖ := by simpa [Metric.mem_ball, dist_zero_right] using hx
    have hs : 1 ≤ ∑ j, x j ^ 2 := by
      nlinarith [norm_sq_le_sum_sq (by omega) x]
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by linarith))]
    exact (inv_le_one₀ (by linarith)).mpr hs
  simpa using hb'.union hc

private lemma sum_update_sq {p : ℕ} (x : Fin p → ℝ) (i : Fin p) (t : ℝ) :
    (∑ j, Function.update x i t j ^ 2) = t ^ 2 + ∑ j ∈ Finset.univ.erase i, x j ^ 2 := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

private lemma shrinkage_deriv {p : ℕ} (a : ℝ) (x : Fin p → ℝ) (i j : Fin p)
    (hji : j ≠ i) (hxj : x j ≠ 0) (t : ℝ) :
    HasDerivAt (fun s => -a * Function.update x i s i /
      ∑ k, Function.update x i s k ^ 2)
      (-a * ((∑ k, Function.update x i t k ^ 2) -
        2 * Function.update x i t i ^ 2) /
        (∑ k, Function.update x i t k ^ 2) ^ 2) t := by
  classical
  let K := ∑ k ∈ Finset.univ.erase i, x k ^ 2
  have hK : 0 < K := lt_of_lt_of_le (sq_pos_of_ne_zero hxj)
    (Finset.single_le_sum (fun k _ => sq_nonneg (x k)) (Finset.mem_erase.mpr ⟨hji, by simp⟩))
  have hD : t ^ 2 + K ≠ 0 := by nlinarith [sq_nonneg t]
  have hd := ((hasDerivAt_id t).const_mul (-a)).div
    (((hasDerivAt_id t).pow 2).add_const K) hD
  convert hd using 1
  · funext s
    simp [sum_update_sq, K]
  · simp only [Function.update_self, sum_update_sq]
    dsimp [K]
    congr 1
    ring

private lemma shrinkage_sq_bound {p : ℕ} (a : ℝ) (x : Fin p → ℝ) (i : Fin p) :
    (-a * x i / ∑ j, x j ^ 2) ^ 2 ≤ a ^ 2 * (∑ j, x j ^ 2)⁻¹ := by
  have hi : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  by_cases hz : (∑ j, x j ^ 2) = 0
  · simp [hz]
  · rw [div_pow, mul_pow, neg_sq]
    calc
      _ ≤ a ^ 2 * (∑ j, x j ^ 2) / (∑ j, x j ^ 2) ^ 2 := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hi (sq_nonneg a))
          (sq_nonneg _)
      _ = _ := by field_simp

private lemma shrinkage_deriv_bound {p : ℕ} (a : ℝ) (x : Fin p → ℝ) (i : Fin p) :
    ‖-a * ((∑ j, x j ^ 2) - 2 * x i ^ 2) / (∑ j, x j ^ 2) ^ 2‖ ≤
      |a| * (∑ j, x j ^ 2)⁻¹ := by
  have hS : 0 ≤ ∑ j, x j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg (x j)
  have hi : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  have ha : |(∑ j, x j ^ 2) - 2 * x i ^ 2| ≤ ∑ j, x j ^ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (x i)]
  by_cases hz : (∑ j, x j ^ 2) = 0
  · simp [hz]
  · rw [Real.norm_eq_abs, abs_div, abs_mul, abs_neg, abs_pow, abs_of_nonneg hS]
    calc
      _ ≤ |a| * (∑ j, x j ^ 2) / (∑ j, x j ^ 2) ^ 2 := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ha (abs_nonneg a))
          (sq_nonneg _)
      _ = _ := by field_simp

private lemma ae_sum_sq_pos {p : ℕ} (hp : 0 < p) (θ : Fin p → ℝ) :
    ∀ᵐ x ∂(Measure.pi fun j => gaussianReal (θ j) 1), 0 < ∑ j, x j ^ 2 := by
  let : ∀ i, NullSingletonClass (gaussianReal (θ i) 1) :=
    fun i => nullSingletonClass_gaussianReal one_ne_zero
  let i : Fin p := ⟨0, hp⟩
  filter_upwards [Measure.ae_eval_ne (fun j => gaussianReal (θ j) 1) i 0] with x hx
  exact lt_of_lt_of_le (sq_pos_of_ne_zero hx)
    (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i))

private lemma sum_shrinkage_correction {p : ℕ} (x : Fin p → ℝ)
    (hx : (∑ j, x j ^ 2) ≠ 0) :
    (∑ i : Fin p, ((-((p : ℝ) - 2) * x i / ∑ j, x j ^ 2) ^ 2 +
      2 * (-((p : ℝ) - 2) * ((∑ j, x j ^ 2) - 2 * x i ^ 2) /
        (∑ j, x j ^ 2) ^ 2))) = -((p : ℝ) - 2) ^ 2 * (∑ j, x j ^ 2)⁻¹ := by
  have ht (i : Fin p) :
      (-((p : ℝ) - 2) * x i / ∑ j, x j ^ 2) ^ 2 +
        2 * (-((p : ℝ) - 2) * ((∑ j, x j ^ 2) - 2 * x i ^ 2) /
          (∑ j, x j ^ 2) ^ 2) =
      (((p : ℝ) - 2) ^ 2 * x i ^ 2 -
        2 * ((p : ℝ) - 2) * (∑ j, x j ^ 2) + 4 * ((p : ℝ) - 2) * x i ^ 2) /
        (∑ j, x j ^ 2) ^ 2 := by
    field_simp
    ring
  simp_rw [ht]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- **James–Stein** (1961): for `p ≥ 3` and `X ~ N(θ, I_p)`, `‖X‖⁻²` is integrable and the risk
of the James–Stein estimator is `p - (p - 2)² E[‖X‖⁻²]`. -/
theorem integrable_and_integral_jamesStein_risk {p : ℕ} (hp : 3 ≤ p) (θ : Fin p → ℝ) :
    Integrable (fun x : Fin p → ℝ => (∑ j, x j ^ 2)⁻¹)
        (Measure.pi fun j => gaussianReal (θ j) 1) ∧
      ∫ x, ∑ i, (jamesStein x i - θ i) ^ 2 ∂(Measure.pi fun j => gaussianReal (θ j) 1) =
        p - ((p : ℝ) - 2) ^ 2 *
          ∫ x, (∑ j, x j ^ 2)⁻¹ ∂(Measure.pi fun j => gaussianReal (θ j) 1) := by
  classical
  let a : ℝ := (p : ℝ) - 2
  let g : Fin p → (Fin p → ℝ) → ℝ := fun i x => -a * x i / ∑ j, x j ^ 2
  let dg : Fin p → (Fin p → ℝ) → ℝ := fun i x =>
    -a * ((∑ j, x j ^ 2) - 2 * x i ^ 2) / (∑ j, x j ^ 2) ^ 2
  have hr := integrable_reciprocal hp θ
  refine ⟨hr, ?_⟩
  have hg (i : Fin p) : Measurable (g i) := by dsimp [g]; fun_prop
  have hdg (i : Fin p) : Measurable (dg i) := by dsimp [dg]; fun_prop
  have hd (i : Fin p) : ∀ᵐ x ∂(Measure.pi fun j => gaussianReal (θ j) 1),
      ∀ t, HasDerivAt (fun s => g i (Function.update x i s))
        (dg i (Function.update x i t)) t := by
    obtain ⟨j, hji, _⟩ := Fin.exists_ne_and_ne_of_two_lt i i (by omega)
    let : NullSingletonClass (gaussianReal (θ j) 1) :=
      nullSingletonClass_gaussianReal one_ne_zero
    filter_upwards [Measure.ae_eval_ne (fun k => gaussianReal (θ k) 1) j 0] with x hx
    intro t
    exact shrinkage_deriv a x i j hji hx t
  have hdi (i : Fin p) : Integrable (dg i) (Measure.pi fun j => gaussianReal (θ j) 1) :=
    (hr.const_mul |a|).mono' (hdg i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => shrinkage_deriv_bound a x i)
  have hg2 (i : Fin p) : MemLp (g i) 2 (Measure.pi fun j => gaussianReal (θ j) 1) := by
    apply (memLp_two_iff_integrable_sq (hg i).aestronglyMeasurable).mpr
    apply (hr.const_mul (a ^ 2)).mono' ((hg i).pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact shrinkage_sq_bound a x i
  calc
    _ = ∫ x, ∑ i, (x i + g i x - θ i) ^ 2
        ∂(Measure.pi fun j => gaussianReal (θ j) 1) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        dsimp [jamesStein, g, a]
        ring
    _ = p + ∫ x, ∑ i, (g i x ^ 2 + 2 * dg i x)
        ∂(Measure.pi fun j => gaussianReal (θ j) 1) :=
      integral_sum_sq_add_sub_pi_gaussianReal θ hd hdi hg2
    _ = p + ∫ x, -a ^ 2 * (∑ j, x j ^ 2)⁻¹
        ∂(Measure.pi fun j => gaussianReal (θ j) 1) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_sum_sq_pos (by omega) θ] with x hx
      exact sum_shrinkage_correction x hx.ne'
    _ = _ := by rw [integral_const_mul]; dsimp [a]; ring


/-- **James–Stein dominance** (Stein 1956, James–Stein 1961): for `p ≥ 3`, the James–Stein
estimator has strictly smaller quadratic risk than `X` at every mean `θ`. -/
theorem integral_jamesStein_risk_lt {p : ℕ} (hp : 3 ≤ p) (θ : Fin p → ℝ) :
    ∫ x, ∑ i, (jamesStein x i - θ i) ^ 2 ∂(Measure.pi fun j => gaussianReal (θ j) 1) <
      ∫ x, ∑ i, (x i - θ i) ^ 2 ∂(Measure.pi fun j => gaussianReal (θ j) 1) := by
  have h := integrable_and_integral_jamesStein_risk hp θ
  rw [h.2, integral_sum_sq_sub_pi_gaussianReal]
  set P := Measure.pi fun j => gaussianReal (θ j) 1
  have i0 : Fin p := ⟨0, by omega⟩
  have hnull : P {x | x i0 = 0} = 0 := by
    have := nullSingletonClass_gaussianReal (μ := θ i0) (v := 1) one_ne_zero
    have := (measurePreserving_eval (fun j => gaussianReal (θ j) 1) i0).measure_preimage
      (s := {0}) (measurableSet_singleton 0).nullMeasurableSet
    rw [measure_singleton] at this
    simpa [Set.preimage] using this
  have hsub : (Function.support fun x : Fin p → ℝ => (∑ j, x j ^ 2)⁻¹)ᶜ ⊆ {x | x i0 = 0} := by
    intro x hx
    simp only [Set.mem_compl_iff, Function.mem_support, ne_eq, not_not, inv_eq_zero] at hx
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (x j)).1 hx i0
      (Finset.mem_univ _)
    simpa using this
  have hsupp : 0 < P (Function.support fun x : Fin p → ℝ => (∑ j, x j ^ 2)⁻¹) := by
    have hc : P (Function.support fun x : Fin p → ℝ => (∑ j, x j ^ 2)⁻¹)ᶜ = 0 :=
      measure_mono_null hsub hnull
    have hmeas : MeasurableSet (Function.support fun x : Fin p → ℝ => (∑ j, x j ^ 2)⁻¹) :=
      measurableSet_support (by fun_prop)
    rw [prob_compl_eq_zero_iff hmeas] at hc
    rw [hc]
    exact one_pos
  have hpos : 0 < ∫ x, (∑ j, x j ^ 2)⁻¹ ∂P :=
    (integral_pos_iff_support_of_nonneg (fun x => by positivity) h.1).2 hsupp
  have hp2 : 0 < ((p : ℝ) - 2) ^ 2 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith
  nlinarith

/-- **James–Stein estimator shrinking towards the grand mean.** For `x ∈ ℝ^N` and a known noise
variance `σ²`, with `x̄ = (∑ⱼ xⱼ) / N` and `S = ∑ⱼ (xⱼ - x̄)²`, the estimate of the `i`-th mean is
`x̄ + (1 - (N - 3) σ² / S) (xᵢ - x̄)` (Efron, *Empirical Bayes: Concepts and Methods*, 2021
manuscript, equation (3.4)). When `S = 0` Lean's `a / 0 = 0` makes the estimate `x`. -/
noncomputable def jamesSteinGrandMean {N : ℕ} (σ2 : ℝ) (x : Fin N → ℝ) : Fin N → ℝ :=
  fun i => (∑ j, x j) / N +
    (1 - ((N : ℝ) - 3) * σ2 / ∑ j, (x j - (∑ k, x k) / N) ^ 2) * (x i - (∑ j, x j) / N)

/-- **Positive-part James–Stein estimator.** `δ⁺(x) = max(0, 1 - (p - 2) / ‖x‖²) x`, the James–Stein
estimator with its shrinkage factor truncated at `0` (Johnstone, *Gaussian estimation: Sequence
and wavelet models*, draft of 16 September 2019, equation (2.65)). -/
noncomputable def jamesSteinPlus {p : ℕ} (x : Fin p → ℝ) : Fin p → ℝ :=
  fun i => max 0 (1 - ((p : ℝ) - 2) / ∑ j, x j ^ 2) * x i

/-- **Mean of the inverse squared norm of a standard Gaussian vector.** For `p ≥ 3` and
`X ~ N(0, I_p)`, `E[‖X‖⁻²] = 1 / (p - 2)`: the mean of the inverse of a `χ²_p` variable
(Johnstone, *Gaussian estimation: Sequence and wavelet models*, draft of 16 September 2019,
equation (2.67)). The proof reads it off the James–Stein risk formula at `θ = 0`. -/
theorem integral_inv_sum_sq_pi_gaussianReal_zero {p : ℕ} (hp : 3 ≤ p) :
    ∫ x, (∑ j, x j ^ 2)⁻¹ ∂(Measure.pi fun _ : Fin p => gaussianReal 0 1) = 1 / ((p : ℝ) - 2) := by
  set P := Measure.pi fun _ : Fin p => gaussianReal 0 1
  have h := integrable_and_integral_jamesStein_risk hp (fun _ => 0)
  have hS : ∫ x, ∑ j, x j ^ 2 ∂P = p := by
    simpa using integral_sum_sq_sub_pi_gaussianReal (p := p) (fun _ => 0)
  have hSi : Integrable (fun x : Fin p → ℝ => ∑ j, x j ^ 2) P :=
    integrable_finsetSum _ fun i _ => by
      simpa using integrable_sq_sub_eval_pi (p := p) (fun _ => 0) i
  set E := ∫ x, (∑ j, x j ^ 2)⁻¹ ∂P with hE
  have hp2 : (0 : ℝ) < (p : ℝ) - 2 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hexp : ∫ x, ∑ i, (jamesStein x i - 0) ^ 2 ∂P =
      p - 2 * ((p : ℝ) - 2) + ((p : ℝ) - 2) ^ 2 * E := by
    have hae : (fun x : Fin p → ℝ => ∑ i, (jamesStein x i - 0) ^ 2) =ᵐ[P]
        fun x => (∑ j, x j ^ 2) - 2 * ((p : ℝ) - 2) + ((p : ℝ) - 2) ^ 2 * (∑ j, x j ^ 2)⁻¹ := by
      filter_upwards [ae_sum_sq_pos (by omega) (fun _ : Fin p => (0 : ℝ))] with x hx
      simp only [jamesStein, sub_zero, mul_pow]
      rw [← Finset.mul_sum]
      field_simp
      ring
    rw [integral_congr_ae hae]
    have hA : Integrable (fun x : Fin p → ℝ => (∑ j, x j ^ 2) - 2 * ((p : ℝ) - 2)) P :=
      hSi.sub (integrable_const _)
    rw [integral_add hA (h.1.const_mul _), integral_sub hSi (integrable_const _),
      integral_const_mul, hS]
    simp only [P, hE]
    rw [integral_const]
    simp only [integral_const_mul]
    simp
  have h2 := h.2
  rw [hexp] at h2
  have : ((p : ℝ) - 2) * E = 1 := by
    have h3 : 2 * ((p : ℝ) - 2) ^ 2 * E = 2 * ((p : ℝ) - 2) := by linarith
    have h4 : 2 * ((p : ℝ) - 2) * (((p : ℝ) - 2) * E - 1) = 0 := by linarith
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exact absurd h5 (by positivity)
    · linarith
  field_simp
  linarith

/-- **The James–Stein shrinkage factor estimates `1 / V` without bias.** If `z ~ N(0, V I_p)`
with `V > 0` and `p ≥ 3`, then `E[(p - 2) / ‖z‖²] = 1 / V`. In the normal–normal model
`μᵢ ~ N(0, A)`, `zᵢ | μᵢ ~ N(μᵢ, 1)`, the marginal law of `z` is `N(0, V I_p)` with `V = A + 1`
and the Bayes rule is `(1 - 1/V) zᵢ`; substituting this unbiased estimate for `1 / V` gives the
James–Stein rule. This is Efron and Morris's empirical Bayes reading of James–Stein, as stated in
B. Efron, *Tweedie's formula and selection bias*, J. Amer. Statist. Assoc. 106 (2011), equations
(3.7)–(3.9). -/
theorem integral_jamesStein_factor_pi_gaussianReal {p : ℕ} (hp : 3 ≤ p) {V : NNReal}
    (hV : V ≠ 0) :
    ∫ x, ((p : ℝ) - 2) / ∑ j, x j ^ 2 ∂(Measure.pi fun _ : Fin p => gaussianReal 0 V) =
      1 / (V : ℝ) := by
  have hVpos : 0 < (V : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hV)
  set c : ℝ := Real.sqrt V
  have hc2 : c ^ 2 = V := Real.sq_sqrt hVpos.le
  have hmap1 : (gaussianReal 0 1).map (c * ·) = gaussianReal 0 V := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    ext
    simp [hc2]
  have hmap : (Measure.pi fun _ : Fin p => gaussianReal 0 1).map (fun x i => c * x i) =
      Measure.pi fun _ : Fin p => gaussianReal 0 V := by
    rw [Measure.pi_map_pi (fun _ => (measurable_const_mul c).aemeasurable)]
    simp only [hmap1]
  have hmeas : Measurable fun (x : Fin p → ℝ) (i : Fin p) => c * x i := by fun_prop
  have hFm : Measurable fun x : Fin p → ℝ => ((p : ℝ) - 2) / ∑ j, x j ^ 2 :=
    measurable_const.div (by fun_prop)
  rw [← hmap, integral_map hmeas.aemeasurable hFm.aestronglyMeasurable]
  have hpt : ∀ x : Fin p → ℝ, ((p : ℝ) - 2) / ∑ j, (c * x j) ^ 2 =
      ((p : ℝ) - 2) / V * (∑ j, x j ^ 2)⁻¹ := by
    intro x
    simp only [mul_pow, hc2, ← Finset.mul_sum]
    by_cases hx : ∑ j, x j ^ 2 = 0
    · simp [hx]
    · field_simp
  simp_rw [hpt]
  rw [integral_const_mul, integral_inv_sum_sq_pi_gaussianReal_zero hp]
  have hp2 : (0 : ℝ) < (p : ℝ) - 2 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  field_simp

/-! ### Shrinkage towards the grand mean -/

private lemma integrableOn_ball_reciprocal {p : ℕ} (hp : 3 ≤ p) :
    IntegrableOn (fun x : Fin p → ℝ => (∑ j, x j ^ 2)⁻¹) (Metric.ball 0 1) volume := by
  have hm : Measurable (fun x : Fin p → ℝ => (∑ j, x j ^ 2)⁻¹) := by fun_prop
  refine integrableOn_ball_of_norm_le_rpow
    (by simpa using (show 1 ≤ p by omega)) (C := 1) (α := 2) ?_ ?_
    hm.aestronglyMeasurable
  · simpa using (show (2 : ℝ) < p by exact_mod_cast (show 2 < p by omega))
  · apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr
      (Finset.sum_nonneg fun i _ => sq_nonneg (x i))), one_mul,
      Real.rpow_neg (norm_nonneg _), Real.rpow_two]
    by_cases hx : x = 0
    · simp [hx]
    · exact inv_anti₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))
        (norm_sq_le_sum_sq (by omega) x)

/-- A bound on `E‖X‖⁻²` for `X ~ N(θ, I_p)` that does not depend on `θ`. -/
private lemma integral_reciprocal_le {p : ℕ} (hp : 3 ≤ p) (θ : Fin p → ℝ) :
    ∫ x, (∑ j, x j ^ 2)⁻¹ ∂(Measure.pi fun j => gaussianReal (θ j) 1) ≤
      (∫ x in Metric.ball (0 : Fin p → ℝ) 1, (∑ j, x j ^ 2)⁻¹) + 1 := by
  set P := Measure.pi fun j => gaussianReal (θ j) 1
  have hf0 : ∀ x : Fin p → ℝ, 0 ≤ (∑ j, x j ^ 2)⁻¹ :=
    fun x => inv_nonneg.mpr (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hi := integrable_reciprocal hp θ
  rw [← integral_add_compl (measurableSet_ball (x := (0 : Fin p → ℝ)) (ε := 1)) hi]
  refine add_le_add ?_ ?_
  · exact integral_mono_measure (Measure.restrict_mono le_rfl (pi_gaussian_le_volume θ))
      (Filter.Eventually.of_forall hf0) (integrableOn_ball_reciprocal hp)
  · calc ∫ x in (Metric.ball (0 : Fin p → ℝ) 1)ᶜ, (∑ j, x j ^ 2)⁻¹ ∂P
        ≤ ∫ x in (Metric.ball (0 : Fin p → ℝ) 1)ᶜ, (1 : ℝ) ∂P := by
          refine setIntegral_mono_on hi.integrableOn (integrable_const _).integrableOn
            measurableSet_ball.compl fun x hx => ?_
          have hx' : 1 ≤ ‖x‖ := by simpa [Metric.mem_ball, dist_zero_right] using hx
          have hs : 1 ≤ ∑ j, x j ^ 2 := by nlinarith [norm_sq_le_sum_sq (by omega) x]
          exact (inv_le_one₀ (by linarith)).mpr hs
      _ ≤ 1 := by
          rw [setIntegral_const, smul_eq_mul, mul_one]
          exact measureReal_le_one

private lemma map_pi_sub_const {p : ℕ} (θ : Fin p → ℝ) (t : ℝ) :
    (Measure.pi fun j => gaussianReal (θ j) 1).map (fun x j => x j - t) =
      Measure.pi fun j => gaussianReal (θ j - t) 1 := by
  rw [Measure.pi_map_pi (f := fun _ y => y - t) (fun _ => (measurable_sub_const t).aemeasurable)]
  simp only [gaussianReal_map_sub_const]

private lemma integrable_reciprocal_sub {p : ℕ} (hp : 3 ≤ p) (θ : Fin p → ℝ) (t : ℝ) :
    Integrable (fun x : Fin p → ℝ => (∑ j, (x j - t) ^ 2)⁻¹)
      (Measure.pi fun j => gaussianReal (θ j) 1) := by
  have h := integrable_reciprocal hp (fun j => θ j - t)
  rw [← map_pi_sub_const θ t] at h
  have hf : Measurable fun (x : Fin p → ℝ) (j : Fin p) => x j - t :=
    Measurable.of_eval fun j => by fun_prop
  have hg : Measurable fun y : Fin p → ℝ => (∑ j, y j ^ 2)⁻¹ := by fun_prop
  simpa [Function.comp_def] using
    (integrable_map_measure hg.aestronglyMeasurable hf.aemeasurable).mp h

private lemma integral_reciprocal_sub_le {p : ℕ} (hp : 3 ≤ p) (θ : Fin p → ℝ) (t : ℝ) :
    ∫ x, (∑ j, (x j - t) ^ 2)⁻¹ ∂(Measure.pi fun j => gaussianReal (θ j) 1) ≤
      (∫ x in Metric.ball (0 : Fin p → ℝ) 1, (∑ j, x j ^ 2)⁻¹) + 1 := by
  have h := integral_reciprocal_le hp (fun j => θ j - t)
  have hf : Measurable fun (x : Fin p → ℝ) (j : Fin p) => x j - t :=
    Measurable.of_eval fun j => by fun_prop
  have hg : Measurable fun y : Fin p → ℝ => (∑ j, y j ^ 2)⁻¹ := by fun_prop
  rw [← map_pi_sub_const θ t, integral_map hf.aemeasurable hg.aestronglyMeasurable] at h
  exact h

/-- `∑ⱼ (xⱼ - c)² = S + N (x̄ - c)²` with `S = ∑ⱼ xⱼ² - (∑ⱼ xⱼ)² / N`. -/
private lemma sum_sq_sub_eq {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (c : ℝ) :
    ∑ j, (x j - c) ^ 2 =
      (∑ j, x j ^ 2 - (∑ j, x j) ^ 2 / N) + N * ((∑ j, x j) / N - c) ^ 2 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

private lemma grandMeanS_eq {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) :
    ∑ j, (x j - (∑ k, x k) / N) ^ 2 = ∑ j, x j ^ 2 - (∑ j, x j) ^ 2 / N := by
  rw [sum_sq_sub_eq hN x]
  simp

private lemma grandMeanS_nonneg {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) :
    0 ≤ ∑ j, x j ^ 2 - (∑ j, x j) ^ 2 / N := by
  rw [← grandMeanS_eq hN]
  exact Finset.sum_nonneg fun j _ => sq_nonneg _

/-- `1 / S ≤ (N + 1) / ∑ⱼ (xⱼ - xₖ)²`, for every `x` (both sides use `a / 0 = 0`). -/
private lemma inv_grandMeanS_le {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (k : Fin N) :
    (∑ j, x j ^ 2 - (∑ j, x j) ^ 2 / N)⁻¹ ≤ (N + 1) * (∑ j, (x j - x k) ^ 2)⁻¹ := by
  set S := ∑ j, x j ^ 2 - (∑ j, x j) ^ 2 / N
  set T := ∑ j, (x j - x k) ^ 2
  have hS0 : 0 ≤ S := grandMeanS_nonneg hN x
  have hT : T = S + N * ((∑ j, x j) / N - x k) ^ 2 := sum_sq_sub_eq hN x (x k)
  have hk : (x k - (∑ j, x j) / N) ^ 2 ≤ S := by
    change _ ≤ ∑ j, x j ^ 2 - (∑ j, x j) ^ 2 / N
    rw [← grandMeanS_eq hN]
    exact Finset.single_le_sum (f := fun j => (x j - (∑ k, x k) / N) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ k)
  have hTle : T ≤ (N + 1) * S := by
    rw [hT, show ((∑ j, x j) / N - x k) ^ 2 = (x k - (∑ j, x j) / N) ^ 2 by ring]
    nlinarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N]
  have hST : S ≤ T := by
    rw [hT]; nlinarith [sq_nonneg ((∑ j, x j) / N - x k), show (0 : ℝ) ≤ N from Nat.cast_nonneg N]
  rcases hS0.eq_or_lt with h | h
  · rw [← h, inv_zero]
    exact mul_nonneg (by positivity) (inv_nonneg.mpr (hS0.trans hST))
  · have hTpos : 0 < T := h.trans_le hST
    rw [← div_eq_mul_inv, le_div_iff₀ hTpos, inv_mul_le_iff₀ h]
    linarith

/-- For `N ≥ 4` and `X ~ N(θ, I_N)`, `1 / S` is integrable, `S = ∑ⱼ (Xⱼ - X̄)²`. -/
private lemma integrable_inv_grandMeanS {N : ℕ} (hN : 4 ≤ N) (θ : Fin N → ℝ) :
    Integrable (fun x : Fin N → ℝ => (∑ j, x j ^ 2 - (∑ j, x j) ^ 2 / N)⁻¹)
      (Measure.pi fun j => gaussianReal (θ j) 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  set P := Measure.pi fun j => gaussianReal (θ j) 1
  set i : Fin (n + 1) := Fin.last n
  set ν := Measure.pi fun j : Fin n => gaussianReal (θ (i.succAbove j)) 1
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hs : MeasurePreserving e.symm ((gaussianReal (θ i) 1).prod ν) P :=
    (measurePreserving_piFinSuccAbove (fun j => gaussianReal (θ j) 1) i).symm
  set C : ℝ := (∫ x in Metric.ball (0 : Fin n → ℝ) 1, (∑ j, x j ^ 2)⁻¹) + 1
  let G : ℝ × (Fin n → ℝ) → ℝ := fun z => ((n + 1 : ℕ) + 1 : ℝ) * (∑ j, (z.2 j - z.1) ^ 2)⁻¹
  have hGm : Measurable G := by fun_prop
  have hG : Integrable G ((gaussianReal (θ i) 1).prod ν) := by
    refine (integrable_prod_iff hGm.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · exact Filter.Eventually.of_forall fun t =>
        (integrable_reciprocal_sub (by omega) (fun j => θ (i.succAbove j)) t).const_mul _
    · refine (integrable_const (((n + 1 : ℕ) + 1 : ℝ) * C)).mono' ?_
        (Filter.Eventually.of_forall fun t => ?_)
      · exact ((hGm.norm.stronglyMeasurable).integral_prod_right' (ν := ν)).aestronglyMeasurable
      · have hnn : ∀ y : Fin n → ℝ, 0 ≤ G (t, y) := fun y =>
          mul_nonneg (by positivity) (inv_nonneg.mpr (Finset.sum_nonneg fun j _ => sq_nonneg _))
        rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
        simp only [Real.norm_of_nonneg (hnn _), G]
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left
          (integral_reciprocal_sub_le (by omega) (fun j => θ (i.succAbove j)) t) (by positivity)
  have hF : Integrable (fun x : Fin (n + 1) → ℝ => ((n + 1 : ℕ) + 1 : ℝ) *
      (∑ j, (x j - x i) ^ 2)⁻¹) P := by
    refine (hs.integrable_comp_emb e.symm.measurableEmbedding).mp ?_
    refine hG.congr (Filter.Eventually.of_forall fun z => ?_)
    have he : e.symm z = Fin.insertNth i z.1 z.2 := rfl
    simp only [G, Function.comp_apply, he]
    rw [Fin.sum_univ_succAbove _ i]
    simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  refine hF.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (grandMeanS_nonneg (by omega) x))]
  exact inv_grandMeanS_le (by omega) x i

private lemma ae_ne_of_ne {N : ℕ} (θ : Fin N → ℝ) {j k : Fin N} (hjk : j ≠ k) :
    ∀ᵐ x ∂(Measure.pi fun l => gaussianReal (θ l) 1), x j ≠ x k := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := j.pos; omega⟩
  set ν := Measure.pi fun l : Fin n => gaussianReal (θ (j.succAbove l)) 1
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j
  have hs : MeasurePreserving e.symm ((gaussianReal (θ j) 1).prod ν)
      (Measure.pi fun l => gaussianReal (θ l) 1) :=
    (measurePreserving_piFinSuccAbove (fun l => gaussianReal (θ l) 1) j).symm
  obtain ⟨k', hk'⟩ := Fin.exists_succAbove_eq hjk.symm
  have hmeas : MeasurableSet {x : Fin (n + 1) → ℝ | x j = x k} :=
    measurableSet_eq_fun (measurable_pi_apply j) (measurable_pi_apply k)
  rw [ae_iff]
  simp only [ne_eq, not_not]
  rw [← hs.measure_preimage hmeas.nullMeasurableSet]
  have hpre : e.symm ⁻¹' {x | x j = x k} = {z : ℝ × (Fin n → ℝ) | z.1 = z.2 k'} := by
    ext z
    have he : e.symm z = Fin.insertNth j z.1 z.2 := rfl
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, he, ← hk', Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove]
  have hm2 : MeasurableSet {z : ℝ × (Fin n → ℝ) | z.1 = z.2 k'} :=
    measurableSet_eq_fun measurable_fst (by fun_prop)
  rw [hpre, Measure.prod_apply_symm hm2]
  have := nullSingletonClass_gaussianReal (μ := θ j) (v := 1) one_ne_zero
  have h0 : ∀ y : Fin n → ℝ,
      (gaussianReal (θ j) 1) ((fun t => (t, y)) ⁻¹' {z : ℝ × (Fin n → ℝ) | z.1 = z.2 k'}) = 0 :=
    fun y => by
      have : (fun t => (t, y)) ⁻¹' {z : ℝ × (Fin n → ℝ) | z.1 = z.2 k'} = {y k'} := by
        ext; simp
      rw [this]
      exact measure_singleton _
  simp only [h0, lintegral_zero]

private lemma sum_update_id {N : ℕ} (x : Fin N → ℝ) (i : Fin N) (t : ℝ) :
    ∑ l, Function.update x i t l = t + ∑ l ∈ Finset.univ.erase i, x l := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
  congr 1
  exact Finset.sum_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]

private lemma sum_update_sq' {N : ℕ} (x : Fin N → ℝ) (i : Fin N) (t : ℝ) :
    ∑ l, Function.update x i t l ^ 2 = t ^ 2 + ∑ l ∈ Finset.univ.erase i, x l ^ 2 := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
  congr 1
  exact Finset.sum_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]

private lemma grandMeanS_pos_of_ne {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) {j k : Fin N}
    (hjk : x j ≠ x k) : 0 < ∑ l, x l ^ 2 - (∑ l, x l) ^ 2 / N := by
  rw [← grandMeanS_eq hN]
  set m := (∑ l, x l) / N
  have hne : j ≠ k := fun h => hjk (h ▸ rfl)
  have h2 : (x j - m) ^ 2 + (x k - m) ^ 2 ≤ ∑ l, (x l - m) ^ 2 := by
    have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {j, k})
      (f := fun l => (x l - m) ^ 2) (fun _ _ _ => sq_nonneg _)
    rwa [Finset.sum_pair hne] at this
  have hd : x j - m - (x k - m) ≠ 0 := by
    intro h; apply hjk; linarith
  nlinarith [sq_nonneg (x j - m + (x k - m)), sq_pos_of_ne_zero hd]

/-- The correction `g_i(x) = -a (x_i - x̄) / S` of the grand-mean James–Stein estimator. -/
private noncomputable def gmG {N : ℕ} (a : ℝ) (i : Fin N) (x : Fin N → ℝ) : ℝ :=
  -a * (x i - (∑ l, x l) / N) / (∑ l, x l ^ 2 - (∑ l, x l) ^ 2 / N)

/-- Its partial derivative in the `i`-th coordinate. -/
private noncomputable def gmDG {N : ℕ} (a : ℝ) (i : Fin N) (x : Fin N → ℝ) : ℝ :=
  -a * ((1 - 1 / (N : ℝ)) * (∑ l, x l ^ 2 - (∑ l, x l) ^ 2 / N) -
    (x i - (∑ l, x l) / N) * (2 * x i - 2 * (∑ l, x l) / N)) /
    (∑ l, x l ^ 2 - (∑ l, x l) ^ 2 / N) ^ 2

private lemma hasDerivAt_gmG {N : ℕ} (hN : 0 < N) (a : ℝ) (x : Fin N → ℝ) (i : Fin N) (t : ℝ)
    (hden : (∑ l, Function.update x i t l ^ 2 - (∑ l, Function.update x i t l) ^ 2 / N) ≠ 0) :
    HasDerivAt (fun s => gmG a i (Function.update x i s)) (gmDG a i (Function.update x i t)) t := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  set R1 := ∑ l ∈ Finset.univ.erase i, x l
  set R2 := ∑ l ∈ Finset.univ.erase i, x l ^ 2
  have hfun : (fun s => gmG a i (Function.update x i s)) =
      fun s => -a * (s - (s + R1) / N) / ((s ^ 2 + R2) - (s + R1) ^ 2 / N) := by
    funext s
    simp only [gmG, Function.update_self, sum_update_id, sum_update_sq']
    rfl
  rw [sum_update_id, sum_update_sq'] at hden
  have h1 : HasDerivAt (fun s : ℝ => -a * (s - (s + R1) / N)) (-a * (1 - 1 / N)) t := by
    have := (((hasDerivAt_id t).sub (((hasDerivAt_id t).add_const R1).div_const (N : ℝ)))).const_mul
      (-a)
    simpa using this
  have h2 : HasDerivAt (fun s : ℝ => (s ^ 2 + R2) - (s + R1) ^ 2 / N)
      (2 * t - 2 * (t + R1) / N) t := by
    have hA := (hasDerivAt_pow 2 t).add_const R2
    have hB := (((hasDerivAt_id' t).add_const R1).pow 2).div_const (N : ℝ)
    exact (hA.sub hB).congr_deriv (by simp)
  rw [hfun]
  convert h1.div h2 hden using 1
  simp only [gmDG, Function.update_self, sum_update_id, sum_update_sq']
  field_simp
  ring

private lemma gm_sum_sq_dev {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) :
    ∑ i, (x i - (∑ l, x l) / N) ^ 2 = ∑ l, x l ^ 2 - (∑ l, x l) ^ 2 / N :=
  grandMeanS_eq hN x

private lemma sq_dev_le {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (i : Fin N) :
    (x i - (∑ l, x l) / N) ^ 2 ≤ ∑ l, x l ^ 2 - (∑ l, x l) ^ 2 / N := by
  rw [← grandMeanS_eq hN]
  exact Finset.single_le_sum (f := fun j => (x j - (∑ k, x k) / N) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)

private lemma gmG_sq_le {N : ℕ} (hN : 0 < N) (a : ℝ) (x : Fin N → ℝ) (i : Fin N) :
    gmG a i x ^ 2 ≤ a ^ 2 * (∑ l, x l ^ 2 - (∑ l, x l) ^ 2 / N)⁻¹ := by
  set D := ∑ l, x l ^ 2 - (∑ l, x l) ^ 2 / N
  have hD := grandMeanS_nonneg hN x
  have hd := sq_dev_le hN x i
  rcases hD.eq_or_lt with h | h
  · simp [gmG, D, ← h]
  · simp only [gmG]
    change (-a * (x i - (∑ l, x l) / N) / D) ^ 2 ≤ a ^ 2 * D⁻¹
    rw [div_pow, mul_pow, neg_sq, div_le_iff₀ (by positivity)]
    calc a ^ 2 * (x i - (∑ l, x l) / N) ^ 2 ≤ a ^ 2 * D := by gcongr
      _ = a ^ 2 * D⁻¹ * D ^ 2 := by field_simp

private lemma abs_gmDG_le {N : ℕ} (hN : 0 < N) (a : ℝ) (x : Fin N → ℝ) (i : Fin N) :
    |gmDG a i x| ≤ 3 * |a| * (∑ l, x l ^ 2 - (∑ l, x l) ^ 2 / N)⁻¹ := by
  set D := ∑ l, x l ^ 2 - (∑ l, x l) ^ 2 / N
  have hD := grandMeanS_nonneg hN x
  have hd := sq_dev_le hN x i
  have hN1 : (0 : ℝ) ≤ 1 - 1 / N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    rw [sub_nonneg, div_le_one (by linarith)]; exact this
  have hN2 : 1 - 1 / (N : ℝ) ≤ 1 := by
    have : (0 : ℝ) ≤ 1 / N := by positivity
    linarith
  rcases hD.eq_or_lt with h | h
  · simp [gmDG, D, ← h]
  · simp only [gmDG]
    change |-a * ((1 - 1 / (N : ℝ)) * D - (x i - (∑ l, x l) / N) * (2 * x i - 2 * (∑ l, x l) / N))
      / D ^ 2| ≤ 3 * |a| * D⁻¹
    have hq : (x i - (∑ l, x l) / N) * (2 * x i - 2 * (∑ l, x l) / N) =
        2 * (x i - (∑ l, x l) / N) ^ 2 := by ring
    rw [hq, abs_div, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < D ^ 2),
      div_le_iff₀ (by positivity)]
    have hb : |(1 - 1 / (N : ℝ)) * D - 2 * (x i - (∑ l, x l) / N) ^ 2| ≤ 3 * D := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x i - (∑ l, x l) / N)]
    calc |a| * |(1 - 1 / (N : ℝ)) * D - 2 * (x i - (∑ l, x l) / N) ^ 2| ≤ |a| * (3 * D) := by
          gcongr
      _ = 3 * |a| * D⁻¹ * D ^ 2 := by field_simp

private lemma sum_gm_correction {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ)
    (hD : (∑ l, x l ^ 2 - (∑ l, x l) ^ 2 / N) ≠ 0) :
    ∑ i, (gmG ((N : ℝ) - 3) i x ^ 2 + 2 * gmDG ((N : ℝ) - 3) i x) =
      -((N : ℝ) - 3) ^ 2 * (∑ l, x l ^ 2 - (∑ l, x l) ^ 2 / N)⁻¹ := by
  set D := ∑ l, x l ^ 2 - (∑ l, x l) ^ 2 / N
  set a : ℝ := (N : ℝ) - 3
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpt : ∀ i, gmG a i x ^ 2 + 2 * gmDG a i x =
      ((a ^ 2 + 4 * a) * (x i - (∑ l, x l) / N) ^ 2 - 2 * a * (1 - 1 / N) * D) / D ^ 2 := by
    intro i
    simp only [gmG, gmDG]
    change (-a * (x i - (∑ l, x l) / N) / D) ^ 2 + 2 * (-a * ((1 - 1 / (N : ℝ)) * D -
      (x i - (∑ l, x l) / N) * (2 * x i - 2 * (∑ l, x l) / N)) / D ^ 2) = _
    field_simp
    ring
  rw [Finset.sum_congr rfl fun i _ => hpt i, ← Finset.sum_div, Finset.sum_sub_distrib,
    ← Finset.mul_sum, gm_sum_sq_dev hN, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  change ((a ^ 2 + 4 * a) * D - N * (2 * a * (1 - 1 / N) * D)) / D ^ 2 = -a ^ 2 * D⁻¹
  field_simp
  simp only [a]
  ring

/-- The risk of the grand-mean James–Stein estimator with unit noise variance:
`N - (N - 3)² E[1 / S]`. -/
private lemma integral_jamesSteinGrandMean_one_risk {N : ℕ} (hN : 4 ≤ N) (θ : Fin N → ℝ) :
    Integrable (fun x => ∑ i, (jamesSteinGrandMean 1 x i - θ i) ^ 2)
      (Measure.pi fun j => gaussianReal (θ j) 1) ∧
    ∫ x, ∑ i, (jamesSteinGrandMean 1 x i - θ i) ^ 2 ∂(Measure.pi fun j => gaussianReal (θ j) 1) =
      N - ((N : ℝ) - 3) ^ 2 * ∫ x : Fin N → ℝ, (∑ l, x l ^ 2 - (∑ l, x l) ^ 2 / (N : ℝ))⁻¹
        ∂(Measure.pi fun j => gaussianReal (θ j) 1) := by
  have hN0 : 0 < N := by omega
  set P := Measure.pi fun j => gaussianReal (θ j) 1
  set a : ℝ := (N : ℝ) - 3
  have hr := integrable_inv_grandMeanS hN θ
  have hgm (i : Fin N) : Measurable (gmG (N := N) a i) := by
    unfold gmG
    exact (measurable_const.mul ((measurable_pi_apply i).sub
      ((Finset.measurable_sum _ fun l _ => measurable_pi_apply l).div_const _))).div
      ((Finset.measurable_sum _ fun l _ => (measurable_pi_apply l).pow_const 2).sub
        (((Finset.measurable_sum _ fun l _ => measurable_pi_apply l).pow_const 2).div_const _))
  have hdgm (i : Fin N) : Measurable (gmDG (N := N) a i) := by
    unfold gmDG
    have hA : Measurable fun x : Fin N → ℝ => ∑ l, x l :=
      Finset.measurable_sum _ fun l _ => measurable_pi_apply l
    have hB : Measurable fun x : Fin N → ℝ => ∑ l, x l ^ 2 :=
      Finset.measurable_sum _ fun l _ => (measurable_pi_apply l).pow_const 2
    have hD : Measurable fun x : Fin N → ℝ => ∑ l, x l ^ 2 - (∑ l, x l) ^ 2 / N :=
      hB.sub ((hA.pow_const 2).div_const _)
    exact (measurable_const.mul ((measurable_const.mul hD).sub
      (((measurable_pi_apply i).sub (hA.div_const _)).mul
        ((measurable_const.mul (measurable_pi_apply i)).sub
          ((measurable_const.mul hA).div_const _))))).div (hD.pow_const 2)
  have hd (i : Fin N) : ∀ᵐ x ∂P, ∀ t, HasDerivAt (fun s => gmG a i (Function.update x i s))
      (gmDG a i (Function.update x i t)) t := by
    obtain ⟨j, hji, _⟩ := Fin.exists_ne_and_ne_of_two_lt i i (by omega)
    obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
    filter_upwards [ae_ne_of_ne θ hkj.symm] with x hx
    intro t
    refine hasDerivAt_gmG hN0 a x i t (grandMeanS_pos_of_ne hN0 _ (j := j) (k := k) ?_).ne'
    rwa [Function.update_of_ne hji, Function.update_of_ne hki]
  have hdi (i : Fin N) : Integrable (gmDG a i) P :=
    (hr.const_mul (3 * |a|)).mono' (hdgm i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact abs_gmDG_le hN0 a x i)
  have hg2 (i : Fin N) : MemLp (gmG a i) 2 P := by
    apply (memLp_two_iff_integrable_sq (hgm i).aestronglyMeasurable).mpr
    apply (hr.const_mul (a ^ 2)).mono' ((hgm i).pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact gmG_sq_le hN0 a x i
  have hae : ∀ᵐ x ∂P, (∑ l, x l ^ 2 - (∑ l, x l) ^ 2 / (N : ℝ)) ≠ 0 := by
    obtain ⟨j, k, hjk⟩ : ∃ j k : Fin N, j ≠ k := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
    filter_upwards [ae_ne_of_ne θ hjk] with x hx
    exact (grandMeanS_pos_of_ne hN0 x hx).ne'
  have hpt : ∀ x : Fin N → ℝ, ∑ i, (jamesSteinGrandMean 1 x i - θ i) ^ 2 =
      ∑ i, (x i + gmG a i x - θ i) ^ 2 := fun x =>
    Finset.sum_congr rfl fun i _ => by
      simp only [jamesSteinGrandMean, gmG, grandMeanS_eq hN0, a]
      ring
  refine ⟨?_, ?_⟩
  · refine (integrable_finsetSum Finset.univ fun i _ =>
      ((memLp_sub_eval_pi θ i).add (hg2 i)).integrable_sq).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [hpt x, Pi.add_apply]
    exact Finset.sum_congr rfl fun i _ => by ring
  calc
    _ = ∫ x, ∑ i, (x i + gmG a i x - θ i) ^ 2 ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = N + ∫ x, ∑ i, (gmG a i x ^ 2 + 2 * gmDG a i x) ∂P :=
      integral_sum_sq_add_sub_pi_gaussianReal θ hd hdi hg2
    _ = N + ∫ x, -a ^ 2 * (∑ l, x l ^ 2 - (∑ l, x l) ^ 2 / N)⁻¹ ∂P := by
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      exact sum_gm_correction hN0 x hx
    _ = _ := by rw [integral_const_mul]; ring

private lemma measurable_jamesSteinGrandMean {N : ℕ} (σ2 : ℝ) (i : Fin N) :
    Measurable fun x : Fin N → ℝ => jamesSteinGrandMean σ2 x i := by
  unfold jamesSteinGrandMean
  have hA : Measurable fun x : Fin N → ℝ => ∑ l, x l :=
    Finset.measurable_sum _ fun l _ => measurable_pi_apply l
  have hS : Measurable fun x : Fin N → ℝ => ∑ j, (x j - (∑ k, x k) / N) ^ 2 :=
    Finset.measurable_sum _ fun j _ => ((measurable_pi_apply j).sub (hA.div_const _)).pow_const 2
  exact (hA.div_const _).add ((measurable_const.sub (measurable_const.div hS)).mul
    ((measurable_pi_apply i).sub (hA.div_const _)))

private lemma jamesSteinGrandMean_smul {N : ℕ} {c : ℝ} (hc : c ≠ 0) (x : Fin N → ℝ) (i : Fin N) :
    jamesSteinGrandMean (c ^ 2) (fun j => c * x j) i = c * jamesSteinGrandMean 1 x i := by
  unfold jamesSteinGrandMean
  set S := ∑ j, (x j - (∑ k, x k) / N) ^ 2
  have hA : ∑ k, c * x k = c * ∑ k, x k := (Finset.mul_sum _ _ _).symm
  have hS' : ∑ j, (c * x j - (∑ k, c * x k) / N) ^ 2 = c ^ 2 * S := by
    simp only [S, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hA]; ring
  rw [hS', hA]
  by_cases hS : S = 0
  · simp [hS]
  · field_simp

/-- **James–Stein shrinkage towards the grand mean dominates the MLE.** Let `N ≥ 4`, `σ² > 0` and
`X ~ N(θ, σ² I_N)`. Then for every `θ` the loss `∑ᵢ (θ̂ᵢ - θᵢ)²` of the estimator
`θ̂ = jamesSteinGrandMean σ² X` is integrable and its mean is `< N σ²` (B. Efron, *Empirical Bayes:
Concepts and Methods*, 2021 manuscript, Theorem 1, equations (3.1)–(3.5), which credits James and
Stein 1961). -/
theorem integral_jamesSteinGrandMean_risk_lt {N : ℕ} (hN : 4 ≤ N) {σ2 : NNReal}
    (hσ : σ2 ≠ 0) (θ : Fin N → ℝ) :
    Integrable (fun x => ∑ i, (jamesSteinGrandMean σ2 x i - θ i) ^ 2)
        (Measure.pi fun j => gaussianReal (θ j) σ2) ∧
      ∫ x, ∑ i, (jamesSteinGrandMean σ2 x i - θ i) ^ 2
        ∂(Measure.pi fun j => gaussianReal (θ j) σ2) < N * σ2 := by
  have hN0 : 0 < N := by omega
  have h1 : ∀ θ' : Fin N → ℝ, ∫ x, ∑ i, (jamesSteinGrandMean 1 x i - θ' i) ^ 2
      ∂(Measure.pi fun j => gaussianReal (θ' j) 1) < N := by
    intro θ'
    rw [(integral_jamesSteinGrandMean_one_risk hN θ').2]
    set P := Measure.pi fun j => gaussianReal (θ' j) 1
    have hr := integrable_inv_grandMeanS hN θ'
    obtain ⟨j, k, hjk⟩ : ∃ j k : Fin N, j ≠ k := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
    have hpos : 0 < ∫ x : Fin N → ℝ, (∑ l, x l ^ 2 - (∑ l, x l) ^ 2 / (N : ℝ))⁻¹ ∂P := by
      refine (integral_pos_iff_support_of_nonneg
        (fun x => inv_nonneg.mpr (grandMeanS_nonneg hN0 x)) hr).2 ?_
      have hnull : P (Function.support fun x : Fin N → ℝ =>
          (∑ l, x l ^ 2 - (∑ l, x l) ^ 2 / (N : ℝ))⁻¹)ᶜ = 0 := by
        refine measure_mono_null (fun x hx => ?_) (ae_iff.mp (ae_ne_of_ne θ' hjk))
        simp only [Set.mem_compl_iff, Function.mem_support, not_not, inv_eq_zero] at hx
        simp only [Set.mem_ofPred_eq, ne_eq, not_not]
        by_contra h
        exact (grandMeanS_pos_of_ne hN0 x h).ne' hx
      have hmeas : MeasurableSet (Function.support fun x : Fin N → ℝ =>
          (∑ l, x l ^ 2 - (∑ l, x l) ^ 2 / (N : ℝ))⁻¹) :=
        measurableSet_support (by fun_prop)
      rw [prob_compl_eq_zero_iff hmeas] at hnull
      rw [hnull]
      exact one_pos
    have ha : 0 < ((N : ℝ) - 3) ^ 2 := by
      have : (4 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith
    nlinarith
  set c : ℝ := Real.sqrt σ2
  have hσpos : (0 : ℝ) < σ2 := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hσ)
  have hc : 0 < c := Real.sqrt_pos.mpr hσpos
  have hc2 : c ^ 2 = σ2 := Real.sq_sqrt (NNReal.coe_nonneg _)
  have hmap1 : ∀ j, (gaussianReal (θ j / c) 1).map (c * ·) = gaussianReal (θ j) σ2 := fun j => by
    rw [gaussianReal_map_const_mul, mul_div_cancel₀ _ hc.ne']
    congr 1
    ext
    simp [hc2]
  have hmap : (Measure.pi fun j => gaussianReal (θ j / c) 1).map (fun x j => c * x j) =
      Measure.pi fun j => gaussianReal (θ j) σ2 := by
    rw [Measure.pi_map_pi (f := fun _ y => c * y) (fun _ => (measurable_const_mul c).aemeasurable)]
    simp only [hmap1]
  have hF : Measurable fun x : Fin N → ℝ => ∑ i, (jamesSteinGrandMean σ2 x i - θ i) ^ 2 :=
    Finset.measurable_sum _ fun i _ =>
      ((measurable_jamesSteinGrandMean _ i).sub measurable_const).pow_const 2
  have hsc : Measurable fun (x : Fin N → ℝ) (j : Fin N) => c * x j :=
    Measurable.of_eval fun j => by fun_prop
  have hpt : ∀ x : Fin N → ℝ, ∑ i, (jamesSteinGrandMean σ2 (fun j => c * x j) i - θ i) ^ 2 =
      σ2 * ∑ i, (jamesSteinGrandMean 1 x i - θ i / c) ^ 2 := fun x => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hc2, jamesSteinGrandMean_smul hc.ne']
    field_simp
  rw [← hmap]
  refine ⟨?_, ?_⟩
  · refine (integrable_map_measure hF.aestronglyMeasurable hsc.aemeasurable).mpr ?_
    refine (((integral_jamesSteinGrandMean_one_risk hN fun j => θ j / c).1).const_mul
      (σ2 : ℝ)).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Function.comp_apply, hpt x]
  rw [integral_map hsc.aemeasurable hF.aestronglyMeasurable]
  simp_rw [hpt]
  rw [integral_const_mul]
  calc (σ2 : ℝ) * ∫ x, ∑ i, (jamesSteinGrandMean 1 x i - θ i / c) ^ 2
        ∂(Measure.pi fun j => gaussianReal (θ j / c) 1) < σ2 * N :=
        mul_lt_mul_of_pos_left (h1 fun j => θ j / c) hσpos
    _ = N * σ2 := mul_comm _ _

end ProbabilityTheory
