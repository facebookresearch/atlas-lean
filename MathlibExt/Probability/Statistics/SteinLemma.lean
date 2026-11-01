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

## References

* C. Stein, *Inadmissibility of the usual estimator for the mean of a multivariate normal
  distribution*, Proc. Third Berkeley Symp. Math. Statist. Probab., Vol. 1, Univ. California
  Press (1956), 197–206.
* W. James and C. Stein, *Estimation with quadratic loss*, Proc. Fourth Berkeley Symp. Math.
  Statist. Probab., Vol. 1, Univ. California Press (1961), 361–379.
* C. M. Stein, *Estimation of the mean of a multivariate normal distribution*, Ann. Statist. 9
  (1981), 1135–1151.
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

end ProbabilityTheory
