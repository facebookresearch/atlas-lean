/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Neyman–Pearson lemma (dominated two-simple-hypothesis form)

A likelihood-ratio threshold test is most powerful among tests of no greater size.

Provenance: J. Neyman and E. S. Pearson, *On the problem of the most efficient tests
of statistical hypotheses*, Philosophical Transactions of the Royal Society of London
A 231 (1933), 289–337, DOI `10.1098/rsta.1933.0009`.

The public theorem below is deliberately stronger than the usual textbook statement:
neither the normalization hypotheses (`∫ p = 1`, `∫ q = 1`) nor a fixed tie value on
the set `{q = k * p}` is needed. The mathematical kernel is the pointwise inequality
`(φ⋆ - φ) * (q - k * p) ≥ 0`, followed by integration and the assumed `p`-size bound.
-/

namespace MathlibExt.Probability.Statistics.NeymanPearson

@[expose] public section

open MeasureTheory

/-- A `[0,1]`-valued measurable test times a nonnegative integrable density is
integrable. -/
private lemma integrable_val_mul_density {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {w d : Ω → ℝ} (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (hd_meas : Measurable d) (hd_nonneg : ∀ x, 0 ≤ d x)
    (hd_int : Integrable d μ) : Integrable (fun x => w x * d x) μ := by
  refine hd_int.mono' (hw.mul hd_meas).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hn : ‖w x‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨le_trans (by norm_num) (hw0 x), hw1 x⟩
  calc ‖w x * d x‖ = ‖w x‖ * ‖d x‖ := norm_mul _ _
    _ ≤ 1 * ‖d x‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    _ = d x := by rw [one_mul, Real.norm_of_nonneg (hd_nonneg x)]

/--
**Neyman–Pearson lemma.** Let $\mu$ be a measure on a measurable space $\Omega$, and let
$p, q : \Omega \to \mathbb{R}$ be measurable, nonnegative and $\mu$-integrable. Let $k \ge 0$ be a
real number and let $\varphi^\star : \Omega \to [0, 1]$ be measurable with $\varphi^\star(x) = 1$
whenever $q(x) > k\,p(x)$ and $\varphi^\star(x) = 0$ whenever $q(x) < k\,p(x)$. Then every
measurable test $\varphi : \Omega \to [0, 1]$ satisfying
$\int \varphi\, p \, d\mu \le \int \varphi^\star p \, d\mu$ also satisfies
$\int \varphi\, q \, d\mu \le \int \varphi^\star q \, d\mu$.

No normalization of $p$ or $q$ and no condition on $\varphi^\star$ on the set where $q = k\,p$ are
assumed.

Source: J. Neyman and E. S. Pearson, "On the problem of the most efficient tests of
statistical hypotheses", Phil. Trans. R. Soc. Lond. A 231 (1933), 289–337,
DOI `10.1098/rsta.1933.0009`.
-/
theorem neyman_pearson_dominated_two_simple
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p q : Ω → ℝ}
    (hp_meas : Measurable p) (hq_meas : Measurable q)
    (hp_nonneg : ∀ x, 0 ≤ p x) (hq_nonneg : ∀ x, 0 ≤ q x)
    (hp_int : Integrable p μ) (hq_int : Integrable q μ)
    (k : ℝ) (hk : 0 ≤ k)
    (φstar : Ω → Set.Icc (0 : ℝ) 1) (hφstar_meas : Measurable φstar)
    (hφstar_gt : ∀ x, k * p x < q x → (φstar x).val = 1)
    (hφstar_lt : ∀ x, q x < k * p x → (φstar x).val = 0) :
    ∀ (φ : Ω → Set.Icc (0 : ℝ) 1), Measurable φ →
      (∫ x, (φ x).val * p x ∂μ ≤ ∫ x, (φstar x).val * p x ∂μ) →
      (∫ x, (φ x).val * q x ∂μ ≤ ∫ x, (φstar x).val * q x ∂μ) := by
  intro φ hφ_meas hsize
  have hstar : Measurable (fun x => (φstar x).val) := hφstar_meas.subtype_val
  have hval : Measurable (fun x => (φ x).val) := hφ_meas.subtype_val
  have hs0 : ∀ x, 0 ≤ (φstar x).val := fun x => (φstar x).property.1
  have hs1 : ∀ x, (φstar x).val ≤ 1 := fun x => (φstar x).property.2
  have hv0 : ∀ x, 0 ≤ (φ x).val := fun x => (φ x).property.1
  have hv1 : ∀ x, (φ x).val ≤ 1 := fun x => (φ x).property.2
  have hint_star_p : Integrable (fun x => (φstar x).val * p x) μ :=
    integrable_val_mul_density hstar hs0 hs1 hp_meas hp_nonneg hp_int
  have hint_val_p : Integrable (fun x => (φ x).val * p x) μ :=
    integrable_val_mul_density hval hv0 hv1 hp_meas hp_nonneg hp_int
  have hint_star_q : Integrable (fun x => (φstar x).val * q x) μ :=
    integrable_val_mul_density hstar hs0 hs1 hq_meas hq_nonneg hq_int
  have hint_val_q : Integrable (fun x => (φ x).val * q x) μ :=
    integrable_val_mul_density hval hv0 hv1 hq_meas hq_nonneg hq_int
  have hint_diff_p : Integrable (fun x => ((φstar x).val - (φ x).val) * p x) μ := by
    apply (hint_star_p.sub hint_val_p).congr
    exact Filter.Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring
  have hint_diff_q : Integrable (fun x => ((φstar x).val - (φ x).val) * q x) μ := by
    apply (hint_star_q.sub hint_val_q).congr
    exact Filter.Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring
  have hkey : ∀ x, 0 ≤ ((φstar x).val - (φ x).val) * (q x - k * p x) := by
    intro x
    rcases lt_trichotomy (q x) (k * p x) with hlt | heq | hgt
    · have h0 : (φstar x).val = 0 := hφstar_lt x hlt
      have hφ0 : (0 : ℝ) ≤ (φ x).val := (φ x).property.1
      have hd : (φstar x).val - (φ x).val ≤ 0 := by
        rw [h0]
        exact sub_nonpos.mpr hφ0
      have hqk : q x - k * p x ≤ 0 := sub_nonpos.mpr (le_of_lt hlt)
      exact mul_nonneg_of_nonpos_of_nonpos hd hqk
    · rw [sub_eq_zero.mpr heq, mul_zero]
    · have h1 : (φstar x).val = 1 := hφstar_gt x hgt
      have hφ1 : (φ x).val ≤ 1 := (φ x).property.2
      have hd : (0 : ℝ) ≤ (φstar x).val - (φ x).val := by
        rw [h1]
        exact sub_nonneg.mpr hφ1
      have hqk : (0 : ℝ) ≤ q x - k * p x := sub_nonneg.mpr (le_of_lt hgt)
      exact mul_nonneg hd hqk
  have hint_kdiff_p :
      Integrable (fun x => k * (((φstar x).val - (φ x).val) * p x)) μ :=
    hint_diff_p.const_mul k
  have hG : (∫ x, ((φstar x).val - (φ x).val) * (q x - k * p x) ∂μ)
      = (∫ x, ((φstar x).val - (φ x).val) * q x ∂μ)
        - k * (∫ x, ((φstar x).val - (φ x).val) * p x ∂μ) := by
    have hcongr : (∫ x, ((φstar x).val - (φ x).val) * (q x - k * p x) ∂μ)
        = (∫ x, (((φstar x).val - (φ x).val) * q x
          - k * (((φstar x).val - (φ x).val) * p x)) ∂μ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by ring
    rw [hcongr, integral_sub hint_diff_q hint_kdiff_p, integral_const_mul]
  have hFp : (∫ x, ((φstar x).val - (φ x).val) * p x ∂μ)
      = (∫ x, (φstar x).val * p x ∂μ) - (∫ x, (φ x).val * p x ∂μ) := by
    have hcongr : (∫ x, ((φstar x).val - (φ x).val) * p x ∂μ)
        = (∫ x, ((φstar x).val * p x - (φ x).val * p x) ∂μ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by ring
    rw [hcongr, integral_sub hint_star_p hint_val_p]
  have hFq : (∫ x, ((φstar x).val - (φ x).val) * q x ∂μ)
      = (∫ x, (φstar x).val * q x ∂μ) - (∫ x, (φ x).val * q x ∂μ) := by
    have hcongr : (∫ x, ((φstar x).val - (φ x).val) * q x ∂μ)
        = (∫ x, ((φstar x).val * q x - (φ x).val * q x) ∂μ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by ring
    rw [hcongr, integral_sub hint_star_q hint_val_q]
  have hG_nonneg : (0 : ℝ) ≤ (∫ x, ((φstar x).val - (φ x).val) * q x ∂μ)
      - k * (∫ x, ((φstar x).val - (φ x).val) * p x ∂μ) := by
    rw [← hG]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall hkey)
  have hFp_nonneg : (0 : ℝ) ≤ (∫ x, ((φstar x).val - (φ x).val) * p x ∂μ) := by
    rw [hFp]
    exact sub_nonneg.mpr hsize
  have hFq_nonneg : (0 : ℝ) ≤ (∫ x, ((φstar x).val - (φ x).val) * q x ∂μ) :=
    le_trans (mul_nonneg hk hFp_nonneg) (le_of_sub_nonneg hG_nonneg)
  have hfinal : (0 : ℝ) ≤ (∫ x, (φstar x).val * q x ∂μ)
      - (∫ x, (φ x).val * q x ∂μ) := by
    rw [← hFq]
    exact hFq_nonneg
  exact le_of_sub_nonneg hfinal

end

end MathlibExt.Probability.Statistics.NeymanPearson
