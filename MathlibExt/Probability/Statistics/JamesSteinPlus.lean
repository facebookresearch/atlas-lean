/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.SteinLemma
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral

/-!
# Risk of the positive-part James–Stein estimator

For independent unit-variance Gaussian coordinates in dimension at least three, truncating the
James–Stein shrinkage factor at zero can only decrease the expected squared loss.
The proof pairs opposite values of each coordinate while holding the other coordinates fixed.
-/

open MeasureTheory

namespace ProbabilityTheory

namespace integral_jamesSteinPlus_risk_le

/-- Of the points `t` and `-t`, the Gaussian density favors the one on the mean's side. -/
private lemma density_sign (μ t : ℝ) :
    0 ≤ t * μ * (gaussianPDFReal μ 1 t - gaussianPDFReal μ 1 (-t)) := by
  have h (s : ℝ) (hs : 0 ≤ s * μ) : gaussianPDFReal μ 1 (-s) ≤ gaussianPDFReal μ 1 s := by
    unfold gaussianPDFReal
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    norm_num
    nlinarith only [hs]
  rcases le_total 0 (t * μ) with ht | ht
  · exact mul_nonneg ht (sub_nonneg.mpr (h t ht))
  · apply mul_nonneg_of_nonpos_of_nonpos ht
    simpa using sub_nonpos.mpr (h (-t) (by simpa using ht))

/-- Compare the Gaussian risks of an even shrinkage factor and its positive part on a line. -/
private lemma slice_risk_le (μ : ℝ) (a : ℝ → ℝ) (ha : ∀ t, a (-t) = a t)
    (hplus : Integrable (fun t => (max 0 (a t) * t - μ) ^ 2) (gaussianReal μ 1))
    (hjs : Integrable (fun t => (a t * t - μ) ^ 2) (gaussianReal μ 1)) :
    ∫ t, (max 0 (a t) * t - μ) ^ 2 ∂gaussianReal μ 1 ≤
      ∫ t, (a t * t - μ) ^ 2 ∂gaussianReal μ 1 := by
  let φ := gaussianPDFReal μ 1
  let L (b : ℝ → ℝ) (t : ℝ) := φ t * (b t * t - μ) ^ 2
  let b (t : ℝ) := max 0 (a t)
  have weighted (c : ℝ → ℝ) (hc : Integrable (fun t => (c t * t - μ) ^ 2) (gaussianReal μ 1)) :
      Integrable (L c) := by
    rw [gaussianReal_of_var_ne_zero μ one_ne_zero] at hc
    simpa only [L, φ, toReal_gaussianPDF, smul_eq_mul] using
      (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF μ 1)
        (ae_of_all _ fun _ => gaussianPDF_lt_top)).mp hc
  have paired (c : ℝ → ℝ) (hc : Integrable (L c)) :
      ∫ t, L c t + L c (-t) = (∫ t, L c t) + ∫ t, L c t := by
    rw [integral_add hc hc.comp_neg, integral_neg_eq_self]
  have hpoint (t : ℝ) : L b t + L b (-t) ≤ L a t + L a (-t) := by
    simp only [L, b, ha]
    rcases le_total 0 (a t) with ht | ht
    · simp [max_eq_right ht]
    · rw [max_eq_left ht]
      have hsq := mul_nonneg (sq_nonneg (a t * t))
        (add_nonneg (gaussianPDFReal_nonneg μ 1 t) (gaussianPDFReal_nonneg μ 1 (-t)))
      have hcross := mul_nonpos_of_nonpos_of_nonneg ht (density_sign μ t)
      dsimp [φ]
      linarith only [hsq, hcross]
  have hb := weighted b hplus
  have ha' := weighted a hjs
  have hi := integral_mono (hb.add hb.comp_neg) (ha'.add ha'.comp_neg) hpoint
  change (∫ t, L b t + L b (-t)) ≤ ∫ t, L a t + L a (-t) at hi
  rw [paired b hb, paired a ha'] at hi
  simp only [integral_gaussianReal_eq_integral_smul one_ne_zero, smul_eq_mul]
  change (∫ t, L b t) ≤ ∫ t, L a t
  linarith

private lemma integrable_losses {p : ℕ} (hp : 3 ≤ p) (θ : Fin p → ℝ) (i : Fin p) :
    Integrable (fun x => (jamesSteinPlus x i - θ i) ^ 2)
        (Measure.pi fun j => gaussianReal (θ j) 1) ∧
      Integrable (fun x => (jamesStein x i - θ i) ^ 2)
        (Measure.pi fun j => gaussianReal (θ j) 1) := by
  let P := Measure.pi fun j => gaussianReal (θ j) 1
  let S (x : Fin p → ℝ) := ∑ j, x j ^ 2
  have hx : MemLp (fun x : Fin p → ℝ => x i) 2 P :=
    (memLp_id_gaussianReal (μ := θ i) (v := 1) 2).comp_measurePreserving
      (measurePreserving_eval (fun j => gaussianReal (θ j) 1) i)
  have hm : Measurable (fun x => x i / S x) := by dsimp [S]; fun_prop
  have hg : MemLp (fun x => x i / S x) 2 P := by
    apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
    apply (integrable_and_integral_jamesStein_risk hp θ).1.mono'
      (hm.pow_const 2).aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _), div_pow]
    change x i ^ 2 / S x ^ 2 ≤ (S x)⁻¹
    have hi : x i ^ 2 ≤ S x :=
      Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    calc
      _ ≤ S x / S x ^ 2 := by gcongr
      _ = _ := by by_cases h : S x = 0 <;> simp [h, sq, div_eq_mul_inv]
  have hjs : MemLp (fun x => jamesStein x i) 2 P := by
    apply (hx.sub (hg.const_mul ((p : ℝ) - 2))).ae_eq
    filter_upwards with x
    dsimp [jamesStein, S]
    ring
  have hplus : MemLp (fun x => jamesSteinPlus x i) 2 P := by
    apply hjs.of_le (by unfold jamesSteinPlus; fun_prop)
    filter_upwards with x
    unfold jamesSteinPlus jamesStein
    rcases le_total 0 (1 - ((p : ℝ) - 2) / ∑ j, x j ^ 2) with h | h
    · simp [max_eq_right h]
    · rw [max_eq_left h, zero_mul, norm_zero]
      exact norm_nonneg _
  exact ⟨(hplus.sub (memLp_const (θ i))).integrable_sq,
    (hjs.sub (memLp_const (θ i))).integrable_sq⟩

private lemma coordinate_risk_le {p : ℕ} (hp : 3 ≤ p) (θ : Fin p → ℝ) (i : Fin p) :
    ∫ x, (jamesSteinPlus x i - θ i) ^ 2 ∂(Measure.pi fun j => gaussianReal (θ j) 1) ≤
      ∫ x, (jamesStein x i - θ i) ^ 2 ∂(Measure.pi fun j => gaussianReal (θ j) 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  have he := (measurePreserving_piFinSuccAbove (fun j => gaussianReal (θ j) 1) i).symm
  obtain ⟨hplus, hjs⟩ := integrable_losses hp θ i
  have hL := he.integrable_comp_of_integrable hplus
  have hR := he.integrable_comp_of_integrable hjs
  simp only [Function.comp_def] at hL hR
  rw [← he.integral_comp' (g := fun x => (jamesSteinPlus x i - θ i) ^ 2),
    ← he.integral_comp' (g := fun x => (jamesStein x i - θ i) ^ 2),
    integral_prod_symm _ hL, integral_prod_symm _ hR]
  apply integral_mono_ae hL.integral_prod_right hR.integral_prod_right
  filter_upwards [hL.prod_left_ae, hR.prod_left_ae] with y hLy hRy
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  let a (t : ℝ) := 1 - ((n + 1 : ℕ) - 2 : ℝ) / (t ^ 2 + ∑ j, y j ^ 2)
  have heq (t : ℝ) : e.symm (t, y) = Fin.insertNth (α := fun _ => ℝ) i t y := rfl
  have hsum (t : ℝ) : ∑ j, (e.symm (t, y) j) ^ 2 = t ^ 2 + ∑ j, y j ^ 2 := by
    rw [Fin.sum_univ_succAbove _ i]
    simp [heq]
  have hcoord (t : ℝ) : e.symm (t, y) i = t := by simp [heq]
  simp only [jamesSteinPlus, jamesStein, hsum, hcoord] at hLy hRy ⊢
  exact slice_risk_le (θ i) a (by simp [a]) hLy hRy

end integral_jamesSteinPlus_risk_le

/-- **The positive-part James–Stein estimator is at least as good as James–Stein.** For `p ≥ 3`
and `X ~ N(θ, I_p)`, the loss `‖δ⁺(X) - θ‖²` is integrable and `E ‖δ⁺(X) - θ‖² ≤ E ‖δ(X) - θ‖²`
for every `θ` (Johnstone, *Gaussian
estimation: Sequence and wavelet models*, draft of 16 September 2019, equation (2.65) and
Exercise 2.12, where it is stated that `δ⁺` has "even better MSE" than `δ`). -/
public theorem integral_jamesSteinPlus_risk_le {p : ℕ} (hp : 3 ≤ p) (θ : Fin p → ℝ) :
    Integrable (fun x => ∑ i, (jamesSteinPlus x i - θ i) ^ 2)
        (Measure.pi fun j => gaussianReal (θ j) 1) ∧
    ∫ x, ∑ i, (jamesSteinPlus x i - θ i) ^ 2 ∂(Measure.pi fun j => gaussianReal (θ j) 1) ≤
      ∫ x, ∑ i, (jamesStein x i - θ i) ^ 2 ∂(Measure.pi fun j => gaussianReal (θ j) 1) := by
  have hi := integral_jamesSteinPlus_risk_le.integrable_losses hp θ
  refine ⟨integrable_finsetSum _ (fun i _ => (hi i).1), ?_⟩
  rw [integral_finsetSum _ (fun i _ => (hi i).1), integral_finsetSum _ (fun i _ => (hi i).2)]
  exact Finset.sum_le_sum fun i _ => integral_jamesSteinPlus_risk_le.coordinate_risk_le hp θ i

end ProbabilityTheory
