/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Privacy.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import MathlibExt.MeasureTheory.Measure.PiWithDensity
import MathlibExt.Probability.Distributions.GaussianTail

/-!
# The Gaussian mechanism

`gaussianMechanism_differentiallyPrivate` proves approximate differential privacy for a
vector-valued query by calibrating independent Gaussian noise to its Euclidean sensitivity.
For neighboring means `a` and `b`, the proof bounds the density at mean `a` by the sum of
`exp ε` times the density at mean `b` and `δ` times a third Gaussian density. The integral
of the third density over any event is at most one.

`gaussian_calibration_tail_le` proves a standardized tail estimate behind the calibration of the
same mechanism (Dwork and Roth (2014), proof of Theorem A.1): for `0 < ε < 1`, `0 < δ`, `0 < c`
and `0 < r`, under `2 * Real.log ((5 / 4) / δ) < c ^ 2` and `r ≤ ε / c`, where `r` is the
standardized shift (sensitivity divided by the noise scale), the standard Gaussian mass above
the privacy-loss threshold `ε / r - r / 2` is at most `δ`, including the trivial case `δ ≥ 1`.
The proof of Theorem A.1 asks for the bound `δ / 2` on this one-sided tail and assumes
sensitivity at least `1`; this estimate gives the bound `δ` with no lower bound on the
sensitivity. The constant `5 / 4` is the source constant `1.25` inside the calibration
hypothesis `2 * Real.log ((5 / 4) / δ) < c ^ 2`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Cslib.Crypto.Privacy

variable {d : ℕ}

private noncomputable def sqDist (a b : Fin d → ℝ) : ℝ := ∑ i, (a i - b i) ^ 2

private noncomputable def density (v : ℝ≥0) (m z : Fin d → ℝ) : ℝ≥0∞ :=
  ∏ i, gaussianPDF (m i) v (z i)

private lemma measurable_density (v : ℝ≥0) (m : Fin d → ℝ) : Measurable (density v m) :=
  Finset.measurable_prod _ fun i _ ↦ (measurable_gaussianPDF _ _).comp (measurable_pi_apply i)

private lemma pi_gaussian_apply {v : ℝ≥0} (hv : v ≠ 0) (m : Fin d → ℝ)
    {S : Set (Fin d → ℝ)} (hS : MeasurableSet S) :
    (Measure.pi fun i ↦ gaussianReal (m i) v) S = ∫⁻ z in S, density v m z := by
  have : ∀ i, SigmaFinite (volume.withDensity (gaussianPDF (m i) v)) := fun i ↦ by
    rw [← gaussianReal_of_var_ne_zero _ hv]
    infer_instance
  simp_rw [gaussianReal_of_var_ne_zero _ hv]
  rw [Measure.pi_withDensity (μ := fun _ ↦ volume) fun i ↦ measurable_gaussianPDF _ _,
    ← volume_pi, withDensity_apply _ hS]
  rfl

private lemma density_eq (v : ℝ≥0) (m z : Fin d → ℝ) :
    density v m z = ENNReal.ofReal
      ((Real.sqrt (2 * Real.pi * v))⁻¹ ^ d * Real.exp (-sqDist z m / (2 * v))) := by
  simp only [density, gaussianPDF]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ gaussianPDFReal_nonneg (m i) v (z i))]
  simp [gaussianPDFReal, Finset.prod_mul_distrib, ← Real.exp_sum, sqDist,
    ← Finset.sum_div, ← Finset.sum_neg_distrib]

-- Compare the two kernels to a third one, centered at a + k(a - b). Completing the
-- square cancels the dependence on the observation in the coefficient of the third kernel.
private lemma kernel_le {k ε v : ℝ} (hk : 0 < k) (a b z : Fin d → ℝ) :
    let t := fun i ↦ a i + k * (a i - b i)
    let K := fun m ↦ Real.exp (-sqDist z m / (2 * v))
    K a ≤ Real.exp ε * K b +
      Real.exp (k * (k + 1) * sqDist a b / (2 * v) - k * ε) / (1 + k) * K t := by
  intro t K
  let u := ε + (sqDist z a - sqDist z b) / (2 * v)
  have hsq : sqDist z t = (1 + k) * sqDist z a - k * sqDist z b +
      k * (k + 1) * sqDist a b := by
    simp only [sqDist, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by dsimp [t]; ring
  have hconv : 1 ≤ Real.exp u + Real.exp (-k * u) / (1 + k) := by
    rw [← sub_le_iff_le_add', le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left (Real.add_one_le_exp u) hk.le,
      Real.add_one_le_exp (-k * u), Real.exp_pos u]
  calc
    K a = K a * 1 := (mul_one _).symm
    _ ≤ K a * (Real.exp u + Real.exp (-k * u) / (1 + k)) :=
      mul_le_mul_of_nonneg_left hconv (Real.exp_pos _).le
    _ = _ := by
      dsimp only [K]
      simp only [mul_add, ← mul_div_assoc, div_mul_eq_mul_div, ← Real.exp_add, hsq, u]
      congr 1
      · congr 1; ring
      · congr 2; ring

-- With k = c² / ε and δ < 1, the calibration gives k > 2/5. This absorbs the
-- factor exp(ε/2) in the coefficient left over from completing the square.
private lemma calibration {c ε δ k : ℝ} (hε₁ : ε < 1)
    (hδ : 0 < δ) (hδ₁ : δ < 1) (hc : 2 * Real.log ((5 / 4) / δ) < c ^ 2)
    (hk : 0 < k) (hke : k * ε = c ^ 2) :
    Real.exp ((ε - c ^ 2) / 2) / (1 + k) ≤ δ := by
  have hlog := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)
  have hratio : (5 / 4 : ℝ) ≤ (5 / 4) / δ := (le_div_iff₀ hδ).2 (by linarith)
  have hlog' := Real.log_le_log (by norm_num) hratio
  norm_num at hlog
  have hk' : 2 / 5 < k := by nlinarith [mul_lt_mul_of_pos_left hε₁ hk]
  have he : Real.exp (ε / 2) ≤ (5 / 4) * (1 + k) := by
    have hsq : Real.exp (ε / 2) ^ 2 < 3 := calc
      _ = Real.exp ε := by rw [sq, ← Real.exp_add]; congr 1; ring
      _ < 3 := (Real.exp_lt_exp.mpr hε₁).trans Real.exp_one_lt_three
    nlinarith [sq_nonneg (Real.exp (ε / 2) - 7 / 4)]
  have hcal : (5 / 4) / δ ≤ Real.exp (c ^ 2 / 2) := by
    rw [← Real.exp_log (div_pos (by norm_num : (0 : ℝ) < 5 / 4) hδ), Real.exp_le_exp]
    linarith
  rw [sub_div, Real.exp_sub, div_le_iff₀ (by positivity), div_le_iff₀ (Real.exp_pos _)]
  have := (div_le_iff₀ hδ).mp hcal
  calc Real.exp (ε / 2) ≤ 5 / 4 * (1 + k) := he
    _ ≤ (Real.exp (c ^ 2 / 2) * δ) * (1 + k) := by gcongr
    _ = _ := by ring

private lemma gaussian_event_le {ε δ k : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hk : 0 < k) (hδ : 0 < δ) (a b : Fin d → ℝ)
    (hcoef : Real.exp (k * (k + 1) * sqDist a b / (2 * v) - k * ε) / (1 + k) ≤ δ)
    {S : Set (Fin d → ℝ)} (hS : MeasurableSet S) :
    (Measure.pi fun i ↦ gaussianReal (a i) v) S ≤
      ENNReal.ofReal (Real.exp ε) * (Measure.pi fun i ↦ gaussianReal (b i) v) S +
      ENNReal.ofReal δ := by
  let t := fun i ↦ a i + k * (a i - b i)
  let K := fun m z : Fin d → ℝ ↦ Real.exp (-sqDist z m / (2 * v))
  let C := (Real.sqrt (2 * Real.pi * v))⁻¹ ^ d
  have hpt (z : Fin d → ℝ) : density v a z ≤ ENNReal.ofReal (Real.exp ε) * density v b z +
      ENNReal.ofReal δ * density v t z := by
    have h := kernel_le (v := (v : ℝ)) (ε := ε) hk a b z
    have hK : K a z ≤ Real.exp ε * K b z + δ * K t z :=
      h.trans (add_le_add_right (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le) _)
    simp only [density_eq, ← ENNReal.ofReal_mul (Real.exp_pos ε).le,
      ← ENNReal.ofReal_mul hδ.le]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    change C * K a z ≤ Real.exp ε * (C * K b z) + δ * (C * K t z)
    calc C * K a z ≤ C * (Real.exp ε * K b z + δ * K t z) :=
            mul_le_mul_of_nonneg_left hK (by dsimp [C]; positivity)
      _ = _ := by ring
  rw [pi_gaussian_apply hv a hS, pi_gaussian_apply hv b hS]
  calc ∫⁻ z in S, density v a z
    _ ≤ ∫⁻ z in S, ENNReal.ofReal (Real.exp ε) * density v b z +
        ENNReal.ofReal δ * density v t z := lintegral_mono hpt
    _ = ENNReal.ofReal (Real.exp ε) * (∫⁻ z in S, density v b z) +
        ENNReal.ofReal δ * (Measure.pi fun i ↦ gaussianReal (t i) v) S := by
      rw [lintegral_add_left ((measurable_density v b).const_mul _),
        lintegral_const_mul _ (measurable_density v b),
        lintegral_const_mul _ (measurable_density v t), pi_gaussian_apply hv t hS]
    _ ≤ _ := by
      grw [prob_le_one (μ := Measure.pi fun i ↦ gaussianReal (t i) v) (s := S)]
      rw [mul_one]

variable {X : Type*} {Adj : X → X → Prop}

/-- **The Gaussian mechanism.** Let `f : X → (Fin d → ℝ)` have `ℓ₂`-sensitivity at most `Δ₂ ≥ 0`,
i.e. `√(∑ i, (f x i - f y i) ^ 2) ≤ Δ₂` whenever `Adj x y`. Let `ε ∈ (0, 1)`, `δ > 0`, `c > 0`
with `c ^ 2 > 2 ln (1.25 / δ)`, and `σ ≥ c Δ₂ / ε`. Adding independent `N(0, σ ^ 2)` noise to each
coordinate is `(ε, δ)`-differentially private (Dwork and Roth, *The Algorithmic Foundations of
Differential Privacy*, 2014, Theorem A.1). -/
theorem gaussianMechanism_differentiallyPrivate {d : ℕ} {f : X → Fin d → ℝ}
    {Δ₂ ε δ c σ : ℝ} (hΔ₂ : 0 ≤ Δ₂) (hε₀ : 0 < ε) (hε₁ : ε < 1) (hδ : 0 < δ) (hc₀ : 0 < c)
    (hc : 2 * Real.log ((5 / 4) / δ) < c ^ 2) (hσ : c * Δ₂ / ε ≤ σ)
    (hf : ∀ ⦃x y⦄, Adj x y → Real.sqrt (∑ i, (f x i - f y i) ^ 2) ≤ Δ₂) :
    DifferentiallyPrivate Adj
      (fun x ↦ Measure.pi fun i ↦ gaussianReal (f x i) (σ ^ 2).toNNReal) ε (ENNReal.ofReal δ) := by
  intro x y hxy S hS
  dsimp only
  by_cases hδ₁ : 1 ≤ δ
  · have hd : 1 ≤ ENNReal.ofReal δ := by simpa using ENNReal.ofReal_le_ofReal hδ₁
    exact prob_le_one.trans (le_add_left hd)
  have hs := hf hxy
  have hσ' := (div_le_iff₀ hε₀).mp hσ
  have hdist : 0 ≤ sqDist (f x) (f y) := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  by_cases hz : σ = 0
  · have hΔ : Δ₂ = 0 := by
      rw [hz, zero_mul] at hσ'
      exact le_antisymm (nonpos_of_mul_nonpos_right hσ' hc₀) hΔ₂
    rw [hΔ] at hs
    have hsum := (Real.sqrt_eq_zero hdist).mp (le_antisymm hs (Real.sqrt_nonneg _))
    have heq : f x = f y := by
      funext i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg (f x j - f y j))).mp
        hsum i (Finset.mem_univ i)
      nlinarith
    rw [heq]
    apply le_add_right
    have he : 1 ≤ ENNReal.ofReal (Real.exp ε) := by
      simpa using ENNReal.ofReal_le_ofReal (Real.one_le_exp_iff.mpr hε₀.le)
    simpa only [one_mul] using mul_le_mul_left he ((Measure.pi fun i ↦
      gaussianReal (f y i) (σ ^ 2).toNNReal) S)
  have hv : (σ ^ 2).toNNReal ≠ 0 := by simpa [Real.toNNReal_eq_zero] using hz
  let k := c ^ 2 / ε
  have hk : 0 < k := div_pos (sq_pos_of_pos hc₀) hε₀
  have hke : k * ε = c ^ 2 := div_mul_cancel₀ _ hε₀.ne'
  refine gaussian_event_le hv hk hδ (f x) (f y) ?_ hS
  rw [Real.coe_toNNReal _ (sq_nonneg _)]
  have hscaled : k * sqDist (f x) (f y) ≤ ε * σ ^ 2 := by
    have hlen : c * Real.sqrt (sqDist (f x) (f y)) ≤ σ * ε :=
      (mul_le_mul_of_nonneg_left hs hc₀.le).trans hσ'
    have hpow := pow_le_pow_left₀ (by positivity) hlen 2
    rw [mul_pow, Real.sq_sqrt hdist, mul_pow] at hpow
    dsimp only [k]
    rw [div_mul_eq_mul_div, div_le_iff₀ hε₀]
    linarith only [hpow]
  refine le_trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr ?_) (by positivity))
    (calibration hε₁ hδ (lt_of_not_ge hδ₁) hc hk hke)
  rw [sub_le_iff_le_add, div_le_iff₀ (by positivity : 0 < 2 * σ ^ 2), ← hke]
  nlinarith [mul_le_mul_of_nonneg_left hscaled (by positivity : 0 ≤ k + 1)]

private lemma prob_Ioi_zero_le :
    gaussianReal 0 1 (Set.Ioi 0) ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
  have h := gaussianReal_Ioi_le_half_exp (u := (0 : ℝ)) le_rfl
  rw [show (-(0 : ℝ) ^ 2 / 2) = 0 by norm_num, Real.exp_zero] at h
  exact h

private lemma exp_half_le : Real.exp (1 / 2 : ℝ) ≤ 2 := by
  have h := Real.exp_bound_div_one_sub_of_interval (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  rwa [show (1 / (1 - 1 / 2 : ℝ)) = 2 by norm_num] at h

private lemma exp_quarter_le : Real.exp (1 / 4 : ℝ) ≤ 4 / 3 := by
  have h := Real.exp_bound_div_one_sub_of_interval (x := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
  rwa [show (1 / (1 - 1 / 4 : ℝ)) = 4 / 3 by norm_num] at h

private lemma log_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 / 5 : ℝ) ≤ Real.log ((5 / 4) / δ) := by
  have h54 : (5 / 4 : ℝ) ≤ (5 / 4) / δ := by
    rw [le_div_iff₀ hδ]
    linarith
  have hlog54 : (1 / 5 : ℝ) ≤ Real.log (5 / 4) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)
    rwa [show (1 - (5 / 4 : ℝ)⁻¹) = 1 / 5 by norm_num] at h
  exact le_trans hlog54 (Real.log_le_log (by norm_num) h54)

private lemma thresh_ge {ε c r : ℝ} (hc₀ : 0 < c) (hr₀ : 0 < r)
    (hr : r ≤ ε / c) : c - ε / (2 * c) ≤ ε / r - r / 2 := by
  have h1 : c ≤ ε / r := by
    rw [le_div_iff₀ hr₀]
    have h2 : r * c ≤ ε := (le_div_iff₀ hc₀).mp hr
    linarith [h2]
  have h3 : r / 2 ≤ ε / (2 * c) := by
    have h4 : r / 2 ≤ (ε / c) / 2 := by
      rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
      exact hr
    rw [div_div, mul_comm c (2 : ℝ)] at h4
    exact h4
  linarith [h1, h3]

private lemma exp_tail_le {ε δ c : ℝ} (hε₁ : ε < 1) (hδ : 0 < δ)
    (hc₀ : 0 < c) (hc : 2 * Real.log ((5 / 4) / δ) < c ^ 2) :
    Real.exp (-(c - ε / (2 * c)) ^ 2 / 2) / 2 ≤ δ := by
  have hc_ne : c ≠ 0 := ne_of_gt hc₀
  have hc2 : c ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < c ^ 2)
  have hsq : (c - ε / (2 * c)) ^ 2 = c ^ 2 - ε + ε ^ 2 / (4 * c ^ 2) := by
    field_simp
    ring
  have hsplit : -(c - ε / (2 * c)) ^ 2 / 2
      = -c ^ 2 / 2 + (ε / 2 - ε ^ 2 / (8 * c ^ 2)) := by
    rw [hsq]
    field_simp
    ring
  have hexp_eq : Real.exp (-(c - ε / (2 * c)) ^ 2 / 2)
      = Real.exp (-c ^ 2 / 2) * Real.exp (ε / 2 - ε ^ 2 / (8 * c ^ 2)) := by
    rw [hsplit, Real.exp_add]
  have hL_pos : (0 : ℝ) < (5 / 4) / δ := div_pos (by norm_num) hδ
  have he1 : Real.exp (-c ^ 2 / 2) ≤ 4 * δ / 5 := by
    have h1 : Real.exp (-c ^ 2 / 2) < Real.exp (-Real.log ((5 / 4) / δ)) := by
      apply Real.exp_lt_exp.mpr
      linarith [hc]
    have h2 : Real.exp (-Real.log ((5 / 4) / δ)) = 4 * δ / 5 := by
      have hδ_ne : δ ≠ 0 := ne_of_gt hδ
      rw [Real.exp_neg, Real.exp_log hL_pos]
      field_simp
    linarith [h1, h2]
  have he2 : Real.exp (ε / 2 - ε ^ 2 / (8 * c ^ 2)) ≤ 2 := by
    have hnn : (0 : ℝ) ≤ ε ^ 2 / (8 * c ^ 2) :=
      div_nonneg (sq_nonneg ε) (by positivity)
    calc Real.exp (ε / 2 - ε ^ 2 / (8 * c ^ 2)) ≤ Real.exp (ε / 2) :=
            Real.exp_le_exp.mpr (by linarith [hnn])
      _ ≤ Real.exp (1 / 2 : ℝ) := Real.exp_le_exp.mpr (by linarith [hε₁])
      _ ≤ 2 := exp_half_le
  rw [hexp_eq]
  have h4δ : (0 : ℝ) ≤ 4 * δ / 5 := by linarith [hδ]
  calc Real.exp (-c ^ 2 / 2) * Real.exp (ε / 2 - ε ^ 2 / (8 * c ^ 2)) / 2
      ≤ (4 * δ / 5) * 2 / 2 := by
        rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
        exact mul_le_mul he1 he2 (Real.exp_nonneg _) h4δ
    _ = 4 * δ / 5 := by ring
    _ ≤ δ := by linarith [hδ]

private lemma phi0_lt : gaussianPDFReal 0 1 0 < 1 / 2 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  rw [gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [show (-(0 : ℝ) ^ 2 / 2) = 0 by norm_num, Real.exp_zero, mul_one]
  have h2 : (2 : ℝ) < Real.sqrt (2 * Real.pi) :=
    calc (2 : ℝ) = Real.sqrt (2 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ < Real.sqrt (2 * Real.pi) :=
          Real.sqrt_lt_sqrt (by norm_num) (by linarith [hpi])
  calc (Real.sqrt (2 * Real.pi))⁻¹ < (2 : ℝ)⁻¹ :=
          (inv_lt_inv₀ (Real.sqrt_pos.mpr (by linarith [hpi])) (by norm_num)).mpr h2
    _ = 1 / 2 := by norm_num

private lemma pdf_le_phi0 {x : ℝ} :
    gaussianPDF 0 1 x ≤ ENNReal.ofReal (gaussianPDFReal 0 1 0) := by
  have h : gaussianPDFReal 0 1 x ≤ gaussianPDFReal 0 1 0 := by
    rw [gaussianPDFReal, gaussianPDFReal]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    rw [show (-(0 : ℝ) ^ 2 / 2) = 0 by norm_num, Real.exp_zero, mul_one]
    have hC : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
    have he : Real.exp (-x ^ 2 / 2) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have hnn : (0 : ℝ) ≤ x ^ 2 / 2 := by positivity
      linarith
    calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)
        ≤ (Real.sqrt (2 * Real.pi))⁻¹ * 1 := mul_le_mul_of_nonneg_left he hC
      _ = (Real.sqrt (2 * Real.pi))⁻¹ := mul_one _
  simp only [gaussianPDF] at h ⊢
  exact ENNReal.ofReal_le_ofReal h

private lemma ioc_le :
    gaussianReal 0 1 (Set.Ioc (-1 / 2) 0) ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
  have h1 : (1 : ℝ≥0) ≠ 0 := by simp
  rw [gaussianReal_apply 0 h1]
  have hle : ∫⁻ x in Set.Ioc (-1 / 2 : ℝ) 0, gaussianPDF 0 1 x ∂volume
      ≤ ∫⁻ x in Set.Ioc (-1 / 2 : ℝ) 0, ENNReal.ofReal (gaussianPDFReal 0 1 0) ∂volume :=
    setLIntegral_mono' measurableSet_Ioc (fun x _ => pdf_le_phi0)
  rw [setLIntegral_const, Real.volume_Ioc] at hle
  have hφ : ENNReal.ofReal (gaussianPDFReal 0 1 0) ≤ ENNReal.ofReal (1 / 2 : ℝ) :=
    ENNReal.ofReal_le_ofReal (le_of_lt phi0_lt)
  rw [show ((0 : ℝ) - -1 / 2) = 1 / 2 by norm_num] at hle
  apply le_trans hle
  calc ENNReal.ofReal (gaussianPDFReal 0 1 0) * ENNReal.ofReal (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hφ zero_le
    _ = ENNReal.ofReal (1 / 4 : ℝ) := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        congr 1
        norm_num

private lemma ioi_neg_half_le :
    gaussianReal 0 1 (Set.Ioi (-1 / 2 : ℝ)) ≤ ENNReal.ofReal (3 / 4 : ℝ) := by
  have hunion : Set.Ioi (0 : ℝ) ∪ Set.Ioc (-1 / 2) 0 = Set.Ioi (-1 / 2 : ℝ) := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Ioc]
    constructor
    · intro h
      rcases h with h | ⟨h1, h2⟩ <;> linarith
    · intro h
      by_cases hx : (0 : ℝ) < x
      · exact Or.inl hx
      · exact Or.inr ⟨h, le_of_not_gt hx⟩
  have hdisj : Disjoint (Set.Ioi (0 : ℝ)) (Set.Ioc (-1 / 2 : ℝ) 0) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [Set.mem_Ioi, Set.mem_Ioc] at hx1 hx2
    linarith
  have h := measure_union (μ := gaussianReal 0 1) hdisj measurableSet_Ioc
  rw [hunion] at h
  rw [h]
  have h34 : ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 4 : ℝ)
      = ENNReal.ofReal (3 / 4 : ℝ) := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    congr 1
    norm_num
  rw [← h34]
  exact add_le_add prob_Ioi_zero_le ioc_le

private lemma delta_gt {δ : ℝ} (hδ : 0 < δ) (hlog : Real.log ((5 / 4) / δ) < 1 / 4) :
    (15 / 16 : ℝ) < δ := by
  have hL_pos : (0 : ℝ) < (5 / 4) / δ := div_pos (by norm_num) hδ
  have hL : (5 / 4 : ℝ) / δ < Real.exp (1 / 4 : ℝ) := by
    have h := Real.exp_lt_exp.mpr hlog
    rwa [Real.exp_log hL_pos] at h
  have hlt : (5 / 4 : ℝ) / δ < 4 / 3 := lt_of_lt_of_le hL exp_quarter_le
  rw [div_lt_iff₀ hδ] at hlt
  linarith [hlt]

private lemma thresh_lo {ε c : ℝ} (hε₁ : ε < 1) (hc₀ : 0 < c)
    (hc_sq : (2 : ℝ) / 5 < c ^ 2) : (-1 / 2 : ℝ) < c - ε / (2 * c) := by
  have hc5 : (1 / 5 : ℝ) < c := by
    rw [← sq_lt_sq₀ (a := (1 / 5 : ℝ)) (b := c) (by norm_num) (le_of_lt hc₀)]
    norm_num
    linarith [hc_sq]
  have hpos : (0 : ℝ) < 2 * c ^ 2 + c - ε := by linarith [hc_sq, hc5, hε₁]
  have heq : c - ε / (2 * c) + 1 / 2 = (2 * c ^ 2 + c - ε) / (2 * c) := by
    have hc_ne : c ≠ 0 := ne_of_gt hc₀
    have h2c : (2 : ℝ) * c ≠ 0 := mul_ne_zero (by norm_num) hc_ne
    field_simp
    ring
  have hq : (0 : ℝ) < (2 * c ^ 2 + c - ε) / (2 * c) :=
    div_pos hpos (by linarith [hc₀])
  linarith [heq, hq]

/-- **Gaussian calibration tail estimate.** Let `0 < ε < 1`, `0 < δ`, `0 < c` and `0 < r`, with
`2 * Real.log ((5 / 4) / δ) < c ^ 2` and `r ≤ ε / c`. Then the standard normal law
`gaussianReal 0 1` gives mass at most `δ` to `(ε / r - r / 2, ∞)`. Here `r` is the standardized
shift (sensitivity divided by the Gaussian noise scale), `c` is the calibration constant and
`ε / r - r / 2` is the standardized privacy-loss threshold. This is a tail estimate behind the
calibration of the Gaussian mechanism in Dwork and Roth, *The Algorithmic Foundations of
Differential Privacy* (2014), proof of Theorem A.1, which asks for the bound `δ / 2` on this
one-sided tail and assumes sensitivity at least `1`; the bound here is `δ`, with no lower bound on
the sensitivity. For `δ ≥ 1` the bound holds because the mass is at most `1`. -/
theorem gaussian_calibration_tail_le {ε δ c r : ℝ} (_hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hδ : 0 < δ) (hc₀ : 0 < c) (hc : 2 * Real.log ((5 / 4) / δ) < c ^ 2) (hr₀ : 0 < r)
    (hr : r ≤ ε / c) :
    gaussianReal 0 1 (Set.Ioi (ε / r - r / 2)) ≤ ENNReal.ofReal δ := by
  by_cases hδ1 : 1 ≤ δ
  · calc gaussianReal 0 1 (Set.Ioi (ε / r - r / 2)) ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal δ := ENNReal.one_le_ofReal.mpr hδ1
  · push Not at hδ1
    have hlog5 : (1 / 5 : ℝ) ≤ Real.log ((5 / 4) / δ) := log_bound hδ hδ1
    have hc_sq : (2 : ℝ) / 5 < c ^ 2 := by linarith [hc, hlog5]
    have hts : c - ε / (2 * c) ≤ ε / r - r / 2 := thresh_ge hc₀ hr₀ hr
    by_cases hs : (0 : ℝ) ≤ c - ε / (2 * c)
    · have h1 : gaussianReal 0 1 (Set.Ioi (ε / r - r / 2))
          ≤ gaussianReal 0 1 (Set.Ioi (c - ε / (2 * c))) :=
        measure_mono (Set.Ioi_subset_Ioi hts)
      have h2 : gaussianReal 0 1 (Set.Ioi (c - ε / (2 * c)))
          ≤ ENNReal.ofReal (Real.exp (-(c - ε / (2 * c)) ^ 2 / 2) / 2) :=
        gaussianReal_Ioi_le_half_exp hs
      have h3 : ENNReal.ofReal (Real.exp (-(c - ε / (2 * c)) ^ 2 / 2) / 2)
          ≤ ENNReal.ofReal δ :=
        ENNReal.ofReal_le_ofReal (exp_tail_le hε₁ hδ hc₀ hc)
      exact le_trans h1 (le_trans h2 h3)
    · push Not at hs
      have hc2 : c ^ 2 < ε / 2 := by
        have hlt : c < ε / (2 * c) := by linarith [hs]
        have hmul := (lt_div_iff₀ (show (0 : ℝ) < 2 * c by linarith [hc₀])).mp hlt
        linarith [hmul]
      have hc2half : c ^ 2 < 1 / 2 := by linarith [hc2, hε₁]
      have hlog4 : Real.log ((5 / 4) / δ) < 1 / 4 := by linarith [hc, hc2half]
      have hδ16 : (15 / 16 : ℝ) < δ := delta_gt hδ hlog4
      have hslo : (-1 / 2 : ℝ) < c - ε / (2 * c) := thresh_lo hε₁ hc₀ hc_sq
      have htlo : (-1 / 2 : ℝ) ≤ ε / r - r / 2 := by linarith [hts, hslo]
      have h1 : gaussianReal 0 1 (Set.Ioi (ε / r - r / 2))
          ≤ gaussianReal 0 1 (Set.Ioi (-1 / 2 : ℝ)) :=
        measure_mono (Set.Ioi_subset_Ioi htlo)
      have h2 : gaussianReal 0 1 (Set.Ioi (-1 / 2 : ℝ)) ≤ ENNReal.ofReal (3 / 4 : ℝ) :=
        ioi_neg_half_le
      have h3 : ENNReal.ofReal (3 / 4 : ℝ) ≤ ENNReal.ofReal δ :=
        ENNReal.ofReal_le_ofReal (by linarith [hδ16])
      exact le_trans h1 (le_trans h2 h3)

end Cslib.Crypto.Privacy
