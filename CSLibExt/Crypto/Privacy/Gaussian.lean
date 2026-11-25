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
import MathlibExt.MeasureTheory.Measure.PiWithDensity

/-!
# The Gaussian mechanism

`gaussianMechanism_differentiallyPrivate` proves approximate differential privacy for a
vector-valued query by calibrating independent Gaussian noise to its Euclidean sensitivity.
For neighboring means `a` and `b`, the proof bounds the density at mean `a` by the sum of
`exp ε` times the density at mean `b` and `δ` times a third Gaussian density. The integral
of the third density over any event is at most one.
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

end Cslib.Crypto.Privacy
