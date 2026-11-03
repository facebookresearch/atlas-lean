/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Lande's selection gradient for a normally distributed trait

A quantitative trait `z` is normally distributed before selection, `z ~ N(μ, v)` with
phenotypic variance `v > 0`. An individual with phenotype `z` has (absolute) fitness `W z`.
The mean fitness of the population is `w̄(μ) = 𝔼[W z]`, and the directional selection
differential is the shift of the trait mean among the selected parents, weighted by fitness:
`S = 𝔼[W z · z] / w̄ - μ = 𝔼[(z - μ) W z] / w̄` (Lande–Arnold 1983).

Lande (1979) showed that for a normally distributed phenotype the selection gradient
`β = P⁻¹ S` equals the gradient of log mean fitness with respect to the trait mean:
`S = P ∇_μ log w̄`. This file proves the one-trait case `S = v · d/dμ log w̄(μ)`, and the
Lande–Arnold form `β = S / v = 𝔼[W' z] / w̄`, the average slope of relative fitness, via
Stein's lemma.

Fitness is biologically nonnegative; the identities need only a bounded measurable `W` with
nonzero mean fitness (bounded fitness covers stabilizing and Gaussian fitness surfaces). The
mean and variance are those before selection; no inheritance model is involved.

## Main results

* `integral_sub_mul_gaussianReal`: **Stein's lemma** for `N(μ, v)`,
  `𝔼[(z - μ) g z] = v 𝔼[g' z]`, for a differentiable `g` with integrable `g, (z - μ) g, g'`.
* `hasDerivAt_meanFitness`: `d/dμ w̄(μ) = 𝔼[(z - μ) W z] / v`.
* `selectionDifferential_eq_mul_deriv_log`: **Lande's equation** `S = v · d/dμ log w̄(μ)`.
* `selectionDifferential_div_eq`: the Lande–Arnold gradient `S / v = 𝔼[W' z] / w̄`.

The multivariate statement `S = P ∇ log w̄` is in `SelectionGradientMultivariate.lean`.

## References

* R. Lande, *Quantitative genetic analysis of multivariate evolution, applied to brain:body
  size allometry*, Evolution 33 (1979), 402–416.
* R. Lande, S. J. Arnold, *The measurement of selection on correlated characters*, Evolution 37
  (1983), 1210–1226.
* C. M. Stein, *Estimation of the mean of a multivariate normal distribution*, Ann. Statist. 9
  (1981), 1135–1151.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MathlibExt.Biology.StatisticalGenetics.SelectionGradient

private lemma integrable_pdf_mul_iff {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    {f : ℝ → ℝ} :
    Integrable (fun x => gaussianPDFReal μ v x * f x) ↔
      Integrable f (gaussianReal μ v) := by
  rw [gaussianReal_of_var_ne_zero μ hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF μ v)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF, smul_eq_mul]

private lemma hasDerivAt_pdf {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal μ v)
      (-(x - μ) / v * gaussianPDFReal μ v x) x := by
  have hvR : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  convert ((((hasDerivAt_id x).sub_const μ).pow 2).neg.div_const
    (2 * (v : ℝ))).exp.const_mul (Real.sqrt (2 * Real.pi * v))⁻¹ using 1
  · rfl
  · dsimp
    unfold gaussianPDFReal
    field_simp

private lemma hasDerivAt_pdf_mean {v : ℝ≥0} (hv : v ≠ 0) (m x : ℝ) :
    HasDerivAt (fun a => gaussianPDFReal a v x)
      ((x - m) / v * gaussianPDFReal m v x) m := by
  have hvR : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  convert ((((hasDerivAt_const m x).sub (hasDerivAt_id m)).pow 2).neg.div_const
    (2 * (v : ℝ))).exp.const_mul (Real.sqrt (2 * Real.pi * v))⁻¹ using 1
  · rfl
  · dsimp
    unfold gaussianPDFReal
    field_simp
    ring

private lemma integrable_bounded {W : ℝ → ℝ} (hWm : Measurable W)
    (hWb : ∃ C, ∀ z, |W z| ≤ C) (μ : ℝ) (v : ℝ≥0) :
    Integrable W (gaussianReal μ v) := by
  obtain ⟨C, hC⟩ := hWb
  exact (integrable_const C).mono' hWm.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x)

private lemma integrable_sub_mul_bounded {W : ℝ → ℝ} (hWm : Measurable W)
    (hWb : ∃ C, ∀ z, |W z| ≤ C) (μ : ℝ) (v : ℝ≥0) :
    Integrable (fun x => (x - μ) * W x) (gaussianReal μ v) := by
  obtain ⟨C, hC⟩ := hWb
  have hi : Integrable (fun x : ℝ => x) (gaussianReal μ v) :=
    (memLp_id_gaussianReal 1).integrable (by norm_num)
  exact (hi.sub (integrable_const μ)).mul_bdd hWm.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x)

private lemma pdf_le_nearby {v : ℝ≥0} (hv : v ≠ 0) (μ m x : ℝ)
    (hm : |m - μ| ≤ 1) :
    gaussianPDFReal m v x ≤ Real.exp (1 / (2 * (v : ℝ))) *
      (gaussianPDFReal (μ + 1) v x + gaussianPDFReal (μ - 1) v x) := by
  have hvp : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hden : 0 < 2 * (v : ℝ) := by positivity
  have hml := (abs_le.mp hm).1
  have hmu := (abs_le.mp hm).2
  have hA : 0 ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by positivity
  by_cases ht : 0 ≤ x - μ
  · have hp : (x - μ) * (m - μ - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos ht (by linarith)
    have he : -(x - m) ^ 2 ≤ -(x - (μ + 1)) ^ 2 + 1 := by
      nlinarith [sq_nonneg (m - μ)]
    have hle : gaussianPDFReal m v x ≤
        Real.exp (1 / (2 * (v : ℝ))) * gaussianPDFReal (μ + 1) v x := by
      unfold gaussianPDFReal
      calc
        _ ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
            Real.exp ((-(x - (μ + 1)) ^ 2 + 1) / (2 * (v : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr ((div_le_div_iff_of_pos_right hden).mpr he)) hA
        _ = _ := by rw [add_div, Real.exp_add]; ring
    exact hle.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (gaussianPDFReal_nonneg _ _ _)) (Real.exp_pos _).le)
  · have ht' : x - μ ≤ 0 := le_of_not_ge ht
    have hp : 0 ≤ (x - μ) * (m - μ + 1) * (-1) := by
      have := mul_nonpos_of_nonpos_of_nonneg ht' (by linarith : 0 ≤ m - μ + 1)
      nlinarith
    have he : -(x - m) ^ 2 ≤ -(x - (μ - 1)) ^ 2 + 1 := by
      nlinarith [sq_nonneg (m - μ)]
    have hle : gaussianPDFReal m v x ≤
        Real.exp (1 / (2 * (v : ℝ))) * gaussianPDFReal (μ - 1) v x := by
      unfold gaussianPDFReal
      calc
        _ ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
            Real.exp ((-(x - (μ - 1)) ^ 2 + 1) / (2 * (v : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr ((div_le_div_iff_of_pos_right hden).mpr he)) hA
        _ = _ := by rw [add_div, Real.exp_add]; ring
    exact hle.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (gaussianPDFReal_nonneg _ _ _)) (Real.exp_pos _).le)

private lemma integrable_abs_sub_pdf {v : ℝ≥0} (hv : v ≠ 0) (μ a : ℝ) :
    Integrable (fun x => (|x - μ| + 1) * gaussianPDFReal a v x) := by
  have hi : Integrable (fun x : ℝ => x) (gaussianReal a v) :=
    (memLp_id_gaussianReal 1).integrable (by norm_num)
  have hb := ((hi.sub (integrable_const μ)).abs.add (integrable_const (1 : ℝ)))
  simpa only [Pi.add_def, Pi.sub_def, mul_comm] using
    (integrable_pdf_mul_iff hv).mpr hb


/-- **Stein's lemma** for the normal law `N(μ, v)`, `v > 0`: if `g` is differentiable with
derivative `g'` and `g`, `(z - μ) g z` and `g'` are integrable, then
`𝔼[(z - μ) g z] = v 𝔼[g' z]` (Stein 1981, Lemma 1). -/
theorem integral_sub_mul_gaussianReal {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) {g g' : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hgi : Integrable g (gaussianReal μ v))
    (hxg : Integrable (fun x => (x - μ) * g x) (gaussianReal μ v))
    (hg' : Integrable g' (gaussianReal μ v)) :
    ∫ x, (x - μ) * g x ∂gaussianReal μ v = v * ∫ x, g' x ∂gaussianReal μ v := by
  have hvR : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have hi := (integrable_pdf_mul_iff hv).mpr hxg
  have hi' := (integrable_pdf_mul_iff hv).mpr hg'
  have hig := (integrable_pdf_mul_iff hv).mpr hgi
  have hip : Integrable (g * fun x => -(x - μ) / v * gaussianPDFReal μ v x) := by
    convert hi.const_mul (-(v : ℝ)⁻¹) using 1
    ext x
    dsimp
    ring
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := g) (u' := g') (v := gaussianPDFReal μ v)
    (v' := fun x => -(x - μ) / v * gaussianPDFReal μ v x)
    (fun x _ => hg x) (fun x _ => hasDerivAt_pdf hv x) hip
    (by simpa only [Pi.mul_def, mul_comm] using hi')
    (by simpa only [Pi.mul_def, mul_comm] using hig)
  have he : (fun x => g x * (-(x - μ) / v * gaussianPDFReal μ v x)) =
      fun x => -(v : ℝ)⁻¹ * (gaussianPDFReal μ v x * ((x - μ) * g x)) := by
    ext x
    ring
  rw [he, integral_const_mul] at h
  simp only [mul_comm (g' _) (gaussianPDFReal μ v _)] at h
  rw [integral_gaussianReal_eq_integral_smul hv,
    integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  rw [neg_mul, neg_inj] at h
  have h2 := congrArg (fun a : ℝ => (v : ℝ) * a) h
  simpa only [← mul_assoc, mul_inv_cancel₀ hvR, one_mul] using h2

/-- The mean fitness `w̄(μ) = 𝔼[W z]` of a population whose trait is distributed as
`N(μ, v)`. -/
noncomputable def meanFitness (W : ℝ → ℝ) (μ : ℝ) (v : ℝ≥0) : ℝ :=
  ∫ z, W z ∂gaussianReal μ v

/-- The directional selection differential `S = 𝔼[(z - μ) W z] / w̄`: the mean trait of the
selected parents, weighting each individual by its fitness, minus the mean trait `μ` before
selection. If `w̄ = 0` the division returns the junk value `0`. -/
noncomputable def selectionDifferential (W : ℝ → ℝ) (μ : ℝ) (v : ℝ≥0) : ℝ :=
  (∫ z, (z - μ) * W z ∂gaussianReal μ v) / meanFitness W μ v

/-- The derivative of mean fitness with respect to the trait mean is
`d/dμ w̄(μ) = 𝔼[(z - μ) W z] / v`, for bounded measurable fitness and `v > 0`. -/
theorem hasDerivAt_meanFitness {W : ℝ → ℝ} (hWm : Measurable W) (hWb : ∃ C, ∀ z, |W z| ≤ C)
    {v : ℝ≥0} (hv : v ≠ 0) (μ : ℝ) :
    HasDerivAt (fun m => meanFitness W m v)
      ((∫ z, (z - μ) * W z ∂gaussianReal μ v) / v) μ := by
  obtain ⟨C, hC⟩ := hWb
  have hC0 : 0 ≤ C := (abs_nonneg (W 0)).trans (hC 0)
  have hvp : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  let F : ℝ → ℝ → ℝ := fun m x => gaussianPDFReal m v x * W x
  let F' : ℝ → ℝ → ℝ := fun m x =>
    ((x - m) / v * gaussianPDFReal m v x) * W x
  let B : ℝ → ℝ := fun x =>
    (C / v * Real.exp (1 / (2 * (v : ℝ)))) *
      ((|x - μ| + 1) *
        (gaussianPDFReal (μ + 1) v x + gaussianPDFReal (μ - 1) v x))
  have hBi : Integrable B := by
    convert ((integrable_abs_sub_pdf hv μ (μ + 1)).add
      (integrable_abs_sub_pdf hv μ (μ - 1))).const_mul
        (C / v * Real.exp (1 / (2 * (v : ℝ)))) using 1
    ext x
    dsimp [B]
    ring
  have hbound : ∀ x m, |m - μ| ≤ 1 → ‖F' m x‖ ≤ B x := by
    intro x m hm
    have hx : |x - m| ≤ |x - μ| + 1 := by
      calc
        |x - m| = |(x - μ) + (μ - m)| := by congr 1; ring
        _ ≤ |x - μ| + |μ - m| := abs_add_le _ _
        _ ≤ |x - μ| + 1 := by rw [abs_sub_comm μ m]; gcongr
    dsimp [F', B]
    rw [abs_mul, abs_mul, abs_div]
    simp only [abs_of_nonneg hvp.le,
      abs_of_nonneg (gaussianPDFReal_nonneg m v x)]
    calc
      _ ≤ ((|x - μ| + 1) / v *
          (Real.exp (1 / (2 * (v : ℝ))) *
            (gaussianPDFReal (μ + 1) v x + gaussianPDFReal (μ - 1) v x))) * C := by
        apply mul_le_mul _ (hC x) (abs_nonneg _)
          (mul_nonneg (div_nonneg (by positivity) hvp.le)
            (mul_nonneg (Real.exp_pos _).le
              (add_nonneg (gaussianPDFReal_nonneg _ _ _)
                (gaussianPDFReal_nonneg _ _ _))))
        exact mul_le_mul (div_le_div_of_nonneg_right hx hvp.le)
          (pdf_le_nearby hv μ m x hm) (gaussianPDFReal_nonneg _ _ _) (by positivity)
      _ = _ := by ring
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := F) (F' := F') (bound := B) (s := Metric.ball μ 1)
    (Metric.ball_mem_nhds μ (by norm_num))
    (Filter.Eventually.of_forall (fun m => by dsimp [F]; fun_prop))
    ((integrable_pdf_mul_iff hv).mpr (integrable_bounded hWm ⟨C, hC⟩ μ v))
    (by dsimp [F']; fun_prop)
    (ae_of_all _ fun x m hm => hbound x m
      (le_of_lt (by simpa only [Metric.mem_ball, Real.dist_eq] using hm))) hBi
    (ae_of_all _ fun x m _ => (hasDerivAt_pdf_mean hv m x).mul_const (W x))
  have he : (∫ x, F' μ x) =
      (∫ x, (x - μ) * W x ∂gaussianReal μ v) / v := by
    rw [integral_gaussianReal_eq_integral_smul hv]
    simp only [smul_eq_mul]
    rw [← integral_div]
    congr 1
    ext x
    dsimp [F']
    ring
  rw [he] at hmain
  convert hmain.2 using 1
  ext m
  exact integral_gaussianReal_eq_integral_smul hv

/-- **Lande's equation** for one normally distributed trait (Lande 1979): the selection
differential is the phenotypic variance times the derivative of log mean fitness with respect
to the trait mean, `S = v · d/dμ log w̄(μ)`. -/
theorem selectionDifferential_eq_mul_deriv_log {W : ℝ → ℝ} (hWm : Measurable W)
    (hWb : ∃ C, ∀ z, |W z| ≤ C) {v : ℝ≥0} (hv : v ≠ 0) {μ : ℝ} (hw : meanFitness W μ v ≠ 0) :
    selectionDifferential W μ v = v * deriv (fun m => Real.log (meanFitness W m v)) μ := by
  have hd := (hasDerivAt_meanFitness hWm hWb hv μ).log hw
  rw [hd.deriv]
  unfold selectionDifferential
  have hvR : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  field_simp

/-- **The Lande–Arnold selection gradient** for one normally distributed trait: for a
differentiable bounded fitness function with integrable derivative, `β = S / v = 𝔼[W' z] / w̄`,
the average slope of relative fitness `W / w̄` (Lande–Arnold 1983). -/
theorem selectionDifferential_div_eq {W W' : ℝ → ℝ} (hW : ∀ z, HasDerivAt W (W' z) z)
    (hWb : ∃ C, ∀ z, |W z| ≤ C) {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hW' : Integrable W' (gaussianReal μ v)) :
    selectionDifferential W μ v / v = (∫ z, W' z ∂gaussianReal μ v) / meanFitness W μ v := by
  have hWm : Measurable W :=
    (continuous_iff_continuousAt.mpr (fun x => (hW x).continuousAt)).measurable
  have hvR : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  unfold selectionDifferential
  rw [integral_sub_mul_gaussianReal hv hW (integrable_bounded hWm hWb μ v)
    (integrable_sub_mul_bounded hWm hWb μ v) hW']
  calc
    _ = ((v : ℝ) / v) * ((∫ z, W' z ∂gaussianReal μ v) / meanFitness W μ v) := by
      ring
    _ = _ := by rw [div_self hvR, one_mul]

end MathlibExt.Biology.StatisticalGenetics.SelectionGradient
