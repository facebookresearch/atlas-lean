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
import MathlibExt.Probability.Statistics.SteinLemma

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
* `integral_mul_indicator_Ioi_div_eq_sqrt`: for truncation fitness `W = 1_{z > 0}` on `N(0, 1)`,
  the selection differential is `√(2/π)`; `hasDerivAt_indicator_Ioi_of_ne` and
  `not_forall_hasDerivAt_indicator_Ioi` show why the Lande–Arnold form does not apply.

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
theorem integral_sub_mul_gaussianReal {μ : ℝ} {v : ℝ≥0} (_hv : v ≠ 0) {g g' : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (_hgi : Integrable g (gaussianReal μ v))
    (_hxg : Integrable (fun x => (x - μ) * g x) (gaussianReal μ v))
    (hg' : Integrable g' (gaussianReal μ v)) :
    ∫ x, (x - μ) * g x ∂gaussianReal μ v = v * ∫ x, g' x ∂gaussianReal μ v := by
  exact (ProbabilityTheory.integrable_and_integral_sub_mul_gaussianReal μ v hg hg').2

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


/-! ### Truncation fitness

The acceptance example `W = 1_{z > 0}` on `N(0, 1)` satisfies the bounded measurable hypotheses
of `selectionDifferential_eq_mul_deriv_log` with `S = √(2/π)`, but not the
everywhere-differentiability hypothesis of `selectionDifferential_div_eq`. -/

/-- Mean fitness of the truncation fitness: `𝔼[1_{z>0}] = 1/2` for `z ~ N(0,1)`,
by negation symmetry of the standard Gaussian. -/
private theorem gaussianReal_Ioi_toReal :
    ((gaussianReal (0 : ℝ) (1 : NNReal)) (Set.Ioi (0 : ℝ))).toReal = 1 / 2 := by
  have hv : (1 : NNReal) ≠ 0 := one_ne_zero
  have hsym : (gaussianReal (0 : ℝ) (1 : NNReal)).map (fun x : ℝ => -x) =
      gaussianReal (0 : ℝ) (1 : NNReal) := by
    rw [gaussianReal_map_neg, neg_zero]
  have hmap : ((gaussianReal (0 : ℝ) (1 : NNReal)).map (fun x : ℝ => -x)) (Set.Ioi (0 : ℝ)) =
      gaussianReal (0 : ℝ) (1 : NNReal) ((fun x : ℝ => -x) ⁻¹' (Set.Ioi (0 : ℝ))) :=
    Measure.map_apply (by fun_prop) measurableSet_Ioi
  have hpre : (fun x : ℝ => -x) ⁻¹' (Set.Ioi (0 : ℝ)) = Set.Iio (0 : ℝ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio]
    constructor <;> intro h <;> linarith
  rw [hsym, hpre] at hmap
  have hU : Set.Iio (0 : ℝ) ∪ {0} ∪ Set.Ioi (0 : ℝ) = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_Ioi, Set.mem_Iio,
      Set.mem_univ, iff_true]
    obtain h | h | h := lt_trichotomy x (0 : ℝ)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hd1 : Disjoint (Set.Iio (0 : ℝ) ∪ {0}) (Set.Ioi (0 : ℝ)) := by
    rw [Set.disjoint_left]
    rintro x (hx | hx) hxIoi
    · rw [Set.mem_Iio] at hx; rw [Set.mem_Ioi] at hxIoi; linarith
    · rw [Set.mem_singleton_iff] at hx; rw [Set.mem_Ioi] at hxIoi; linarith
  have hd2 : Disjoint (Set.Iio (0 : ℝ)) ({0} : Set ℝ) := by
    rw [Set.disjoint_left]
    rintro x hx hx0
    rw [Set.mem_Iio] at hx; rw [Set.mem_singleton_iff] at hx0; linarith
  have hns : NullSingletonClass (gaussianReal (0 : ℝ) (1 : NNReal)) :=
    nullSingletonClass_gaussianReal hv
  have h0 : gaussianReal (0 : ℝ) (1 : NNReal) ({0} : Set ℝ) = 0 := by simp
  have hsum : gaussianReal (0 : ℝ) (1 : NNReal) (Set.Ioi (0 : ℝ)) +
      gaussianReal (0 : ℝ) (1 : NNReal) (Set.Ioi (0 : ℝ)) = 1 := by
    have h1 : gaussianReal (0 : ℝ) (1 : NNReal) (Set.Iio (0 : ℝ) ∪ {0} ∪ Set.Ioi (0 : ℝ)) = 1 := by
      rw [hU]
      simp
    rwa [measure_union hd1 measurableSet_Ioi,
      measure_union hd2 (measurableSet_singleton 0), h0, ← hmap, add_zero] at h1
  have hfin : gaussianReal (0 : ℝ) (1 : NNReal) (Set.Ioi (0 : ℝ)) ≠ ⊤ := measure_ne_top _ _
  have h2 : ((gaussianReal (0 : ℝ) (1 : NNReal)) (Set.Ioi (0 : ℝ))).toReal +
      ((gaussianReal (0 : ℝ) (1 : NNReal)) (Set.Ioi (0 : ℝ))).toReal = 1 := by
    rw [← ENNReal.toReal_add hfin hfin, hsum, ENNReal.toReal_one]
  linarith

/-- Numerator: `𝔼[z 1_{z>0}] = 1 / √(2π)` for `z ~ N(0,1)`, by FTC-2 on `(0, ∞)`
with antiderivative `-(2π)^{-1/2} exp(-x^2 / 2)`. -/
private theorem integral_mul_indicator_Ioi_eq :
    (∫ z, z * (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) z ∂gaussianReal 0 1) =
      (Real.sqrt (2 * Real.pi))⁻¹ := by
  have hrewrite : ∀ z : ℝ, z * (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) z =
      (Set.Ioi (0 : ℝ)).indicator (fun z => z) z := fun z => by
    by_cases h : z ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem h _, Set.indicator_of_mem h _]; simp
    · rw [Set.indicator_of_notMem h _, Set.indicator_of_notMem h _]; simp
  simp only [hrewrite]
  rw [integral_indicator measurableSet_Ioi]
  have hv : (1 : NNReal) ≠ 0 := one_ne_zero
  rw [gaussianReal_of_var_ne_zero _ hv]
  have hconv : (∫ x in Set.Ioi (0 : ℝ), x
        ∂(volume.withDensity (gaussianPDF (0 : ℝ) (1 : NNReal)))) =
      ∫ x in Set.Ioi (0 : ℝ), (gaussianPDF (0 : ℝ) (1 : NNReal) x).toReal • x ∂volume :=
    setIntegral_withDensity_eq_setIntegral_toReal_smul (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ => gaussianPDF_lt_top) _ measurableSet_Ioi
  rw [hconv]
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt
      (fun x : ℝ => (-(Real.sqrt (2 * Real.pi))⁻¹) * Real.exp (-(1 / 2 : ℝ) * x ^ 2))
      (x * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ) * x ^ 2))) x := by
    intro x _
    have hg : HasDerivAt (fun x : ℝ => -(1 / 2 : ℝ) * x ^ 2)
        (-(1 / 2 : ℝ) * (((2 : ℕ) : ℝ) * x ^ (2 - 1))) x :=
      HasDerivAt.const_mul (-(1 / 2 : ℝ)) (hasDerivAt_pow 2 x)
    have hexp : HasDerivAt (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2))
        (Real.exp (-(1 / 2 : ℝ) * x ^ 2) * (-(1 / 2 : ℝ) * (((2 : ℕ) : ℝ) * x ^ (2 - 1)))) x :=
      hg.exp
    have h := hexp.const_mul (-(Real.sqrt (2 * Real.pi))⁻¹)
    have hval : (-(Real.sqrt (2 * Real.pi))⁻¹) *
        (Real.exp (-(1 / 2 : ℝ) * x ^ 2) * (-(1 / 2 : ℝ) * (((2 : ℕ) : ℝ) * x ^ (2 - 1)))) =
        x * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
      rw [show ((2 : ℕ) : ℝ) = 2 by norm_num, show (2 - 1 : ℕ) = 1 by norm_num, pow_one]
      ring
    rw [hval] at h
    exact h
  have hint : IntegrableOn
      (fun x : ℝ => x * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ) * x ^ 2)))
      (Set.Ioi 0) := by
    have hbase := (integrable_mul_exp_neg_mul_sq (show (0 : ℝ) < 1 / 2 by norm_num)).const_mul
      ((Real.sqrt (2 * Real.pi))⁻¹)
    have heq : (fun x : ℝ => x * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ) * x ^ 2))) =
        (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * (x * Real.exp (-(1 / 2 : ℝ) * x ^ 2))) := by
      funext x; ring
    rw [heq]
    exact hbase.integrableOn
  have hlim : Filter.Tendsto
      (fun x : ℝ => (-(Real.sqrt (2 * Real.pi))⁻¹) * Real.exp (-(1 / 2 : ℝ) * x ^ 2))
      Filter.atTop (nhds 0) := by
    have hsq : Filter.Tendsto (fun x : ℝ => x ^ 2) Filter.atTop Filter.atTop := by
      have h : Filter.Tendsto (fun x : ℝ => x * x) Filter.atTop Filter.atTop :=
        Filter.tendsto_mul_self_atTop
      simpa [pow_two] using h
    have hmul : Filter.Tendsto (fun x : ℝ => (1 / 2 : ℝ) * x ^ 2) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num) hsq
    have hexp0 : Filter.Tendsto (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2)) Filter.atTop
        (nhds 0) := by
      have h := Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp hmul)
      refine Filter.Tendsto.congr (fun x => ?_) h
      simp only [Function.comp_apply]
      congr 1
      ring
    simpa only [smul_eq_mul, mul_zero] using hexp0.const_smul (-(Real.sqrt (2 * Real.pi))⁻¹)
  have hf0 : (fun x : ℝ => (-(Real.sqrt (2 * Real.pi))⁻¹) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) 0 =
      -((Real.sqrt (2 * Real.pi))⁻¹) := by
    change (-(Real.sqrt (2 * Real.pi))⁻¹) * Real.exp (-(1 / 2 : ℝ) * (0 : ℝ) ^ 2) =
      -((Real.sqrt (2 * Real.pi))⁻¹)
    rw [show (-(1 / 2 : ℝ)) * (0 : ℝ) ^ 2 = 0 by norm_num, Real.exp_zero, mul_one]
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  have hFTC2 : (∫ x in Set.Ioi (0 : ℝ),
      x * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ) * x ^ 2))) =
      (Real.sqrt (2 * Real.pi))⁻¹ := by
    have h := hFTC
    simpa [hf0] using h
  have hpdf : (fun x : ℝ => (gaussianPDF (0 : ℝ) (1 : NNReal) x).toReal • x) =
      (fun x : ℝ => x * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ) * x ^ 2))) := by
    funext x
    rw [toReal_gaussianPDF, smul_eq_mul]
    have h1 : (2 * Real.pi * ((1 : NNReal) : ℝ)) = 2 * Real.pi := by simp
    have h2 : (-(x - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ))) = -(1 / 2 : ℝ) * x ^ 2 := by
      simp only [sub_zero, NNReal.coe_one, mul_one]
      ring
    unfold gaussianPDFReal
    rw [h1, h2]
    ring
  rw [hpdf]
  exact hFTC2

/-- **Truncation selection on a standard normal trait.** For fitness `W = 1_{z > 0}` and
`z ~ N(0, 1)`, the selection differential `𝔼[z W] / 𝔼[W]` is `√(2/π)`. -/
theorem integral_mul_indicator_Ioi_div_eq_sqrt :
    (∫ z, z * (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) z ∂gaussianReal 0 1) /
        (∫ z, (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) z ∂gaussianReal 0 1) =
      Real.sqrt (2 / Real.pi) := by
  have hnum := integral_mul_indicator_Ioi_eq
  have hden : (∫ z, (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) z ∂gaussianReal 0 1) =
      1 / 2 := by
    rw [integral_indicator measurableSet_Ioi]
    simp only [setIntegral_const, smul_eq_mul, mul_one]
    change ((gaussianReal (0 : ℝ) (1 : NNReal)) (Set.Ioi (0 : ℝ))).toReal = 1 / 2
    exact gaussianReal_Ioi_toReal
  rw [hnum, hden]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2pi : (0 : ℝ) < 2 * Real.pi := mul_pos (by norm_num) hpi
  have hnn : (0 : ℝ) ≤ 2 / Real.sqrt (2 * Real.pi) := div_nonneg zero_le_two (Real.sqrt_nonneg _)
  have hsq : (2 / Real.sqrt (2 * Real.pi)) ^ 2 = 2 / Real.pi := by
    have hpi0 : Real.pi ≠ 0 := ne_of_gt hpi
    have h2pi0 : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num) hpi0
    rw [div_pow, Real.sq_sqrt h2pi.le]
    field
  have hne : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h2pi)
  have hstep : (Real.sqrt (2 * Real.pi))⁻¹ / (1 / 2 : ℝ) = 2 / Real.sqrt (2 * Real.pi) := by
    field
  rw [hstep, ← Real.sqrt_sq hnn, hsq]

/-- The truncation fitness `1_{z > 0}` has derivative `0` at every `z ≠ 0`. -/
theorem hasDerivAt_indicator_Ioi_of_ne {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt ((Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ))) 0 z := by
  rcases lt_or_gt_of_ne hz with h | h
  · have hmem : Set.Iic (0 : ℝ) ∈ nhds z := Iic_mem_nhds h
    have heq : (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) =ᶠ[nhds z] fun _ => (0 : ℝ) := by
      filter_upwards [hmem] with x hx
      have hxle : x ≤ 0 := hx
      have hx' : x ∉ Set.Ioi (0 : ℝ) := fun h => not_lt_of_ge hxle h
      rw [Set.indicator_of_notMem hx' _]
    exact (hasDerivAt_const z (0 : ℝ)).congr_of_eventuallyEq heq
  · have hmem : Set.Ioi (0 : ℝ) ∈ nhds z := Ioi_mem_nhds h
    have heq : (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) =ᶠ[nhds z] fun _ => (1 : ℝ) := by
      filter_upwards [hmem] with x hx
      rw [Set.indicator_of_mem hx _]
    exact (hasDerivAt_const z (1 : ℝ)).congr_of_eventuallyEq heq

/-- The truncation fitness `1_{z > 0}` is not everywhere differentiable (it is not continuous at
`0`), so it does not satisfy the everywhere-differentiability hypothesis of the Lande–Arnold
(Stein) form `selectionDifferential_div_eq`. -/
theorem not_forall_hasDerivAt_indicator_Ioi :
    ¬ ∃ W' : ℝ → ℝ, ∀ z, HasDerivAt ((Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ))) (W' z) z := by
  rintro ⟨W', hW'⟩
  have hcont : ContinuousAt ((Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ))) 0 :=
    (hW' 0).continuousAt
  have h0 : (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) (0 : ℝ) = 0 :=
    Set.indicator_of_notMem (by rw [Set.mem_Ioi]; exact lt_irrefl 0) _
  have hev : ∀ᶠ x in nhds (0 : ℝ),
      (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) x < 1 / 2 :=
    Filter.Tendsto.eventually hcont (eventually_lt_nhds (by rw [h0]; norm_num))
  have hs : {x : ℝ | (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) x < 1 / 2} ∈ nhds (0 : ℝ) := hev
  have hmem : (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ)) := by
    rw [closure_Ioi]
    exact le_rfl
  have h0mem : (0 : ℝ) ∈
      interior {x : ℝ | (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) x < 1 / 2} :=
    mem_interior_iff_mem_nhds.mpr hs
  obtain ⟨x, hxopen, hxs⟩ := mem_closure_iff.mp hmem _ isOpen_interior h0mem
  have hxmem : x ∈ {x : ℝ | (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) x < 1 / 2} :=
    interior_subset hxopen
  have hxlt : (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) x < 1 / 2 := hxmem
  have hfx : (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) x = 1 := Set.indicator_of_mem hxs _
  rw [hfx] at hxlt
  norm_num at hxlt

end MathlibExt.Biology.StatisticalGenetics.SelectionGradient
