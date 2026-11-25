/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

import MathlibExt.Probability.Distributions.GaussianDensity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Lande's selection gradient for multivariate normal traits

A vector of quantitative traits `z ∈ ℝ^ι` is multivariate normal before selection,
`z ~ N(μ, P)` with positive definite phenotypic covariance matrix `P`. An individual with
phenotype `z` has fitness `W z`. Mean fitness is `w̄(μ) = 𝔼[W z]` and the directional selection
differential is `S = 𝔼[W z · (z - μ)] / w̄` (Lande–Arnold 1983).

**Lande's equation** (Lande 1979): `S = P ∇_μ log w̄(μ)`, i.e. the selection gradient
`β = P⁻¹ S` is the gradient of log mean fitness with respect to the vector of trait means.

The identities need a bounded measurable fitness function (fitness is biologically
nonnegative; boundedness covers stabilizing and Gaussian fitness surfaces) and, for the
logarithm, nonzero mean fitness.

## Main results

* `hasGradientAt_meanFitnessMV`: `∇_μ w̄(μ) = P⁻¹ 𝔼[W z · (z - μ)]`.
* `selectionDifferentialMV_eq`: **Lande's equation** `S = P ∇_μ log w̄(μ)`.

## References

* R. Lande, *Quantitative genetic analysis of multivariate evolution, applied to brain:body
  size allometry*, Evolution 33 (1979), 402–416.
* R. Lande, S. J. Arnold, *The measurement of selection on correlated characters*, Evolution 37
  (1983), 1210–1226.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix

namespace MathlibExt.Biology.StatisticalGenetics.SelectionGradient

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped RealInnerProductSpace Topology MatrixOrder
open InnerProductSpace WithLp

private lemma pdf_hasFDerivAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : Matrix ι ι ℝ} (hP : P.PosDef) (m x : EuclideanSpace ℝ ι) :
    HasFDerivAt (fun m => MetaMathlibExt.multivariateGaussianPDFReal m P x)
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)
        (MetaMathlibExt.multivariateGaussianPDFReal m P x •
          toEuclideanCLM (𝕜 := ℝ) P⁻¹ (x - m))) m := by
  let B := toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt P)⁻¹
  have hb := B.hasFDerivAt.comp m ((hasFDerivAt_const x m).sub (hasFDerivAt_id m))
  have hn := hb.norm_sq
  have he := ((hn.const_mul (-1 / 2)).exp).const_mul
    (((√(2 * Real.pi)) ^ Fintype.card ι)⁻¹ * (√P.det)⁻¹)
  have heq : (fun m => MetaMathlibExt.multivariateGaussianPDFReal m P x) =
      (fun m => ((√(2 * Real.pi)) ^ Fintype.card ι)⁻¹ * (√P.det)⁻¹ *
        Real.exp ((-1 / 2) * ‖B (x - m)‖ ^ 2)) := by
    funext m
    rw [MetaMathlibExt.norm_sq_sqrt_inv_apply hP]
    simp only [MetaMathlibExt.multivariateGaussianPDFReal]
    congr 2
    ring
  rw [heq]
  convert he using 1 <;> try rfl
  ext v
  simp only [toDual_apply_apply, real_inner_smul_left, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, _root_.neg_apply,
    ContinuousLinearMap.id_apply, zero_sub, map_neg, innerSL_apply_apply,
    Function.comp_apply, Pi.sub_apply, id_eq, smul_eq_mul]
  have hsa : IsSelfAdjoint B := by
    dsimp [B]
    rw [hP.posSemidef.inv_sqrt]
    exact (CFC.sqrt_nonneg P⁻¹).isSelfAdjoint.map _
  have hsq : B * B = toEuclideanCLM (𝕜 := ℝ) P⁻¹ := by
    dsimp [B]
    rw [← map_mul, hP.posSemidef.inv_sqrt,
      CFC.sqrt_mul_sqrt_self _ hP.posSemidef.inv.nonneg]
  have hi : ⟪B (x - m), B v⟫ = ⟪toEuclideanCLM (𝕜 := ℝ) P⁻¹ (x - m), v⟫ := by
    rw [← ContinuousLinearMap.adjoint_inner_left, hsa.adjoint_eq,
      ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, hsq]
  rw [hi, MetaMathlibExt.multivariateGaussianPDFReal,
    ← MetaMathlibExt.norm_sq_sqrt_inv_apply hP]
  dsimp [B]
  ring_nf

private lemma radial_integrable {ι : Type*} [Fintype ι] {c : ℝ} (hc : 0 < c) :
    Integrable (fun v : EuclideanSpace ℝ ι => Real.exp (-c * ‖v‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (show 0 < (c : ℂ).re from hc) 0 (0 : EuclideanSpace ℝ ι)).norm
  convert h using 1
  ext v
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  norm_cast

private lemma scalar_decay {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) (htr : t ≤ r + 1) :
    Real.exp (-r ^ 2 / 2) * r ≤
      16 * Real.exp (1 / 2) * Real.exp (-t ^ 2 / 8) := by
  have hrb : r ≤ 16 * Real.exp (r ^ 2 / 4) := by
    have he := Real.add_one_le_exp (r ^ 2 / 4)
    have hs := sq_nonneg (r - 2)
    nlinarith
  have ht2 : t ^ 2 ≤ 2 * r ^ 2 + 2 := by
    have hs := sq_nonneg (r - 1)
    nlinarith
  calc
    Real.exp (-r ^ 2 / 2) * r ≤
        Real.exp (-r ^ 2 / 2) * (16 * Real.exp (r ^ 2 / 4)) :=
      mul_le_mul_of_nonneg_left hrb (Real.exp_pos _).le
    _ = 16 * Real.exp (-r ^ 2 / 4) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ 16 * Real.exp (1 / 2 - t ^ 2 / 8) := by
      gcongr
      nlinarith
    _ = 16 * Real.exp (1 / 2) * Real.exp (-t ^ 2 / 8) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring_nf

private lemma integrable_affine_radial {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : Matrix ι ι ℝ} (hP : P.PosDef) (μ : EuclideanSpace ℝ ι) {c : ℝ} (hc : 0 < c)
    :
    Integrable (fun x => Real.exp (-c *
      ‖toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt P)⁻¹ (x - μ)‖ ^ 2)) := by
  have hd : 0 < (CFC.sqrt P).det := by
    rw [hP.posSemidef.det_sqrt, RCLike.sqrt_real]
    exact Real.sqrt_pos.2 hP.det_pos
  let e := MetaMathlibExt.affineEquiv μ (CFC.sqrt P) hd.ne'.isUnit
  have hg : Integrable (fun x => Real.exp (-c * ‖e.symm x‖ ^ 2)) (volume.map e) := by
    apply (integrable_map_equiv e _).2
    simpa only [Function.comp_def, e.symm_apply_apply] using
      (radial_integrable (ι := ι) hc)
  rw [MetaMathlibExt.map_affineEquiv_volume] at hg
  have hn : ENNReal.ofReal |((CFC.sqrt P).det)⁻¹| ≠ 0 := by
    exact (ENNReal.ofReal_pos.2 (abs_pos.2 (inv_ne_zero hd.ne'))).ne'
  exact (integrable_smul_measure hn ENNReal.ofReal_ne_top).1 hg

private lemma pdf_derivative_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : Matrix ι ι ℝ} (hP : P.PosDef) (μ m x : EuclideanSpace ℝ ι) (a : ℝ)
    {C : ℝ} (ha : |a| ≤ C)
    (hm : ‖toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt P)⁻¹ (m - μ)‖ ≤ 1) :
    ‖a • InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)
      (MetaMathlibExt.multivariateGaussianPDFReal m P x •
        toEuclideanCLM (𝕜 := ℝ) P⁻¹ (x - m))‖ ≤
      C * (((√(2 * Real.pi)) ^ Fintype.card ι)⁻¹ * (√P.det)⁻¹) *
        ‖toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt P)⁻¹‖ *
        (16 * Real.exp (1 / 2)) * Real.exp ((-1 / 8) *
          ‖toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt P)⁻¹ (x - μ)‖ ^ 2) := by
  let B := toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt P)⁻¹
  let A := ((√(2 * Real.pi)) ^ Fintype.card ι)⁻¹ * (√P.det)⁻¹
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ C := (abs_nonneg a).trans ha
  have hsq : B * B = toEuclideanCLM (𝕜 := ℝ) P⁻¹ := by
    dsimp [B]
    rw [← map_mul, hP.posSemidef.inv_sqrt,
      CFC.sqrt_mul_sqrt_self _ hP.posSemidef.inv.nonneg]
  have hq : ‖toEuclideanCLM (𝕜 := ℝ) P⁻¹ (x - m)‖ ≤ ‖B‖ * ‖B (x - m)‖ := by
    rw [← hsq, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
    exact B.le_opNorm _
  have ht : ‖B (x - μ)‖ ≤ ‖B (x - m)‖ + 1 := by
    calc
      ‖B (x - μ)‖ = ‖B (x - m) + B (m - μ)‖ := by
        rw [← map_add]
        congr 2
        abel
      _ ≤ ‖B (x - m)‖ + ‖B (m - μ)‖ := norm_add_le _ _
      _ ≤ ‖B (x - m)‖ + 1 := by linarith
  have hd := scalar_decay (norm_nonneg (B (x - μ))) (norm_nonneg (B (x - m))) ht
  have hp : MetaMathlibExt.multivariateGaussianPDFReal m P x =
      A * Real.exp (-‖B (x - m)‖ ^ 2 / 2) := by
    rw [MetaMathlibExt.multivariateGaussianPDFReal,
      ← MetaMathlibExt.norm_sq_sqrt_inv_apply hP]
  have hp0 : 0 ≤ MetaMathlibExt.multivariateGaussianPDFReal m P x := by
    rw [hp]; positivity
  rw [norm_smul, (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).norm_map,
    norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp0, hp]
  calc
    |a| * (A * Real.exp (-‖B (x - m)‖ ^ 2 / 2) *
        ‖toEuclideanCLM (𝕜 := ℝ) P⁻¹ (x - m)‖) ≤
      C * (A * Real.exp (-‖B (x - m)‖ ^ 2 / 2) * (‖B‖ * ‖B (x - m)‖)) := by
        gcongr
    _ = (C * A * ‖B‖) * (Real.exp (-‖B (x - m)‖ ^ 2 / 2) * ‖B (x - m)‖) := by ring
    _ ≤ (C * A * ‖B‖) * (16 * Real.exp (1 / 2) *
        Real.exp (-‖B (x - μ)‖ ^ 2 / 8)) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by dsimp [A, B]; ring_nf

private lemma pdf_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m x : EuclideanSpace ℝ ι) (P : Matrix ι ι ℝ) :
    0 ≤ MetaMathlibExt.multivariateGaussianPDFReal m P x := by
  unfold MetaMathlibExt.multivariateGaussianPDFReal
  positivity

private lemma pdf_measurable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : EuclideanSpace ℝ ι) (P : Matrix ι ι ℝ) :
    Measurable (MetaMathlibExt.multivariateGaussianPDFReal m P) := by
  unfold MetaMathlibExt.multivariateGaussianPDFReal
  fun_prop

private lemma integral_pdf {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : EuclideanSpace ℝ ι → E)
    {P : Matrix ι ι ℝ} (hP : P.PosDef) (m : EuclideanSpace ℝ ι) :
    (∫ x, f x ∂multivariateGaussian m P) =
      ∫ x, MetaMathlibExt.multivariateGaussianPDFReal m P x • f x := by
  rw [MetaMathlibExt.multivariateGaussian_eq_withDensity m hP,
    integral_withDensity_eq_integral_toReal_smul
      (show Measurable (fun x => ENNReal.ofReal
        (MetaMathlibExt.multivariateGaussianPDFReal m P x)) from
          ENNReal.measurable_ofReal.comp (pdf_measurable m P))
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (pdf_nonneg _ _ _)]

private lemma integrable_pdf {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : EuclideanSpace ℝ ι → E}
    {P : Matrix ι ι ℝ} (hP : P.PosDef) (m : EuclideanSpace ℝ ι)
    (hf : Integrable f (multivariateGaussian m P)) :
    Integrable (fun x => MetaMathlibExt.multivariateGaussianPDFReal m P x • f x) := by
  rw [MetaMathlibExt.multivariateGaussian_eq_withDensity m hP] at hf
  have h := (integrable_withDensity_iff_integrable_smul'
    (ENNReal.measurable_ofReal.comp (pdf_measurable m P))
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).1 hf
  simpa only [Function.comp_apply, ENNReal.toReal_ofReal (pdf_nonneg _ _ _)] using h

/-- The mean fitness `w̄(μ) = 𝔼[W z]` of a population whose trait vector is distributed as
`N(μ, P)`. -/
noncomputable def meanFitnessMV (W : EuclideanSpace ℝ ι → ℝ) (P : Matrix ι ι ℝ)
    (μ : EuclideanSpace ℝ ι) : ℝ :=
  ∫ z, W z ∂multivariateGaussian μ P

/-- The directional selection differential `S = 𝔼[W z · (z - μ)] / w̄` of a trait vector
distributed as `N(μ, P)`: the fitness-weighted mean trait vector of the selected parents minus
the mean `μ` before selection. If `w̄ = 0` it is the junk value `0`. -/
noncomputable def selectionDifferentialMV (W : EuclideanSpace ℝ ι → ℝ) (P : Matrix ι ι ℝ)
    (μ : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  (meanFitnessMV W P μ)⁻¹ • ∫ z, W z • (z - μ) ∂multivariateGaussian μ P

/-- The gradient of mean fitness with respect to the vector of trait means is
`∇_μ w̄(μ) = P⁻¹ 𝔼[W z · (z - μ)]`, for positive definite `P` and bounded measurable `W`. -/
theorem hasGradientAt_meanFitnessMV {W : EuclideanSpace ℝ ι → ℝ} (hWm : Measurable W)
    (hWb : ∃ C, ∀ z, |W z| ≤ C) {P : Matrix ι ι ℝ} (hP : P.PosDef) (μ : EuclideanSpace ℝ ι) :
    HasGradientAt (meanFitnessMV W P)
      (toEuclideanCLM (𝕜 := ℝ) P⁻¹ (∫ z, W z • (z - μ) ∂multivariateGaussian μ P)) μ := by
  rcases hWb with ⟨C, hC⟩
  let B := toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt P)⁻¹
  let A := ((√(2 * Real.pi)) ^ Fintype.card ι)⁻¹ * (√P.det)⁻¹
  let K := C * A * ‖B‖ * (16 * Real.exp (1 / 2))
  let F := fun m x => W x * MetaMathlibExt.multivariateGaussianPDFReal m P x
  let D := fun m x => W x • InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)
    (MetaMathlibExt.multivariateGaussianPDFReal m P x •
      toEuclideanCLM (𝕜 := ℝ) P⁻¹ (x - m))
  have hs : {m | ‖B (m - μ)‖ < 1} ∈ 𝓝 μ := by
    apply IsOpen.mem_nhds (isOpen_lt (by fun_prop) continuous_const)
    simp
  have hWi : Integrable W (multivariateGaussian μ P) :=
    (integrable_const C).mono' hWm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x)
  have hFi : Integrable (F μ) := by
    simpa only [F, smul_eq_mul, mul_comm] using integrable_pdf hP μ hWi
  have hFm : ∀ᶠ m in 𝓝 μ, AEStronglyMeasurable (F m) := by
    exact Filter.Eventually.of_forall fun m =>
      (hWm.mul (pdf_measurable m P)).aestronglyMeasurable
  have hDm : AEStronglyMeasurable (D μ) := by
    dsimp [D]
    apply hWm.aestronglyMeasurable.smul
    apply Continuous.aestronglyMeasurable
    unfold MetaMathlibExt.multivariateGaussianPDFReal
    fun_prop
  have hbound : ∀ᵐ x, ∀ m ∈ {m | ‖B (m - μ)‖ < 1},
      ‖D m x‖ ≤ K * Real.exp ((-1 / 8) * ‖B (x - μ)‖ ^ 2) := by
    exact ae_of_all _ fun x m hm => pdf_derivative_bound hP μ m x (W x) (hC x) hm.le
  have hbi : Integrable (fun x => K * Real.exp ((-1 / 8) * ‖B (x - μ)‖ ^ 2)) := by
    simpa only [neg_div, neg_mul] using
      (integrable_affine_radial hP μ (show (0 : ℝ) < 1 / 8 by norm_num)).const_mul K
  have hdiff : ∀ᵐ x, ∀ m ∈ {m | ‖B (m - μ)‖ < 1},
      HasFDerivAt (F · x) (D m x) m := by
    exact ae_of_all _ fun x m _ => (pdf_hasFDerivAt hP m x).const_mul (W x)
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le hs hFm hFi hDm hbound hbi hdiff
  have hmoment : Integrable (fun x => W x • (x - μ)) (multivariateGaussian μ P) := by
    have hi : Integrable (fun x : EuclideanSpace ℝ ι => x) (multivariateGaussian μ P) :=
      IsGaussian.integrable_id
    exact (hi.sub (integrable_const μ)).bdd_smul C hWm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x)
  have hmi := integrable_pdf hP μ hmoment
  have heq : meanFitnessMV W P = (fun m => ∫ x, F m x) := by
    funext m
    simpa only [meanFitnessMV, F, smul_eq_mul, mul_comm] using integral_pdf W hP m
  rw [hasGradientAt_iff_hasFDerivAt, heq]
  convert h using 1
  dsimp [D]
  rw [integral_pdf (fun x => W x • (x - μ)) hP μ]
  rw [← (toEuclideanCLM (𝕜 := ℝ) P⁻¹).integral_comp_comm hmi]
  let T := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).toContinuousLinearEquiv
  have hT : (∫ x, InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)
      (toEuclideanCLM (𝕜 := ℝ) P⁻¹
        (MetaMathlibExt.multivariateGaussianPDFReal μ P x • W x • (x - μ)))) =
      InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)
        (∫ x, toEuclideanCLM (𝕜 := ℝ) P⁻¹
          (MetaMathlibExt.multivariateGaussianPDFReal μ P x • W x • (x - μ))) :=
    T.toContinuousLinearMap.integral_comp_comm
      ((toEuclideanCLM (𝕜 := ℝ) P⁻¹).integrable_comp hmi)
  rw [← hT]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by simp only [map_smul, smul_smul, mul_comm]

/-- **Lande's equation** (Lande 1979): for a multivariate normal trait vector, the selection
differential is the phenotypic covariance matrix applied to the gradient of log mean fitness
with respect to the trait means, `S = P ∇_μ log w̄(μ)`. -/
theorem selectionDifferentialMV_eq {W : EuclideanSpace ℝ ι → ℝ} (hWm : Measurable W)
    (hWb : ∃ C, ∀ z, |W z| ≤ C) {P : Matrix ι ι ℝ} (hP : P.PosDef) {μ : EuclideanSpace ℝ ι}
    (hw : meanFitnessMV W P μ ≠ 0) :
    selectionDifferentialMV W P μ =
      toEuclideanCLM (𝕜 := ℝ) P (gradient (fun m => Real.log (meanFitnessMV W P m)) μ) := by
  have h := (hasGradientAt_meanFitnessMV hWm hWb hP μ).hasFDerivAt.log hw
  have hg : HasGradientAt (fun m => Real.log (meanFitnessMV W P m))
      ((meanFitnessMV W P μ)⁻¹ • toEuclideanCLM (𝕜 := ℝ) P⁻¹
        (∫ z, W z • (z - μ) ∂multivariateGaussian μ P)) μ := by
    rw [hasGradientAt_iff_hasFDerivAt, map_smul]
    exact h
  rw [hg.gradient, map_smul, selectionDifferentialMV]
  congr 1
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
    mul_nonsing_inv _ hP.det_pos.ne'.isUnit, map_one]
  rfl

end MathlibExt.Biology.StatisticalGenetics.SelectionGradient
