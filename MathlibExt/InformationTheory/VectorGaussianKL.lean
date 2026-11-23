/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.GaussianDensity
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Vector Gaussian KL divergence

The KL divergence between two multivariate Gaussians with
positive definite covariances is the standard trace/log-det
formula, computed through the canonical multivariate Gaussian
density from `MathlibExt.Probability.Distributions.GaussianDensity`
(imported, not copied). Equal covariances reduce it to half the
Mahalanobis term (`klDiv_multivariateGaussian_same_covariance`). A zero covariance, which is not
positive definite, gives a point mass and divergence `⊤`
(`klDiv_multivariateGaussian_zero_covariance`). Private `_of_density` variants take the
density theorem `MetaMathlibExt.multivariateGaussian_eq_withDensity` as a hypothesis and the public
theorems discharge it.

## References

* C. E. Rasmussen and C. K. I. Williams, *Gaussian Processes for Machine Learning*, MIT Press
  (2006), Appendix A.5, eq. (A.23) (KL divergence between two multivariate Gaussians, after
  S. Kullback, *Information Theory and Statistics*, Wiley (1959), §9.1).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal
namespace MathlibExt.InformationTheory.VectorGaussianKL

open _root_.InformationTheory

/-- The closed form of the Gaussian Kullback-Leibler divergence, in nats:
`(log (det T / det S) - n + trace (T⁻¹ * S) + (m - q)ᵀ T⁻¹ (m - q)) / 2`, `n = card ι`. -/
noncomputable def multivariateGaussianKLReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m q : EuclideanSpace ℝ ι) (S T : Matrix ι ι ℝ) : ℝ :=
  (Real.log (T.det / S.det) - (Fintype.card ι : ℝ) + (T⁻¹ * S).trace +
      ofLp (m - q) ⬝ᵥ T⁻¹ *ᵥ ofLp (m - q)) / 2

/-! ### Gaussian quadratic expectation (trace evaluation) -/

private lemma memLp_eval_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (c : ℝ) (i : ι) :
    MemLp (fun x : EuclideanSpace ℝ ι => x i - c) 2 (multivariateGaussian m S) := by
  have h := IsGaussian.memLp_dual (multivariateGaussian m S)
    (EuclideanSpace.proj (𝕜 := ℝ) i) 2 (by simp)
  exact h.sub (memLp_const c)

private lemma integral_eval_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (c : ℝ) (i : ι) :
    ∫ x, (x i - c) ∂(multivariateGaussian m S) = m i - c := by
  have hi : Integrable (fun x : EuclideanSpace ℝ ι => x i) (multivariateGaussian m S) :=
    IsGaussian.integrable_dual _ (EuclideanSpace.proj (𝕜 := ℝ) i)
  rw [integral_sub hi (integrable_const c), integral_const, probReal_univ, one_smul]
  have := (EuclideanSpace.proj (𝕜 := ℝ) (ι := ι) i).integral_comp_comm
    (IsGaussian.integrable_id (μ := multivariateGaussian m S))
  simp only [id, integral_id_multivariateGaussian] at this
  simpa using this

private lemma integral_eval_sub_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m q : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (i j : ι) :
    ∫ x, (x i - q i) * (x j - q j) ∂(multivariateGaussian m S) =
      S i j + (m i - q i) * (m j - q j) := by
  have h := covariance_eq_sub (memLp_eval_sub m S (q i) i) (memLp_eval_sub m S (q j) j)
  have hi : Integrable (fun x : EuclideanSpace ℝ ι => x i) (multivariateGaussian m S) :=
    IsGaussian.integrable_dual _ (EuclideanSpace.proj (𝕜 := ℝ) i)
  have hj : Integrable (fun x : EuclideanSpace ℝ ι => x j) (multivariateGaussian m S) :=
    IsGaussian.integrable_dual _ (EuclideanSpace.proj (𝕜 := ℝ) j)
  rw [covariance_sub_const_left hi, covariance_sub_const_right hj,
    covariance_eval_multivariateGaussian hS, integral_eval_sub, integral_eval_sub] at h
  simp only [Pi.mul_apply] at h
  linarith

private lemma quad_expand {ι : Type*} [Fintype ι] (v : ι → ℝ) (A : Matrix ι ι ℝ) :
    v ⬝ᵥ A *ᵥ v = ∑ i, ∑ j, A i j * (v i * v j) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Gaussian quadratic expectation: under `N(m, S)` with `S` positive semidefinite, for any real
matrix `A`, `E[(x - q)ᵀ A (x - q)] = trace (A * S) + (m - q)ᵀ A (m - q)`. Mean and covariance come
from Mathlib's `multivariateGaussian` API. -/
theorem integral_quadratic_multivariateGaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m q : EuclideanSpace ℝ ι) (S A : Matrix ι ι ℝ) (hS : S.PosSemidef) :
    ∫ x, ofLp (x - q) ⬝ᵥ A *ᵥ ofLp (x - q) ∂(multivariateGaussian m S) =
      (A * S).trace + ofLp (m - q) ⬝ᵥ A *ᵥ ofLp (m - q) := by
  have hint : ∀ i j, Integrable (fun x : EuclideanSpace ℝ ι =>
      A i j * (ofLp (x - q) i * ofLp (x - q) j)) (multivariateGaussian m S) := fun i j => by
    simp only [ofLp_sub, Pi.sub_apply]
    exact ((memLp_eval_sub m S (q i) i).integrable_mul (memLp_eval_sub m S (q j) j)).const_mul _
  have hterm : ∀ i j, ∫ x, A i j * (ofLp (x - q) i * ofLp (x - q) j) ∂(multivariateGaussian m S)
      = A i j * (S i j + (m i - q i) * (m j - q j)) := fun i j => by
    rw [integral_const_mul]
    simp only [ofLp_sub, Pi.sub_apply]
    rw [integral_eval_sub_mul m q S hS i j]
  simp_rw [quad_expand]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  simp_rw [integral_finsetSum _ fun j _ => hint _ j, hterm]
  have hsym : ∀ i j, S j i = S i j := fun i j => by
    simpa using hS.isHermitian.apply i j
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, ofLp_sub, Pi.sub_apply, mul_add,
    Finset.sum_add_distrib, hsym]

/-- Gaussian quadratic forms are integrable: under `N(m, S)` with `S` positive semidefinite,
`x ↦ (x - q)ᵀ A (x - q)` is integrable for any real matrix `A`. -/
theorem integrable_quadratic_multivariateGaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m q : EuclideanSpace ℝ ι) (S A : Matrix ι ι ℝ) (hS : S.PosSemidef) :
    Integrable (fun x => ofLp (x - q) ⬝ᵥ A *ᵥ ofLp (x - q)) (multivariateGaussian m S) := by
  have _ := hS
  simp_rw [quad_expand]
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  simp only [ofLp_sub, Pi.sub_apply]
  exact ((memLp_eval_sub m S (q i) i).integrable_mul (memLp_eval_sub m S (q j) j)).const_mul _

/-! ### KL density assembly -/

private lemma pdf_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (hS : S.PosDef) (x : EuclideanSpace ℝ ι) :
    0 < MetaMathlibExt.multivariateGaussianPDFReal m S x := by
  unfold MetaMathlibExt.multivariateGaussianPDFReal
  have := hS.det_pos
  positivity

private lemma log_pdf {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (hS : S.PosDef) (x : EuclideanSpace ℝ ι) :
    Real.log (MetaMathlibExt.multivariateGaussianPDFReal m S x) =
      -Real.log ((√(2 * Real.pi)) ^ Fintype.card ι) - Real.log S.det / 2 -
        ofLp (x - m) ⬝ᵥ S⁻¹ *ᵥ ofLp (x - m) / 2 := by
  unfold MetaMathlibExt.multivariateGaussianPDFReal
  have hd := hS.det_pos
  have h1 : 0 < (√(2 * Real.pi)) ^ Fintype.card ι := by positivity
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul (by positivity)
    (by positivity), Real.log_inv, Real.log_inv, Real.log_sqrt hd.le, Real.log_exp]
  ring

private lemma measurable_pdf {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    Measurable (MetaMathlibExt.multivariateGaussianPDFReal m S) := by
  unfold MetaMathlibExt.multivariateGaussianPDFReal
  fun_prop

/-- Pointwise log density ratio of two Gaussians with positive definite covariances:
`log (p_{m,S}(x) / p_{q,T}(x)) = (log (det T / det S) - (x - m)ᵀ S⁻¹ (x - m)
+ (x - q)ᵀ T⁻¹ (x - q)) / 2`. -/
theorem log_multivariateGaussianPDFReal_div {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m q : EuclideanSpace ℝ ι) (S T : Matrix ι ι ℝ) (hS : S.PosDef) (hT : T.PosDef)
    (x : EuclideanSpace ℝ ι) :
    Real.log (MetaMathlibExt.multivariateGaussianPDFReal m S x /
        MetaMathlibExt.multivariateGaussianPDFReal q T x) =
      (Real.log (T.det / S.det) - ofLp (x - m) ⬝ᵥ S⁻¹ *ᵥ ofLp (x - m) +
        ofLp (x - q) ⬝ᵥ T⁻¹ *ᵥ ofLp (x - q)) / 2 := by
  rw [Real.log_div (pdf_pos m S hS x).ne' (pdf_pos q T hT x).ne', log_pdf m S hS, log_pdf q T hT,
    Real.log_div hT.det_pos.ne' hS.det_pos.ne']
  ring

/-- Gaussians with positive definite covariances are absolutely continuous with respect to each
other; one direction: `N(m, S) ≪ N(q, T)`, given the shared density theorem at both laws. -/
private theorem multivariateGaussian_absolutelyContinuous_of_density {ι : Type*} [Fintype ι]
    [DecidableEq ι] (m q : EuclideanSpace ℝ ι) (S T : Matrix ι ι ℝ) (hT : T.PosDef)
    (hdS : multivariateGaussian m S =
      volume.withDensity fun x =>
        ENNReal.ofReal (MetaMathlibExt.multivariateGaussianPDFReal m S x))
    (hdT : multivariateGaussian q T =
      volume.withDensity fun x =>
        ENNReal.ofReal (MetaMathlibExt.multivariateGaussianPDFReal q T x)) :
    multivariateGaussian m S ≪ multivariateGaussian q T := by
  rw [hdS, hdT]
  refine (withDensity_absolutelyContinuous _ _).trans ?_
  refine withDensity_absolutelyContinuous' (measurable_pdf q T).ennreal_ofReal.aemeasurable ?_
  exact Filter.Eventually.of_forall fun x => by simpa using pdf_pos q T hT x

/-- The log-likelihood ratio of `N(m, S)` against `N(q, T)` is, `N(m, S)`-almost everywhere,
`(log (det T / det S) - (x - m)ᵀ S⁻¹ (x - m) + (x - q)ᵀ T⁻¹ (x - q)) / 2`. -/
private theorem llr_multivariateGaussian_ae_of_density {ι : Type*} [Fintype ι]
    [DecidableEq ι] (m q : EuclideanSpace ℝ ι) (S T : Matrix ι ι ℝ) (hS : S.PosDef) (hT : T.PosDef)
    (hdS : multivariateGaussian m S =
      volume.withDensity fun x =>
        ENNReal.ofReal (MetaMathlibExt.multivariateGaussianPDFReal m S x))
    (hdT : multivariateGaussian q T =
      volume.withDensity fun x =>
        ENNReal.ofReal (MetaMathlibExt.multivariateGaussianPDFReal q T x)) :
    llr (multivariateGaussian m S) (multivariateGaussian q T) =ᵐ[multivariateGaussian m S]
      fun x => (Real.log (T.det / S.det) - ofLp (x - m) ⬝ᵥ S⁻¹ *ᵥ ofLp (x - m) +
        ofLp (x - q) ⬝ᵥ T⁻¹ *ᵥ ofLp (x - q)) / 2 := by
  have hac : multivariateGaussian m S ≪ volume := by
    rw [hdS]; exact withDensity_absolutelyContinuous _ _
  have h1 := Measure.rnDeriv_withDensity (volume : Measure (EuclideanSpace ℝ ι))
    (measurable_pdf m S).ennreal_ofReal
  have h2 := Measure.rnDeriv_withDensity_right (multivariateGaussian m S)
    (volume : Measure (EuclideanSpace ℝ ι)) (measurable_pdf q T).ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall fun x => by simpa using pdf_pos q T hT x)
    (Filter.Eventually.of_forall fun x => by simp)
  rw [← hdT] at h2
  rw [← hdS] at h1
  filter_upwards [hac.ae_le h1, hac.ae_le h2] with x hx1 hx2
  rw [llr, hx2, hx1, ← log_multivariateGaussianPDFReal_div m q S T hS hT x]
  congr 1
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (pdf_pos q T hT x).le,
    ENNReal.toReal_ofReal (pdf_pos m S hS x).le, div_eq_inv_mul]

/-- The log-likelihood ratio of `N(m, S)` against `N(q, T)` is `N(m, S)`-integrable. -/
private theorem integrable_llr_multivariateGaussian_of_density {ι : Type*} [Fintype ι]
    [DecidableEq ι] (m q : EuclideanSpace ℝ ι) (S T : Matrix ι ι ℝ) (hS : S.PosDef) (hT : T.PosDef)
    (hdS : multivariateGaussian m S =
      volume.withDensity fun x =>
        ENNReal.ofReal (MetaMathlibExt.multivariateGaussianPDFReal m S x))
    (hdT : multivariateGaussian q T =
      volume.withDensity fun x =>
        ENNReal.ofReal (MetaMathlibExt.multivariateGaussianPDFReal q T x)) :
    Integrable (llr (multivariateGaussian m S) (multivariateGaussian q T))
      (multivariateGaussian m S) := by
  refine Integrable.congr ?_ (llr_multivariateGaussian_ae_of_density m q S T hS hT hdS hdT).symm
  have h1 := integrable_quadratic_multivariateGaussian m m S S⁻¹ hS.posSemidef
  have h2 := integrable_quadratic_multivariateGaussian m q S T⁻¹ hS.posSemidef
  exact (((integrable_const _).sub h1).add h2).div_const 2

/-! ### Headline -/

/-- Density-hypothesis form of `klDiv_multivariateGaussian`. For `n ≥ 1` and positive
definite covariances `S`, `T` on `EuclideanSpace ℝ ι` (`n = card ι`), given the shared density
theorem at both laws,
`KL(N(m, S) ‖ N(q, T)) =
ofReal ((log (det T / det S) - n + trace (T⁻¹ S) + (m - q)ᵀ T⁻¹ (m - q)) / 2)`.
-/
private theorem klDiv_multivariateGaussian_of_density {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (m q : EuclideanSpace ℝ ι) (S T : Matrix ι ι ℝ) (hS : S.PosDef) (hT : T.PosDef)
    (hdS : multivariateGaussian m S =
      volume.withDensity fun x =>
        ENNReal.ofReal (MetaMathlibExt.multivariateGaussianPDFReal m S x))
    (hdT : multivariateGaussian q T =
      volume.withDensity fun x =>
        ENNReal.ofReal (MetaMathlibExt.multivariateGaussianPDFReal q T x)) :
    klDiv (multivariateGaussian m S) (multivariateGaussian q T) =
      ENNReal.ofReal (multivariateGaussianKLReal m q S T) := by
  have hac := multivariateGaussian_absolutelyContinuous_of_density m q S T hT hdS hdT
  have hint := integrable_llr_multivariateGaussian_of_density m q S T hS hT hdS hdT
  rw [klDiv_of_ac_of_integrable hac hint, probReal_univ, probReal_univ, add_sub_cancel_right,
    integral_congr_ae (llr_multivariateGaussian_ae_of_density m q S T hS hT hdS hdT)]
  congr 1
  have h1 := integrable_quadratic_multivariateGaussian m m S S⁻¹ hS.posSemidef
  have h2 := integrable_quadratic_multivariateGaussian m q S T⁻¹ hS.posSemidef
  have hc : Integrable (fun _ : EuclideanSpace ℝ ι => Real.log (T.det / S.det))
      (multivariateGaussian m S) := integrable_const _
  have h3 : Integrable (fun a : EuclideanSpace ℝ ι => Real.log (T.det / S.det) -
      ofLp (a - m) ⬝ᵥ S⁻¹ *ᵥ ofLp (a - m)) (multivariateGaussian m S) := hc.sub h1
  rw [integral_div, integral_add h3 h2, integral_sub hc h1, integral_const,
    integral_quadratic_multivariateGaussian m m S S⁻¹ hS.posSemidef,
    integral_quadratic_multivariateGaussian m q S T⁻¹ hS.posSemidef,
    Matrix.nonsing_inv_mul S (isUnit_iff_ne_zero.mpr hS.det_pos.ne')]
  simp [multivariateGaussianKLReal]
  ring

/-! ### Validation -/

/-- Validation, `n = 1`: with `S = [s]`, `T = [t]` the closed form is the scalar Gaussian KL
formula `(log (t / s) - 1 + s / t + (m - q)² / t) / 2` (an identity for all real `s`, `t`). -/
theorem multivariateGaussianKLReal_fin_one (m q s t : ℝ) :
    multivariateGaussianKLReal (toLp 2 ![m]) (toLp 2 ![q]) (!![s] : Matrix (Fin 1) (Fin 1) ℝ)
        (!![t] : Matrix (Fin 1) (Fin 1) ℝ) =
      (Real.log (t / s) - 1 + s / t + (m - q) ^ 2 / t) / 2 := by
  simp [multivariateGaussianKLReal, Matrix.trace_fin_one]
  ring

/-- Validation, equal laws: the closed form vanishes at `q = m`, `T = S` for positive definite
`S`. -/
theorem multivariateGaussianKLReal_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (hS : S.PosDef) :
    multivariateGaussianKLReal m m S S = 0 := by
  have hdet : S.det ≠ 0 := hS.det_pos.ne'
  simp [multivariateGaussianKLReal, div_self hdet,
    Matrix.nonsing_inv_mul S (isUnit_iff_ne_zero.mpr hdet)]

/-- Equal covariances: for positive definite `S` the closed form at `T = S` is half the
Mahalanobis term, `(m - q)ᵀ S⁻¹ (m - q) / 2`. -/
theorem multivariateGaussianKLReal_same_covariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m q : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (hS : S.PosDef) :
    multivariateGaussianKLReal m q S S = ofLp (m - q) ⬝ᵥ S⁻¹ *ᵥ ofLp (m - q) / 2 := by
  have hdet : S.det ≠ 0 := hS.det_pos.ne'
  simp [multivariateGaussianKLReal, div_self hdet,
    Matrix.nonsing_inv_mul S (isUnit_iff_ne_zero.mpr hdet)]

/-- Validation, equal laws: both sides of the headline are zero at `q = m`, `T = S`. -/
theorem klDiv_multivariateGaussian_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (hS : S.PosDef) :
    klDiv (multivariateGaussian m S) (multivariateGaussian m S) =
      ENNReal.ofReal (multivariateGaussianKLReal m m S S) := by
  rw [klDiv_self, multivariateGaussianKLReal_self m S hS, ENNReal.ofReal_zero]

/-- Validation, nondiagonal covariance (closed form): `T = [[2,1],[1,2]]`, `S = 1`,
`m = (1, 0)`, `q = 0` give `(log 3 - 2 + 4/3 + 2/3) / 2 = log 3 / 2`. -/
theorem multivariateGaussianKLReal_nondiagonal :
    multivariateGaussianKLReal (toLp 2 ![1, 0]) 0 (1 : Matrix (Fin 2) (Fin 2) ℝ)
        !![2, 1; 1, 2] =
      Real.log 3 / 2 := by
  simp [multivariateGaussianKLReal, Matrix.det_fin_two_of, Matrix.inv_def,
    Matrix.adjugate_fin_two_of, Matrix.trace_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  norm_num
  ring

/-- The nondiagonal witness covariance `[[2,1],[1,2]]` is positive definite. -/
private lemma posDef_two_one_one_two : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      rw [not_or, not_ne_iff, not_ne_iff] at h
      exact hx (funext fun i => by fin_cases i <;> simp [h.1, h.2])
    simp only [star_trivial, dotProduct, mulVec, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    rcases hx' with h | h
    · have := pow_pos (abs_pos.mpr h) 2
      nlinarith [sq_nonneg (x 0 + x 1), sq_abs (x 0)]
    · have := pow_pos (abs_pos.mpr h) 2
      nlinarith [sq_nonneg (x 0 + x 1), sq_abs (x 1)]

/-- Validation, nondiagonal covariance (measure level, coordinate transport):
`KL(N((1,0), 1) ‖ N(0, [[2,1],[1,2]])) = ofReal (log 3 / 2)`, given the shared density theorem at
both laws. -/
private theorem klDiv_multivariateGaussian_nondiagonal_of_density
    (hdS : multivariateGaussian (toLp 2 ![1, 0]) (1 : Matrix (Fin 2) (Fin 2) ℝ) =
      volume.withDensity fun x => ENNReal.ofReal
        (MetaMathlibExt.multivariateGaussianPDFReal (toLp 2 ![1, 0]) 1 x))
    (hdT : multivariateGaussian 0 (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) =
      volume.withDensity fun x => ENNReal.ofReal
        (MetaMathlibExt.multivariateGaussianPDFReal 0 !![2, 1; 1, 2] x)) :
    klDiv (multivariateGaussian (toLp 2 ![1, 0]) (1 : Matrix (Fin 2) (Fin 2) ℝ))
        (multivariateGaussian 0 !![2, 1; 1, 2]) =
      ENNReal.ofReal (Real.log 3 / 2) := by
  rw [klDiv_multivariateGaussian_of_density _ _ _ _ Matrix.PosDef.one posDef_two_one_one_two
      hdS hdT,
    multivariateGaussianKLReal_nondiagonal]

/-- Violated premise (`S` positive definite): for `n ≥ 1` the zero covariance gives the point mass
`N(m, 0) = δ_m`, which is singular to `N(q, T)`, so the divergence is `⊤`. -/
private theorem klDiv_multivariateGaussian_zero_covariance_of_density {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (m q : EuclideanSpace ℝ ι) (T : Matrix ι ι ℝ)
    (hdT : multivariateGaussian q T =
      volume.withDensity fun x =>
        ENNReal.ofReal (MetaMathlibExt.multivariateGaussianPDFReal q T x)) :
    klDiv (multivariateGaussian m 0) (multivariateGaussian q T) = ∞ := by
  have h0 : multivariateGaussian m (0 : Matrix ι ι ℝ) = Measure.dirac m := by
    simp [multivariateGaussian, CFC.sqrt_zero]
  have hnac : ¬ multivariateGaussian m 0 ≪ multivariateGaussian q T := by
    intro hac
    have hvol : multivariateGaussian q T {m} = 0 := by
      rw [hdT]
      exact withDensity_absolutelyContinuous _ _ (by simp)
    have := hac hvol
    rw [h0] at this
    simp at this
  exact klDiv_of_not_ac hnac

/-! ### Density discharged

The public statements below supply the canonical density theorem
`MetaMathlibExt.multivariateGaussian_eq_withDensity` to the private `_of_density` variants. -/

/-- **Absolute continuity, density discharged.** Gaussians with positive definite covariances
satisfy `N(m, S) ≪ N(q, T)`. -/
theorem multivariateGaussian_absolutelyContinuous {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m q : EuclideanSpace ℝ ι) (S T : Matrix ι ι ℝ) (hS : S.PosDef) (hT : T.PosDef) :
    multivariateGaussian m S ≪ multivariateGaussian q T :=
  multivariateGaussian_absolutelyContinuous_of_density m q S T hT
    (MetaMathlibExt.multivariateGaussian_eq_withDensity m hS)
    (MetaMathlibExt.multivariateGaussian_eq_withDensity q hT)

/-- The log-likelihood ratio of `N(m, S)` against `N(q, T)` is, `N(m, S)`-almost everywhere,
`(log (det T / det S) - (x - m)ᵀ S⁻¹ (x - m) + (x - q)ᵀ T⁻¹ (x - q)) / 2`; density discharged. -/
theorem llr_multivariateGaussian_ae {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m q : EuclideanSpace ℝ ι) (S T : Matrix ι ι ℝ) (hS : S.PosDef) (hT : T.PosDef) :
    llr (multivariateGaussian m S) (multivariateGaussian q T) =ᵐ[multivariateGaussian m S]
      fun x => (Real.log (T.det / S.det) - ofLp (x - m) ⬝ᵥ S⁻¹ *ᵥ ofLp (x - m) +
        ofLp (x - q) ⬝ᵥ T⁻¹ *ᵥ ofLp (x - q)) / 2 :=
  llr_multivariateGaussian_ae_of_density m q S T hS hT
    (MetaMathlibExt.multivariateGaussian_eq_withDensity m hS)
    (MetaMathlibExt.multivariateGaussian_eq_withDensity q hT)

/-- The log-likelihood ratio of `N(m, S)` against `N(q, T)` is `N(m, S)`-integrable; density
discharged. -/
theorem integrable_llr_multivariateGaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m q : EuclideanSpace ℝ ι) (S T : Matrix ι ι ℝ) (hS : S.PosDef) (hT : T.PosDef) :
    Integrable (llr (multivariateGaussian m S) (multivariateGaussian q T))
      (multivariateGaussian m S) :=
  integrable_llr_multivariateGaussian_of_density m q S T hS hT
    (MetaMathlibExt.multivariateGaussian_eq_withDensity m hS)
    (MetaMathlibExt.multivariateGaussian_eq_withDensity q hT)

/-- **Kullback-Leibler divergence between multivariate Gaussians.** For `n ≥ 1` and positive
definite covariances `S`, `T` on `EuclideanSpace ℝ ι` (`n = card ι`),
`KL(N(m, S) ‖ N(q, T)) =
ofReal ((log (det T / det S) - n + trace (T⁻¹ S) + (m - q)ᵀ T⁻¹ (m - q)) / 2)`.
-/
theorem klDiv_multivariateGaussian {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (m q : EuclideanSpace ℝ ι) (S T : Matrix ι ι ℝ) (hS : S.PosDef) (hT : T.PosDef) :
    klDiv (multivariateGaussian m S) (multivariateGaussian q T) =
      ENNReal.ofReal (multivariateGaussianKLReal m q S T) :=
  klDiv_multivariateGaussian_of_density m q S T hS hT
    (MetaMathlibExt.multivariateGaussian_eq_withDensity m hS)
    (MetaMathlibExt.multivariateGaussian_eq_withDensity q hT)

/-- **Equal covariances.** For `n ≥ 1` and positive definite `S`, the divergence between Gaussians
with the same covariance is half the Mahalanobis term:
`KL(N(m, S) ‖ N(q, S)) = ofReal ((m - q)ᵀ S⁻¹ (m - q) / 2)`. Density discharged. -/
theorem klDiv_multivariateGaussian_same_covariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (m q : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (hS : S.PosDef) :
    klDiv (multivariateGaussian m S) (multivariateGaussian q S) =
      ENNReal.ofReal (ofLp (m - q) ⬝ᵥ S⁻¹ *ᵥ ofLp (m - q) / 2) := by
  rw [klDiv_multivariateGaussian m q S S hS hS, multivariateGaussianKLReal_same_covariance m q S hS]

/-- Validation, nondiagonal covariance (measure level, coordinate transport):
`KL(N((1,0), 1) ‖ N(0, [[2,1],[1,2]])) = ofReal (log 3 / 2)`; density discharged. -/
theorem klDiv_multivariateGaussian_nondiagonal :
    klDiv (multivariateGaussian (toLp 2 ![1, 0]) (1 : Matrix (Fin 2) (Fin 2) ℝ))
        (multivariateGaussian 0 !![2, 1; 1, 2]) =
      ENNReal.ofReal (Real.log 3 / 2) :=
  klDiv_multivariateGaussian_nondiagonal_of_density
    (MetaMathlibExt.multivariateGaussian_eq_withDensity _ Matrix.PosDef.one)
    (MetaMathlibExt.multivariateGaussian_eq_withDensity _ posDef_two_one_one_two)

/-- **Violated premise** (`S` positive definite): for `n ≥ 1` the zero covariance gives the point
mass `N(m, 0) = δ_m`, which is singular to `N(q, T)`, so
`KL(N(m, 0) ‖ N(q, T)) = ⊤`. Density discharged. -/
theorem klDiv_multivariateGaussian_zero_covariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (m q : EuclideanSpace ℝ ι) (T : Matrix ι ι ℝ) (hT : T.PosDef) :
    klDiv (multivariateGaussian m 0) (multivariateGaussian q T) = ∞ :=
  klDiv_multivariateGaussian_zero_covariance_of_density m q T
    (MetaMathlibExt.multivariateGaussian_eq_withDensity q hT)

/-- Corollary of `klDiv_multivariateGaussian_zero_covariance`: at the zero covariance the
divergence is not the finite closed form, so the positive-definiteness premise of
`klDiv_multivariateGaussian` cannot be dropped. -/
theorem klDiv_multivariateGaussian_zero_covariance_ne {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (m q : EuclideanSpace ℝ ι) (T : Matrix ι ι ℝ) (hT : T.PosDef) :
    klDiv (multivariateGaussian m 0) (multivariateGaussian q T) ≠
      ENNReal.ofReal (multivariateGaussianKLReal m q 0 T) := by
  rw [klDiv_multivariateGaussian_zero_covariance m q T hT]
  exact ENNReal.top_ne_ofReal

end MathlibExt.InformationTheory.VectorGaussianKL
