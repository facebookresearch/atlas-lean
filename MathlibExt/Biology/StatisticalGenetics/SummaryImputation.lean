/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.Positivity

/-!
# Gaussian imputation of summary statistics (ImpG)

ImpG (Pasaniuc et al. 2014) imputes the association `z`-score `z_t` of an untyped marker from
the `z`-scores `z_o` of typed markers. Under the null model the vector `(z_t, z_o)` is centred
with covariance given by the LD matrix, `Σ_oo = Cov(z_o)`, `Σ_to = Cov(z_t, z_o)`,
`Σ_tt = Var z_t` (`= 1`); the imputed statistic is the conditional mean
`ẑ_t = Σ_to Σ_oo⁻¹ z_o`, a fixed linear combination `wᵀ z_o` of the typed statistics, its
accuracy is measured from the linear-prediction residual variance
`Σ_tt - Σ_to Σ_oo⁻¹ Σ_ot` (for `Σ_tt = 1`,
`r²_pred = Σ_to Σ_oo⁻¹ Σ_ot`), which is the conditional variance only under the Gaussian
model. To account for sampling noise in the reference-panel LD, ImpG
replaces `Σ_oo` by `Σ_oo + λ I`, and normalizes the imputed statistic by its variance under the
null, `wᵀ Σ_oo w`, which is no longer `wᵀ Σ_ot`.

All of this is second-moment algebra and holds for every centred random vector, Gaussian or not;
we state it with raw second moments (`Model`). For a Gaussian vector the best linear predictor
is also the conditional expectation, and the conditional law is
`GaussianConditioning.condDistrib_multivariateGaussian`.

* `Model.integral_imputed_sq`, `Model.integral_imputed_mul`, `Model.integral_error_sq`: second
  moments of `ẑ = wᵀ z_o` and of the error `z_t - ẑ` for any weights `w`.
* `Model.integral_imputed_sq_of_normal`, `Model.integral_error_sq_of_normal`: for the ImpG
  weights (`Σ_oo w = Σ_ot`), `𝔼 ẑ² = wᵀ Σ_ot` (`= r²_pred`) and
  `𝔼 (z_t - ẑ)² = Σ_tt - wᵀ Σ_ot` (the linear-prediction residual variance; the conditional
  variance only under the Gaussian model).
* `Model.integral_error_sq_le`: the ImpG weights minimize the mean squared error among all linear
  imputations (best linear prediction); the excess error of `w'` is `(w' - w)ᵀ Σ_oo (w' - w)`.
* `Model.integral_normalized_sq`: for any weights, in particular the ridge weights solving
  `(Σ_oo + λ I) w = Σ_ot`, the statistic `ẑ / √(wᵀ Σ_oo w)` has second moment `1` under the
  null.

## Main results

* `Model`, `Model.imputed`.
* `Model.integral_imputed_sq`, `Model.integral_imputed_mul`, `Model.integral_error_sq`.
* `Model.integral_imputed_sq_of_normal`, `Model.integral_error_sq_of_normal`.
* `Model.integral_error_sq_eq`, `Model.integral_error_sq_le`.
* `Model.integral_normalized_sq`.

## References

* B. Pasaniuc, N. Zaitlen, H. Shi, G. Bhatia, A. Gusev, J. Pickrell, J. Hirschhorn,
  D. P. Strachan, N. Patterson, A. L. Price, *Fast and accurate imputation of summary statistics
  enhances evidence of functional enrichment*, Bioinformatics 30 (2014), 2906–2914.
-/

@[expose] public section

open MeasureTheory Matrix

namespace MathlibExt.Biology.StatisticalGenetics.SummaryImputation

variable {ι Ω : Type*} [Fintype ι] {m : MeasurableSpace Ω}

/-- Square-integrable statistics `z_t` (untyped marker) and `z_o` (typed markers) with raw second
moments `𝔼 z_o z_oᵀ = Σ_oo`, `𝔼 z_t z_o = Σ_ot`, `𝔼 z_t² = Σ_tt`. These are the covariances of
the ImpG null model when the statistics are centred. -/
structure Model (P : Measure Ω) (ι : Type*) where
  /-- The statistic of the untyped (target) marker. -/
  zt : Ω → ℝ
  /-- The statistics of the typed markers. -/
  zo : ι → Ω → ℝ
  /-- The target statistic is square integrable. -/
  memLp_zt : MemLp zt 2 P
  /-- The typed statistics are square integrable. -/
  memLp_zo : ∀ i, MemLp (zo i) 2 P
  /-- The LD (covariance) matrix `Σ_oo` among typed markers. -/
  sigmaOO : Matrix ι ι ℝ
  /-- The LD (covariance) vector `Σ_ot` between typed markers and the target. -/
  sigmaOT : ι → ℝ
  /-- The variance `Σ_tt` of the target statistic. -/
  sigmaTT : ℝ
  /-- `𝔼 z_o z_oᵀ = Σ_oo`. -/
  integral_zo_mul : ∀ i j, ∫ ω, zo i ω * zo j ω ∂P = sigmaOO i j
  /-- `𝔼 z_t z_o = Σ_ot`. -/
  integral_zt_mul : ∀ i, ∫ ω, zt ω * zo i ω ∂P = sigmaOT i
  /-- `𝔼 z_t² = Σ_tt`. -/
  integral_zt_sq : ∫ ω, zt ω ^ 2 ∂P = sigmaTT

namespace Model

variable {P : Measure Ω} (D : Model P ι)

/-- The imputed statistic `ẑ = wᵀ z_o` with weights `w`. -/
def imputed (w : ι → ℝ) (ω : Ω) : ℝ := ∑ i, w i * D.zo i ω

omit [Fintype ι] in
private theorem integrable_zo_mul (i j : ι) : Integrable (fun ω => D.zo i ω * D.zo j ω) P :=
  (D.memLp_zo i).integrable_mul (D.memLp_zo j)

omit [Fintype ι] in
private theorem integrable_zt_mul (i : ι) : Integrable (fun ω => D.zt ω * D.zo i ω) P :=
  D.memLp_zt.integrable_mul (D.memLp_zo i)

/-- `𝔼 ẑ² = wᵀ Σ_oo w`. -/
theorem integral_imputed_sq (w : ι → ℝ) :
    ∫ ω, D.imputed w ω ^ 2 ∂P = w ⬝ᵥ (D.sigmaOO *ᵥ w) := by
  have he (ω : Ω) : D.imputed w ω ^ 2 =
      ∑ i, ∑ j, (w i * w j) * (D.zo i ω * D.zo j ω) := by
    rw [imputed, pow_two, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [he]
  rw [integral_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => (D.integrable_zo_mul i j).const_mul _]
  simp_rw [integral_finsetSum _ fun j _ => (D.integrable_zo_mul _ j).const_mul _,
    integral_const_mul, D.integral_zo_mul]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `𝔼 ẑ z_t = wᵀ Σ_ot`. -/
theorem integral_imputed_mul (w : ι → ℝ) :
    ∫ ω, D.imputed w ω * D.zt ω ∂P = w ⬝ᵥ D.sigmaOT := by
  have he (ω : Ω) : D.imputed w ω * D.zt ω = ∑ i, w i * (D.zt ω * D.zo i ω) := by
    rw [imputed, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp_rw [he]
  rw [integral_finsetSum _ fun i _ => (D.integrable_zt_mul i).const_mul _]
  simp_rw [integral_const_mul, D.integral_zt_mul]
  rfl

private theorem memLp_imputed (w : ι → ℝ) : MemLp (D.imputed w) 2 P := by
  unfold imputed
  exact memLp_finsetSum _ fun i _ => (D.memLp_zo i).const_mul _

/-- The mean squared imputation error: `𝔼 (z_t - ẑ)² = Σ_tt - 2 wᵀ Σ_ot + wᵀ Σ_oo w`. -/
theorem integral_error_sq (w : ι → ℝ) :
    ∫ ω, (D.zt ω - D.imputed w ω) ^ 2 ∂P =
      D.sigmaTT - 2 * (w ⬝ᵥ D.sigmaOT) + w ⬝ᵥ (D.sigmaOO *ᵥ w) := by
  have h1 : Integrable (fun ω => D.zt ω ^ 2) P := D.memLp_zt.integrable_sq
  have h2 : Integrable (fun ω => D.imputed w ω * D.zt ω) P :=
    (D.memLp_imputed w).integrable_mul D.memLp_zt
  have h3 : Integrable (fun ω => D.imputed w ω ^ 2) P := (D.memLp_imputed w).integrable_sq
  have he (ω : Ω) : (D.zt ω - D.imputed w ω) ^ 2 =
      D.zt ω ^ 2 - 2 * (D.imputed w ω * D.zt ω) + D.imputed w ω ^ 2 := by ring
  simp_rw [he]
  have h12 : Integrable (fun ω => D.zt ω ^ 2 - 2 * (D.imputed w ω * D.zt ω)) P :=
    h1.sub (h2.const_mul 2)
  rw [integral_add h12 h3, integral_sub h1 (h2.const_mul 2), integral_const_mul,
    D.integral_zt_sq, D.integral_imputed_mul, D.integral_imputed_sq]

/-- For the ImpG weights (`Σ_oo w = Σ_ot`, i.e. `w = Σ_oo⁻¹ Σ_ot` when `Σ_oo` is invertible) the
imputed statistic has second moment `wᵀ Σ_ot = Σ_to Σ_oo⁻¹ Σ_ot`; for `Σ_tt = 1` this is
`1 -` the linear-prediction residual variance, ImpG's `r²_pred`. -/
theorem integral_imputed_sq_of_normal {w : ι → ℝ} (hw : D.sigmaOO *ᵥ w = D.sigmaOT) :
    ∫ ω, D.imputed w ω ^ 2 ∂P = w ⬝ᵥ D.sigmaOT := by
  rw [D.integral_imputed_sq, hw]

/-- For the ImpG weights (`Σ_oo w = Σ_ot`) the mean squared imputation error is
`Σ_tt - wᵀ Σ_ot = Σ_tt - Σ_to Σ_oo⁻¹ Σ_ot`, the linear-prediction residual variance
(the conditional variance only under the Gaussian ImpG model). -/
theorem integral_error_sq_of_normal {w : ι → ℝ} (hw : D.sigmaOO *ᵥ w = D.sigmaOT) :
    ∫ ω, (D.zt ω - D.imputed w ω) ^ 2 ∂P = D.sigmaTT - w ⬝ᵥ D.sigmaOT := by
  rw [D.integral_error_sq, hw]
  ring

omit [Fintype ι] in
/-- The moment matrix `Σ_oo` is symmetric. -/
theorem sigmaOO_transpose : D.sigmaOOᵀ = D.sigmaOO := by
  ext i j
  rw [transpose_apply, ← D.integral_zo_mul, ← D.integral_zo_mul]
  simp_rw [mul_comm]

/-- **Excess error of a linear imputation**: if `Σ_oo w = Σ_ot`, then for any weights `w'`,
`𝔼 (z_t - w'ᵀ z_o)² = 𝔼 (z_t - wᵀ z_o)² + (w' - w)ᵀ Σ_oo (w' - w)`. -/
theorem integral_error_sq_eq {w : ι → ℝ} (hw : D.sigmaOO *ᵥ w = D.sigmaOT) (w' : ι → ℝ) :
    ∫ ω, (D.zt ω - D.imputed w' ω) ^ 2 ∂P =
      ∫ ω, (D.zt ω - D.imputed w ω) ^ 2 ∂P + (w' - w) ⬝ᵥ (D.sigmaOO *ᵥ (w' - w)) := by
  have hsym : w ⬝ᵥ (D.sigmaOO *ᵥ w') = w' ⬝ᵥ (D.sigmaOO *ᵥ w) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, D.sigmaOO_transpose, dotProduct_comm]
  rw [D.integral_error_sq, D.integral_error_sq, ← hw]
  simp only [mulVec_sub, sub_dotProduct, dotProduct_sub, hsym]
  ring

/-- **ImpG is the best linear imputation**: the weights solving `Σ_oo w = Σ_ot` minimize the mean
squared error `𝔼 (z_t - w'ᵀ z_o)²` over all weights `w'`. -/
theorem integral_error_sq_le {w : ι → ℝ} (hw : D.sigmaOO *ᵥ w = D.sigmaOT) (w' : ι → ℝ) :
    ∫ ω, (D.zt ω - D.imputed w ω) ^ 2 ∂P ≤ ∫ ω, (D.zt ω - D.imputed w' ω) ^ 2 ∂P := by
  rw [D.integral_error_sq_eq hw w', le_add_iff_nonneg_right, ← D.integral_imputed_sq]
  exact integral_nonneg fun ω => sq_nonneg _

/-- **Normalized imputed statistic**: for any weights `w` with `wᵀ Σ_oo w > 0` (for example the
ridge weights solving `(Σ_oo + λ I) w = Σ_ot`), the statistic `ẑ / √(wᵀ Σ_oo w)` has second
moment `1`, so it has unit variance under the centred null. -/
theorem integral_normalized_sq (w : ι → ℝ) (hpos : 0 < w ⬝ᵥ (D.sigmaOO *ᵥ w)) :
    ∫ ω, (D.imputed w ω / Real.sqrt (w ⬝ᵥ (D.sigmaOO *ᵥ w))) ^ 2 ∂P = 1 := by
  simp_rw [div_pow, Real.sq_sqrt hpos.le]
  rw [integral_div, D.integral_imputed_sq, div_self hpos.ne']

end Model

end MathlibExt.Biology.StatisticalGenetics.SummaryImputation
