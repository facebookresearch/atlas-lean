/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.QuadraticFormCongruence
public import MathlibExt.Probability.Distributions.CochranTheorem
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# The Gaussian projection lemma

Let `Z ~ N(0, V)` on `EuclideanSpace ℝ ι` with `V` positive definite, and let `T` be a linear
subspace. The residual quadratic form `min_{u ∈ T} (Z - u)ᵀ V⁻¹ (Z - u)` has the chi-square law
with `c = card ι - dim T` degrees of freedom when `c > 0`. This finite-dimensional Gaussian lemma
(no asymptotics) motivates the chi-square reference laws of qp-style rank tests.

The statistic `gaussProjStat` is defined in whitened projection form: with `A = (√V)⁻¹` (through
`CFC.sqrt`), whitening sends `T` to the subspace `A '' T`, and the statistic is the squared norm
of the orthogonal projection of `A z` onto `(A '' T)ᗮ`. This form is continuous in `z` and needs
no choice of minimizer; `gaussProjStat_eq_iInf` identifies it with the minimum of the residual
quadratic form. Quadratic forms are Atlas's `QuadraticFormCongruence.quadForm`, `x ⬝ᵥ (A *ᵥ x)` on
coordinate vectors, applied to the coordinates `fun i => w i` of a Euclidean vector `w`. The
definitions are total in `V`, and every theorem assumes `V.PosDef`.

`chiSquareMeasure 0` is the zero measure (the gamma density at shape `0`), not the Dirac mass at
`0`. The codimension-zero endpoint `T = ⊤` is therefore stated separately, with the law
`Measure.dirac 0`, and the main law assumes positive codimension.

## Main results

* `gaussProjStat_eq_iInf`: the statistic is the minimum over `u ∈ T` of the residual quadratic
  form `quadForm V⁻¹ (fun i => (z - u) i)`, and the minimum is attained.
* `map_gaussProjStat_multivariateGaussian`: the Gaussian projection lemma, the chi-square law
  with `card ι - finrank ℝ T` degrees of freedom.
* `gaussProjStat_top`, `map_gaussProjStat_top`: for `T = ⊤` the statistic vanishes and its law is
  the Dirac mass at `0`.
* `gaussProjStat_bot`, `map_quadForm_multivariateGaussian`: for `T = ⊥` the statistic is the full
  quadratic form `zᵀ V⁻¹ z`, which is chi-square with `card ι` degrees of freedom.

## Implementation notes

`multivariateGaussian 0 V` is the standard Gaussian law pushed forward by `√V`, so the whitened
vector `A Z` is standard Gaussian and the statistic is the squared norm of an orthogonal
projection of it. Cochran's theorem in projection form
(`ProbabilityTheory.stdGaussian_map_norm_sq_starProjection`) then gives the law. The complement
`(A '' T)ᗮ` has dimension `card ι - finrank ℝ T` because `A` is injective.

## References

* W. G. Cochran, *The distribution of quadratic forms in a normal system, with applications to
  the analysis of covariance*, Proc. Cambridge Philos. Soc. 30 (1934), 178–191.
* C. R. Rao, *Linear Statistical Inference and its Applications*, 2nd ed., Wiley (1973),
  ch. 3b.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Module
open MathlibExt.LinearAlgebra.Matrix.QuadraticFormCongruence (quadForm)
open scoped RealInnerProductSpace MatrixOrder

namespace MathlibExt.Biology.PopulationGenetics.Admixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The whitening matrix of `V`: the inverse of the CFC square root `√V`.
Totalized as `(CFC.sqrt V)⁻¹` for arbitrary matrices: the square root of a matrix that is not
positive semidefinite is `0` and the inverse of a singular matrix is `0`, so the whitening matrix
is `0` unless `V` is positive definite, the intended domain. -/
noncomputable def whitening (V : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (CFC.sqrt V)⁻¹

/-- The Gaussian projection (residual) statistic in whitened form: with `A = whitening V`, the
squared norm of the orthogonal projection of `A z` onto `(A '' T)ᗮ`. When `V` is not positive
definite, `A = 0` and the statistic is `0`; the intended domain is positive definite `V`. -/
noncomputable def gaussProjStat (V : Matrix ι ι ℝ)
    (T : Submodule ℝ (EuclideanSpace ℝ ι)) (z : EuclideanSpace ℝ ι) : ℝ :=
  ‖(LinearMap.range ((Matrix.toEuclideanLin (whitening V)).comp
      T.subtype))ᗮ.starProjection
    (Matrix.toEuclideanLin (whitening V) z)‖ ^ 2

/-! ### Whitening -/

private lemma isUnit_det_sqrt {V : Matrix ι ι ℝ} (hV : V.PosDef) :
    IsUnit (CFC.sqrt V).det := by
  have hV' : V.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det V).mp hV.isUnit).ne_zero
  rw [← CFC.sqrt_mul_sqrt_self V hV.posSemidef.nonneg, Matrix.det_mul] at hV'
  exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul hV')

private lemma whitening_mul_sqrt {V : Matrix ι ι ℝ} (hV : V.PosDef) :
    whitening V * CFC.sqrt V = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_det_sqrt hV)

private lemma sqrt_mul_whitening {V : Matrix ι ι ℝ} (hV : V.PosDef) :
    CFC.sqrt V * whitening V = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_det_sqrt hV)

private lemma whitening_mul_whitening {V : Matrix ι ι ℝ} (hV : V.PosDef) :
    whitening V * whitening V = V⁻¹ := by
  rw [whitening, ← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self V hV.posSemidef.nonneg]

private lemma transpose_whitening (V : Matrix ι ι ℝ) : (whitening V)ᵀ = whitening V := by
  have h : (CFC.sqrt V)ᵀ = CFC.sqrt V := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg V)).isHermitian.eq
  rw [whitening, Matrix.transpose_nonsing_inv, h]

private lemma toEuclideanLin_mul_apply (A B : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    Matrix.toEuclideanLin A (Matrix.toEuclideanLin B x) = Matrix.toEuclideanLin (A * B) x := by
  rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply]

private lemma injective_toEuclideanLin_whitening {V : Matrix ι ι ℝ} (hV : V.PosDef) :
    Function.Injective (Matrix.toEuclideanLin (whitening V)) := by
  refine Function.LeftInverse.injective (g := Matrix.toEuclideanLin (CFC.sqrt V)) fun x => ?_
  rw [toEuclideanLin_mul_apply, sqrt_mul_whitening hV, Matrix.toLpLin_one, LinearMap.id_apply]

/-- The residual quadratic form is the squared norm of the whitened vector. -/
private lemma quadForm_inv_eq_norm_sq {V : Matrix ι ι ℝ} (hV : V.PosDef)
    (w : EuclideanSpace ℝ ι) :
    quadForm V⁻¹ (fun i => w i) = ‖Matrix.toEuclideanLin (whitening V) w‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, quadForm, ← whitening_mul_whitening hV,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    transpose_whitening]
  simp [dotProduct, Matrix.toLpLin_apply, pow_two]

private lemma quadForm_inv_nonneg {V : Matrix ι ι ℝ} (hV : V.PosDef) (w : EuclideanSpace ℝ ι) :
    0 ≤ quadForm V⁻¹ (fun i => w i) := by
  rw [quadForm_inv_eq_norm_sq hV]
  positivity

/-- Whitening `N(0, V)` gives the standard Gaussian law. -/
private lemma map_toEuclideanLin_whitening {V : Matrix ι ι ℝ} (hV : V.PosDef) :
    (multivariateGaussian 0 V).map (Matrix.toEuclideanLin (whitening V)) =
      stdGaussian (EuclideanSpace ℝ ι) := by
  have hcomp : (Matrix.toEuclideanLin (whitening V)) ∘
      (fun x => (0 : EuclideanSpace ℝ ι) + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt V) x) = id := by
    funext x
    ext i
    simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, whitening_mul_sqrt hV]
  rw [multivariateGaussian,
    Measure.map_map (LinearMap.continuous_of_finiteDimensional _).measurable (by fun_prop),
    hcomp, Measure.map_id]

/-! ### The whitened subspace -/

/-- The whitened image `A '' T` of `T`, as the range of `A ∘ T.subtype`. -/
private noncomputable def whitenedRange (V : Matrix ι ι ℝ)
    (T : Submodule ℝ (EuclideanSpace ℝ ι)) : Submodule ℝ (EuclideanSpace ℝ ι) :=
  LinearMap.range ((Matrix.toEuclideanLin (whitening V)).comp T.subtype)

private lemma gaussProjStat_eq_norm_sq (V : Matrix ι ι ℝ)
    (T : Submodule ℝ (EuclideanSpace ℝ ι)) (z : EuclideanSpace ℝ ι) :
    gaussProjStat V T z =
      ‖(whitenedRange V T)ᗮ.starProjection (Matrix.toEuclideanLin (whitening V) z)‖ ^ 2 :=
  rfl

private lemma finrank_orthogonal_whitenedRange {V : Matrix ι ι ℝ} (hV : V.PosDef)
    (T : Submodule ℝ (EuclideanSpace ℝ ι)) :
    finrank ℝ (whitenedRange V T)ᗮ = Fintype.card ι - finrank ℝ T := by
  have hinj : Function.Injective ((Matrix.toEuclideanLin (whitening V)).comp T.subtype) :=
    (injective_toEuclideanLin_whitening hV).comp T.injective_subtype
  have h1 := (whitenedRange V T).finrank_add_finrank_orthogonal
  have h2 : finrank ℝ (whitenedRange V T) = finrank ℝ T := LinearMap.finrank_range_of_inj hinj
  rw [h2, finrank_euclideanSpace] at h1
  omega

/-- Pythagoras for the projection onto `Kᗮ`: every `v ∈ K` lies at squared distance at least
`‖P_{Kᗮ} x‖²` from `x`. -/
private lemma norm_sq_starProjection_orthogonal_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Submodule ℝ E) [K.HasOrthogonalProjection] (x : E) {v : E}
    (hv : v ∈ K) : ‖Kᗮ.starProjection x‖ ^ 2 ≤ ‖x - v‖ ^ 2 := by
  have hsplit : x - v = (K.starProjection x - v) + Kᗮ.starProjection x := by
    rw [Submodule.starProjection_orthogonal_val]
    abel
  have horth : ⟪K.starProjection x - v, Kᗮ.starProjection x⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (K.sub_mem (K.starProjection_apply_mem x) hv)
      (Kᗮ.starProjection_apply_mem x)
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  rw [hsplit, sq, sq, h]
  nlinarith [mul_self_nonneg ‖K.starProjection x - v‖]

/-- The whitened statistic is a lower bound of the whitened residuals over `T`, attained at the
preimage of the projection onto the whitened subspace. -/
private lemma whitened_min (V : Matrix ι ι ℝ) (T : Submodule ℝ (EuclideanSpace ℝ ι))
    (x : EuclideanSpace ℝ ι) :
    (∀ u : T, ‖(whitenedRange V T)ᗮ.starProjection x‖ ^ 2 ≤
        ‖x - Matrix.toEuclideanLin (whitening V) u‖ ^ 2) ∧
      ∃ u : T, ‖(whitenedRange V T)ᗮ.starProjection x‖ ^ 2 =
        ‖x - Matrix.toEuclideanLin (whitening V) u‖ ^ 2 := by
  refine ⟨fun u => norm_sq_starProjection_orthogonal_le _ x
    (LinearMap.mem_range_self ((Matrix.toEuclideanLin (whitening V)).comp T.subtype) u), ?_⟩
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp ((whitenedRange V T).starProjection_apply_mem x)
  have hu' : Matrix.toEuclideanLin (whitening V) u = (whitenedRange V T).starProjection x := hu
  exact ⟨u, by rw [hu', Submodule.starProjection_orthogonal_val]⟩

/-! ### The statistic as a minimum -/

/-- For positive definite `V`, the whitened projection statistic is the minimum of the residual
quadratic form, and the minimum is attained. -/
theorem gaussProjStat_eq_iInf {V : Matrix ι ι ℝ} (hV : V.PosDef)
    (T : Submodule ℝ (EuclideanSpace ℝ ι)) (z : EuclideanSpace ℝ ι) :
    gaussProjStat V T z = ⨅ u : T, quadForm V⁻¹ (fun i => (z - (u : EuclideanSpace ℝ ι)) i) ∧
      ∃ u : EuclideanSpace ℝ ι, u ∈ T ∧
        gaussProjStat V T z = quadForm V⁻¹ (fun i => (z - u) i) := by
  have hq : ∀ u : EuclideanSpace ℝ ι, quadForm V⁻¹ (fun i => (z - u) i) =
      ‖Matrix.toEuclideanLin (whitening V) z - Matrix.toEuclideanLin (whitening V) u‖ ^ 2 :=
    fun u => by rw [quadForm_inv_eq_norm_sq hV, map_sub]
  obtain ⟨hle, u₀, hu₀⟩ := whitened_min V T (Matrix.toEuclideanLin (whitening V) z)
  have heq : gaussProjStat V T z = quadForm V⁻¹ (fun i => (z - (u₀ : EuclideanSpace ℝ ι)) i) := by
    rw [hq, gaussProjStat_eq_norm_sq]
    exact hu₀
  refine ⟨le_antisymm (le_ciInf fun u => ?_) ?_, u₀, u₀.2, heq⟩
  · rw [hq, gaussProjStat_eq_norm_sq]
    exact hle u
  · rw [heq]
    refine ciInf_le ⟨0, ?_⟩ u₀
    rintro _ ⟨u, rfl⟩
    exact quadForm_inv_nonneg hV _

/-! ### The chi-square law -/

/-- **Gaussian projection lemma.** If `Z ~ N(0, V)` with `V` positive definite
and `T` has codimension `c = card ι - finrank T > 0`, the residual statistic has
the chi-square law with `c` degrees of freedom. -/
theorem map_gaussProjStat_multivariateGaussian {V : Matrix ι ι ℝ} (hV : V.PosDef)
    (T : Submodule ℝ (EuclideanSpace ℝ ι))
    (hc : 0 < Fintype.card ι - finrank ℝ T) :
    (multivariateGaussian 0 V).map (gaussProjStat V T) =
      chiSquareMeasure (Fintype.card ι - finrank ℝ T) := by
  have hK := finrank_orthogonal_whitenedRange hV T
  have hfun : gaussProjStat V T =
      (fun y => ‖(whitenedRange V T)ᗮ.starProjection y‖ ^ 2) ∘
        Matrix.toEuclideanLin (whitening V) :=
    rfl
  rw [hfun, ← Measure.map_map (by fun_prop)
      (LinearMap.continuous_of_finiteDimensional _).measurable,
    map_toEuclideanLin_whitening hV,
    stdGaussian_map_norm_sq_starProjection (whitenedRange V T)ᗮ (hK ▸ hc), hK]

/-! ### Endpoints -/

/-- Endpoint `T = ⊤` (codimension `0`), for positive definite `V`: the statistic is identically
`0`, so its law under a probability measure is the Dirac mass at `0` (not `chiSquareMeasure 0`,
the zero measure). -/
theorem gaussProjStat_top {V : Matrix ι ι ℝ} (hV : V.PosDef)
    (z : EuclideanSpace ℝ ι) :
    gaussProjStat V ⊤ z = 0 := by
  obtain ⟨h, -⟩ := gaussProjStat_eq_iInf hV ⊤ z
  refine le_antisymm ?_ (by rw [gaussProjStat_eq_norm_sq]; positivity)
  rw [h]
  refine ciInf_le_of_le ⟨0, ?_⟩ ⟨z, Submodule.mem_top⟩ ?_
  · rintro _ ⟨u, rfl⟩
    exact quadForm_inv_nonneg hV _
  · change quadForm V⁻¹ (fun i => (z - z) i) ≤ 0
    rw [sub_self, quadForm_inv_eq_norm_sq hV, map_zero, norm_zero]
    norm_num

theorem map_gaussProjStat_top {V : Matrix ι ι ℝ} (hV : V.PosDef) :
    (multivariateGaussian 0 V).map (gaussProjStat V ⊤) = Measure.dirac 0 := by
  have hfun : gaussProjStat V ⊤ = fun _ => 0 := funext (gaussProjStat_top hV)
  rw [hfun, Measure.map_const, measure_univ, one_smul]

/-- Endpoint `T = ⊥`, for positive definite `V`: the statistic is the full quadratic form
`zᵀ V⁻¹ z`. -/
theorem gaussProjStat_bot {V : Matrix ι ι ℝ} (hV : V.PosDef)
    (z : EuclideanSpace ℝ ι) :
    gaussProjStat V ⊥ z = quadForm V⁻¹ (fun i => z i) := by
  obtain ⟨-, u, hu, h⟩ := gaussProjStat_eq_iInf hV ⊥ z
  rw [Submodule.mem_bot] at hu
  rw [h, hu, sub_zero]

/-- Endpoint `T = ⊥` (Hotelling form): for positive definite `V`, nonempty `ι` and
`Z ~ N(0, V)`, `Zᵀ V⁻¹ Z` has the chi-square law with `card ι` degrees of freedom. -/
theorem map_quadForm_multivariateGaussian {V : Matrix ι ι ℝ} (hV : V.PosDef)
    (hm : 0 < Fintype.card ι) :
    (multivariateGaussian 0 V).map (fun w => quadForm V⁻¹ (fun i => w i)) =
      chiSquareMeasure (Fintype.card ι) := by
  have hfun : (fun w : EuclideanSpace ℝ ι => quadForm V⁻¹ (fun i => w i)) = gaussProjStat V ⊥ :=
    funext fun z => (gaussProjStat_bot hV z).symm
  have h := map_gaussProjStat_multivariateGaussian hV ⊥ (by rwa [finrank_bot, Nat.sub_zero])
  rwa [finrank_bot, Nat.sub_zero, ← hfun] at h

end MathlibExt.Biology.PopulationGenetics.Admixture
