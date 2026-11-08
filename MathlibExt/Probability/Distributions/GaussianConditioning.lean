/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Gaussian conditioning

Conditional distributions of jointly Gaussian vectors, with Mathlib's `condDistrib` and
`multivariateGaussian`.

Main results:

* `noiseKernel`, `condDistrib_add_of_indepFun`: **a signal in independent additive noise**: if `Z`
  is independent of `Y`, the conditional distribution of `f Y + Z` given `Y = y` is the law of
  `f y + Z` (any laws).
* `condDistrib_of_hasGaussianLaw`: **Gaussian conditioning** on finite-dimensional Hilbert spaces:
  if `(X, Y)` is jointly Gaussian and the residual `X - A Y` of a linear map `A` is uncorrelated
  with `Y` (the normal equations), then the residual is Gaussian and independent of `Y`, and
  `X | Y = y` is the law of `A y + (X - A Y)`.
* `map_toEuclideanLin_multivariateGaussian`: linear images, `M · N(μ, S) = N(M μ, M S Mᵀ)`;
  `map_add_multivariateGaussian`: translations.
* `condDistrib_multivariateGaussian`: **the Schur-complement formula**: if `(X, Y) ~ N(μ, S)` with
  blocks `S₁₁, S₁₂, S₂₁, S₂₂` and `S₂₂` invertible, then for almost every `y`,
  `X | Y = y ~ N(μ_X + S₁₂ S₂₂⁻¹ (y - μ_Y), S₁₁ - S₁₂ S₂₂⁻¹ S₂₁)`. The blocks of a vector on
  `ι ⊕ κ` are read with `blockRow`.
* `posSemidef_fromBlocks_zero`, `inner_sumEquivProd_symm`, `charFun_map_sumEquivProd_symm_prod`,
  `map_sumEquivProd_symm_prod_multivariateGaussian`, `map_sumEquivProd_symm_of_indepFun`:
  **independent Gaussian blocks** `N(m, S)` and `N(m', R)` concatenate (with Mathlib's
  `EuclideanSpace.sumEquivProd`) to `N((m, m'), [[S, 0], [0, R]])`. This turns a model written
  with independent Gaussian noise into one joint Gaussian, to which the conditioning formula
  applies.
* Linear-Gaussian models (Bishop, *Pattern Recognition and Machine Learning*, Section 2.3.3), for
  a state `x ~ N(m, S)` observed linearly in independent Gaussian noise:
  `map_linear_add_of_indepFun`, **the marginal** `F x + w ~ N(F m + c, F S Fᵀ + Q)`;
  `posSemidef_fromBlocks_linear`, `posSemidef_sub_mul_inv_mul`, the joint and posterior
  covariances are positive semidefinite; `condDistrib_linear_add_of_indepFun`, **Bayes' theorem**:
  given `y = H x + v` with `v ~ N(0, R)` and `H S Hᵀ + R` invertible,
  `x | y ~ N(m + S Hᵀ (H S Hᵀ + R)⁻¹ (y - H m), S - S Hᵀ (H S Hᵀ + R)⁻¹ H S)`. The proof
  concatenates `(x, v)`, maps it to `(x, y)` by `[[1, 0], [H, 1]]`, and applies the
  Schur-complement formula.
-/

@[expose] public section

set_option autoImplicit false

namespace MetaMathlibExt

open MeasureTheory ProbabilityTheory

section Noise

variable {Ω E F : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd₂ E] [MeasurableSpace F]

/-- The kernel `y ↦ law of f y + Z`, for `Z ~ ν`. -/
noncomputable def noiseKernel (f : F → E) (hf : Measurable f) (ν : Measure E) : Kernel F E :=
  (Kernel.deterministic f hf ×ₖ Kernel.const F ν).map fun p => p.1 + p.2

instance (f : F → E) (hf : Measurable f) (ν : Measure E) [IsProbabilityMeasure ν] :
    IsMarkovKernel (noiseKernel f hf ν) := by
  unfold noiseKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

theorem noiseKernel_apply (f : F → E) (hf : Measurable f) (ν : Measure E)
    [IsProbabilityMeasure ν] (y : F) : noiseKernel f hf ν y = ν.map (f y + ·) := by
  rw [noiseKernel, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.deterministic_apply,
    Kernel.const_apply, Measure.dirac_prod, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- **Conditioning on a signal observed in independent additive noise**: if `Z` is independent of
`Y`, the conditional distribution of `f Y + Z` given `Y = y` is the law of `f y + Z`. -/
theorem condDistrib_add_of_indepFun [StandardBorelSpace E] [Nonempty E] {Y : Ω → F} {Z : Ω → E}
    (hY : Measurable Y) (hZ : Measurable Z) (hind : IndepFun Y Z P) {f : F → E}
    (hf : Measurable f) :
    condDistrib (fun ω => f (Y ω) + Z ω) Y P =ᵐ[P.map Y] noiseKernel f hf (P.map Z) := by
  have : IsProbabilityMeasure (P.map Z) :=
    (Measure.isProbabilityMeasure_map_iff hZ.aemeasurable).2 inferInstance
  refine condDistrib_ae_eq_of_measure_eq_compProd hY.aemeasurable (by fun_prop) ?_
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable).1 hind
  have hg : Measurable fun p : F × E => (p.1, f p.1 + p.2) := by fun_prop
  have hmap : P.map (fun ω => (Y ω, f (Y ω) + Z ω)) =
      (P.map fun ω => (Y ω, Z ω)).map fun p => (p.1, f p.1 + p.2) := by
    rw [Measure.map_map hg (by fun_prop)]
    rfl
  rw [hmap, hprod]
  ext s hs
  rw [Measure.map_apply hg hs, Measure.prod_apply (hg hs), Measure.compProd_apply hs]
  refine lintegral_congr fun y => ?_
  rw [noiseKernel_apply, Measure.map_apply (by fun_prop) (measurable_prodMk_left hs)]
  rfl

end Noise

section Gaussian

open scoped RealInnerProductSpace

variable {Ω E F : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
  [BorelSpace F]

/-- **Gaussian conditioning**: let `(X, Y)` be jointly Gaussian and `A` a linear map whose residual
`X - A Y` is uncorrelated with `Y` (the normal equations). Then `X - A Y` is a Gaussian
independent of `Y`, and the conditional distribution of `X` given `Y = y` is the law of
`A y + (X - A Y)`. -/
theorem condDistrib_of_hasGaussianLaw {X : Ω → E} {Y : Ω → F} (hX : Measurable X)
    (hY : Measurable Y) (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P) (A : F →L[ℝ] E)
    (hA : ∀ x y, cov[fun ω => ⟪x, X ω - A (Y ω)⟫, fun ω => ⟪y, Y ω⟫; P] = 0) :
    HasGaussianLaw (fun ω => X ω - A (Y ω)) P ∧
      IndepFun (fun ω => X ω - A (Y ω)) Y P ∧
      condDistrib X Y P =ᵐ[P.map Y]
        noiseKernel A A.continuous.measurable (P.map fun ω => X ω - A (Y ω)) := by
  set L : E × F →L[ℝ] E × F :=
    ((ContinuousLinearMap.fst ℝ E F) - A.comp (ContinuousLinearMap.snd ℝ E F)).prod
      (ContinuousLinearMap.snd ℝ E F)
  have hZY : HasGaussianLaw (fun ω => (X ω - A (Y ω), Y ω)) P := hXY.map_fun L
  have hind : IndepFun (fun ω => X ω - A (Y ω)) Y P := hZY.indepFun_of_covariance_inner hA
  have hZ : HasGaussianLaw (fun ω => X ω - A (Y ω)) P := hZY.fst
  refine ⟨hZ, hind, ?_⟩
  have hXeq : X = fun ω => A (Y ω) + (X ω - A (Y ω)) := by
    funext ω; abel
  have hcd := condDistrib_add_of_indepFun hY (by fun_prop) hind.symm A.continuous.measurable
  rw [← hXeq] at hcd
  exact hcd

end Gaussian

section LinearImage

open Matrix WithLp
open scoped RealInnerProductSpace MatrixOrder

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem inner_toEuclideanLin (M : Matrix ι κ ℝ) (t : EuclideanSpace ℝ ι)
    (z : EuclideanSpace ℝ κ) : ⟪toEuclideanLin M z, t⟫ = ⟪z, toEuclideanLin Mᵀ t⟫ := by
  rw [← conjTranspose_eq_transpose_of_trivial, toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_right]

omit [Fintype ι] [DecidableEq ι] in
theorem continuous_toEuclideanLin [Finite ι] (M : Matrix ι κ ℝ) : Continuous (toEuclideanLin M) :=
  have := Fintype.ofFinite ι
  LinearMap.continuous_of_finiteDimensional _

/-- **Linear images of multivariate Gaussians**: `M · N(μ, S) = N(M μ, M S Mᵀ)`. -/
theorem map_toEuclideanLin_multivariateGaussian (M : Matrix ι κ ℝ) (μ : EuclideanSpace ℝ κ)
    {S : Matrix κ κ ℝ} (hS : S.PosSemidef) :
    (multivariateGaussian μ S).map (toEuclideanLin M) =
      multivariateGaussian (toEuclideanLin M μ) (M * S * Mᵀ) := by
  have hMS : (M * S * Mᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hS.mul_mul_conjTranspose_same M
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_apply, integral_map (continuous_toEuclideanLin M).aemeasurable (by fun_prop)]
  simp_rw [inner_toEuclideanLin]
  rw [← charFun_apply, charFun_multivariateGaussian hS, charFun_multivariateGaussian hMS]
  have hq : ofLp (toEuclideanLin Mᵀ t) ⬝ᵥ S *ᵥ ofLp (toEuclideanLin Mᵀ t) =
      ofLp t ⬝ᵥ (M * S * Mᵀ) *ᵥ ofLp t := by
    change (Mᵀ *ᵥ ofLp t) ⬝ᵥ S *ᵥ (Mᵀ *ᵥ ofLp t) = _
    rw [mulVec_transpose, ← dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, mulVec_mulVec]
  rw [hq, real_inner_comm, ← inner_toEuclideanLin, real_inner_comm]

/-- Translating a multivariate Gaussian translates its mean. -/
theorem map_add_multivariateGaussian (c μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    (multivariateGaussian μ S).map (c + ·) = multivariateGaussian (c + μ) S := by
  rw [multivariateGaussian, multivariateGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp [add_assoc]

/-- The matrix `[P Q]` with columns indexed by `ι ⊕ κ`. -/
def blockRow {ρ : Type*} (P : Matrix ρ ι ℝ) (Q : Matrix ρ κ ℝ) : Matrix ρ (ι ⊕ κ) ℝ :=
  Matrix.of fun r => Sum.elim (P r) (Q r)

omit [DecidableEq ι] [DecidableEq κ] in
theorem blockRow_mul_mul_transpose {ρ ρ' : Type*} (P : Matrix ρ ι ℝ)
    (Q : Matrix ρ κ ℝ) (P' : Matrix ρ' ι ℝ) (Q' : Matrix ρ' κ ℝ) (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) :
    blockRow P Q * S * (blockRow P' Q')ᵀ =
      P * S.toBlocks₁₁ * P'ᵀ + P * S.toBlocks₁₂ * Q'ᵀ + Q * S.toBlocks₂₁ * P'ᵀ +
        Q * S.toBlocks₂₂ * Q'ᵀ := by
  ext r r'
  simp only [blockRow, mul_apply, Fintype.sum_sum_type, of_apply, Sum.elim_inl, Sum.elim_inr,
    transpose_apply, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, Matrix.add_apply,
    Finset.sum_add_distrib, add_mul, Finset.sum_mul]
  ring

end LinearImage

section Schur

open Matrix WithLp
open scoped RealInnerProductSpace MatrixOrder

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- Covariances of linear functionals of a multivariate Gaussian vector. -/
theorem covariance_inner_of_map_eq {ν : Type*} [Fintype ν] [DecidableEq ν]
    {V : Ω → EuclideanSpace ℝ ν} (hV : Measurable V) {μ : EuclideanSpace ℝ ν}
    {S : Matrix ν ν ℝ} (hS : S.PosSemidef) (hlaw : P.map V = multivariateGaussian μ S)
    (a b : EuclideanSpace ℝ ν) :
    cov[fun ω => ⟪a, V ω⟫, fun ω => ⟪b, V ω⟫; P] = ofLp a ⬝ᵥ S *ᵥ ofLp b := by
  have h := covarianceBilin_multivariateGaussian (μ := μ) hS a b
  rw [← hlaw, covarianceBilin_apply_eq_cov (by rw [hlaw]; exact IsGaussian.memLp_two_id),
    covariance_map (by fun_prop) (by fun_prop) hV.aemeasurable] at h
  exact h

/-- **Gaussian conditioning (Schur complement)**: let `V = (X, Y)` have law `N(μ, S)` with blocks
`S₁₁, S₁₂, S₂₁, S₂₂` and `S₂₂` invertible. Then for almost every `y`, the conditional distribution
of `X` given `Y = y` is `N(μ_X + S₁₂ S₂₂⁻¹ (y - μ_Y), S₁₁ - S₁₂ S₂₂⁻¹ S₂₁)`. -/
theorem condDistrib_multivariateGaussian {V : Ω → EuclideanSpace ℝ (ι ⊕ κ)} (hV : Measurable V)
    {μ : EuclideanSpace ℝ (ι ⊕ κ)} {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ} (hS : S.PosSemidef)
    (hlaw : P.map V = multivariateGaussian μ S) (hYY : IsUnit S.toBlocks₂₂.det) :
    ∀ᵐ y ∂P.map (fun ω => toEuclideanLin (blockRow (0 : Matrix κ ι ℝ) 1) (V ω)),
      condDistrib (fun ω => toEuclideanLin (blockRow (1 : Matrix ι ι ℝ) 0) (V ω))
          (fun ω => toEuclideanLin (blockRow (0 : Matrix κ ι ℝ) 1) (V ω)) P y =
        multivariateGaussian
          (toEuclideanLin (blockRow (1 : Matrix ι ι ℝ) 0) μ +
            toEuclideanLin (S.toBlocks₁₂ * S.toBlocks₂₂⁻¹)
              (y - toEuclideanLin (blockRow (0 : Matrix κ ι ℝ) 1) μ))
          (S.toBlocks₁₁ - S.toBlocks₁₂ * S.toBlocks₂₂⁻¹ * S.toBlocks₂₁) := by
  set Mx : Matrix ι (ι ⊕ κ) ℝ := blockRow 1 0 with hMx
  set My : Matrix κ (ι ⊕ κ) ℝ := blockRow 0 1 with hMy
  set A : Matrix ι κ ℝ := S.toBlocks₁₂ * S.toBlocks₂₂⁻¹ with hAdef
  set Mz : Matrix ι (ι ⊕ κ) ℝ := blockRow 1 (-A) with hMz
  set Acl : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ι :=
    LinearMap.toContinuousLinearMap (toEuclideanLin A) with hAcl
  have hAS : A * S.toBlocks₂₂ = S.toBlocks₁₂ := by
    rw [hAdef, Matrix.mul_assoc, nonsing_inv_mul _ hYY, Matrix.mul_one]
  have hMzeq : Mz = Mx - A * My := by
    ext i a
    cases a <;> simp [hMz, hMx, hMy, blockRow, mul_apply, Matrix.one_apply]
  have hZ : ∀ ω, toEuclideanLin Mx (V ω) - Acl (toEuclideanLin My (V ω)) =
      toEuclideanLin Mz (V ω) := by
    intro ω
    apply WithLp.ofLp_injective
    change Mx *ᵥ ofLp (V ω) - A *ᵥ (My *ᵥ ofLp (V ω)) = Mz *ᵥ ofLp (V ω)
    rw [hMzeq, sub_mulVec, mulVec_mulVec]
  -- `(X, Y)` is jointly Gaussian
  have : IsGaussian (P.map V) := by rw [hlaw]; infer_instance
  have hVG : HasGaussianLaw V P := IsGaussian.hasGaussianLaw hV.aemeasurable
  have hXY : HasGaussianLaw (fun ω => (toEuclideanLin Mx (V ω), toEuclideanLin My (V ω))) P :=
    hVG.map_fun ((LinearMap.toContinuousLinearMap (toEuclideanLin Mx)).prod
      (LinearMap.toContinuousLinearMap (toEuclideanLin My)))
  have hXm : Measurable fun ω => toEuclideanLin Mx (V ω) :=
    (continuous_toEuclideanLin Mx).measurable.comp hV
  have hYm : Measurable fun ω => toEuclideanLin My (V ω) :=
    (continuous_toEuclideanLin My).measurable.comp hV
  -- the normal equations
  have hzy : Mz * S * Myᵀ = 0 := by
    rw [hMz, hMy, blockRow_mul_mul_transpose]
    simp only [transpose_zero, transpose_one, Matrix.mul_zero, Matrix.mul_one, Matrix.one_mul,
      Matrix.neg_mul, hAS, zero_add, add_zero, add_neg_cancel]
  have hnorm : ∀ x y, cov[fun ω => ⟪x, toEuclideanLin Mx (V ω) - Acl (toEuclideanLin My (V ω))⟫,
      fun ω => ⟪y, toEuclideanLin My (V ω)⟫; P] = 0 := by
    intro x y
    have h1 : ∀ ω, ⟪x, toEuclideanLin Mx (V ω) - Acl (toEuclideanLin My (V ω))⟫ =
        ⟪toEuclideanLin Mzᵀ x, V ω⟫ := fun ω => by
      rw [hZ, real_inner_comm, inner_toEuclideanLin, real_inner_comm]
    have h2 : ∀ ω, ⟪y, toEuclideanLin My (V ω)⟫ = ⟪toEuclideanLin Myᵀ y, V ω⟫ := fun ω => by
      rw [real_inner_comm, inner_toEuclideanLin, real_inner_comm]
    simp_rw [h1, h2]
    rw [covariance_inner_of_map_eq hV hS hlaw]
    change (Mzᵀ *ᵥ ofLp x) ⬝ᵥ S *ᵥ (Myᵀ *ᵥ ofLp y) = 0
    rw [mulVec_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hzy, zero_mulVec,
      dotProduct_zero]
  obtain ⟨-, -, hcd⟩ := condDistrib_of_hasGaussianLaw hXm hYm hXY Acl hnorm
  -- the law of the residual
  have hzz : Mz * S * Mzᵀ = S.toBlocks₁₁ - A * S.toBlocks₂₁ := by
    rw [hMz, blockRow_mul_mul_transpose]
    have : A * S.toBlocks₂₂ * Aᵀ = S.toBlocks₁₂ * Aᵀ := by rw [hAS]
    simp only [transpose_one, transpose_neg, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
      Matrix.neg_mul, neg_neg, this]
    abel
  have hlawZ : P.map (fun ω => toEuclideanLin Mx (V ω) - Acl (toEuclideanLin My (V ω))) =
      multivariateGaussian (toEuclideanLin Mz μ) (S.toBlocks₁₁ - A * S.toBlocks₂₁) := by
    simp_rw [hZ]
    rw [← hzz, ← map_toEuclideanLin_multivariateGaussian Mz μ hS, ← hlaw,
      Measure.map_map (continuous_toEuclideanLin Mz).measurable hV]
    rfl
  filter_upwards [hcd] with y hy
  rw [hy, noiseKernel_apply, hlawZ, map_add_multivariateGaussian]
  congr 1
  apply WithLp.ofLp_injective
  change A *ᵥ ofLp y + Mz *ᵥ ofLp μ = Mx *ᵥ ofLp μ + A *ᵥ (ofLp y - My *ᵥ ofLp μ)
  rw [hMzeq, sub_mulVec, mulVec_sub, mulVec_mulVec]
  abel

end Schur

section Blocks

/-! ### Independent Gaussian blocks -/

open Matrix WithLp Complex
open scoped RealInnerProductSpace MatrixOrder

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
/-- A block-diagonal matrix of positive semidefinite blocks is positive semidefinite. -/
theorem posSemidef_fromBlocks_zero [Finite ι] [Finite κ] {S : Matrix ι ι ℝ} {R : Matrix κ κ ℝ}
    (hS : S.PosSemidef) (hR : R.PosSemidef) : (fromBlocks S 0 0 R).PosSemidef := by
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  rw [posSemidef_iff_dotProduct_mulVec] at hS hR ⊢
  refine ⟨?_, fun x => ?_⟩
  · have hS' : Sᵀ = S := by simpa [conjTranspose_eq_transpose_of_trivial] using hS.1.eq
    have hR' : Rᵀ = R := by simpa [conjTranspose_eq_transpose_of_trivial] using hR.1.eq
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, fromBlocks_transpose, hS', hR',
      transpose_zero, transpose_zero]
  · have hx : x = Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) := by
      funext a; cases a <;> rfl
    rw [hx, fromBlocks_mulVec]
    simp only [zero_mulVec, add_zero, zero_add, Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [show star (Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr)) =
      Sum.elim (star (x ∘ Sum.inl)) (star (x ∘ Sum.inr)) from by
        funext a; cases a <;> rfl, sumElim_dotProduct_sumElim]
    exact add_nonneg (hS.2 _) (hR.2 _)

omit [DecidableEq ι] [DecidableEq κ] in
/-- The inner product splits over the blocks of `EuclideanSpace.sumEquivProd`. -/
theorem inner_sumEquivProd_symm (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)
    (t : EuclideanSpace ℝ (ι ⊕ κ)) :
    ⟪(EuclideanSpace.sumEquivProd (𝕜 := ℝ)).symm p, t⟫ =
      ⟪p.1, (EuclideanSpace.sumEquivProd (𝕜 := ℝ) t).1⟫ +
        ⟪p.2, (EuclideanSpace.sumEquivProd (𝕜 := ℝ) t).2⟫ := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fintype.sum_sum_type]

omit [DecidableEq ι] [DecidableEq κ] in
/-- The characteristic function of a concatenation of independent blocks is the product of the
blocks' characteristic functions. -/
theorem charFun_map_sumEquivProd_symm_prod (μ : Measure (EuclideanSpace ℝ ι))
    (ν : Measure (EuclideanSpace ℝ κ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (t : EuclideanSpace ℝ (ι ⊕ κ)) :
    charFun ((μ.prod ν).map (EuclideanSpace.sumEquivProd (𝕜 := ℝ)).symm) t =
      charFun μ (EuclideanSpace.sumEquivProd (𝕜 := ℝ) t).1 *
        charFun ν (EuclideanSpace.sumEquivProd (𝕜 := ℝ) t).2 := by
  rw [charFun_apply, integral_map
    (EuclideanSpace.sumEquivProd (𝕜 := ℝ)).symm.continuous.aemeasurable (by fun_prop)]
  simp_rw [inner_sumEquivProd_symm, ofReal_add, add_mul, Complex.exp_add]
  rw [integral_prod_mul (fun a => cexp (⟪a, (EuclideanSpace.sumEquivProd (𝕜 := ℝ) t).1⟫ * I))
    (fun b => cexp (⟪b, (EuclideanSpace.sumEquivProd (𝕜 := ℝ) t).2⟫ * I)), charFun_apply,
    charFun_apply]

/-- **Independent Gaussian blocks**: concatenating independent blocks `N(m, S)` and `N(m', R)`
gives `N((m, m'), [[S, 0], [0, R]])`. -/
theorem map_sumEquivProd_symm_prod_multivariateGaussian (m : EuclideanSpace ℝ ι)
    (m' : EuclideanSpace ℝ κ) {S : Matrix ι ι ℝ} {R : Matrix κ κ ℝ} (hS : S.PosSemidef)
    (hR : R.PosSemidef) :
    ((multivariateGaussian m S).prod (multivariateGaussian m' R)).map
        (EuclideanSpace.sumEquivProd (𝕜 := ℝ)).symm =
      multivariateGaussian ((EuclideanSpace.sumEquivProd (𝕜 := ℝ)).symm (m, m'))
        (fromBlocks S 0 0 R) := by
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_map_sumEquivProd_symm_prod, charFun_multivariateGaussian hS,
    charFun_multivariateGaussian hR,
    charFun_multivariateGaussian (posSemidef_fromBlocks_zero hS hR), ← Complex.exp_add]
  congr 1
  have h1 : ⟪t, (EuclideanSpace.sumEquivProd (𝕜 := ℝ)).symm (m, m')⟫ =
      ⟪(EuclideanSpace.sumEquivProd (𝕜 := ℝ) t).1, m⟫ +
        ⟪(EuclideanSpace.sumEquivProd (𝕜 := ℝ) t).2, m'⟫ := by
    rw [real_inner_comm, inner_sumEquivProd_symm, real_inner_comm, real_inner_comm m']
  have h2 : ofLp t ⬝ᵥ fromBlocks S 0 0 R *ᵥ ofLp t =
      ofLp (EuclideanSpace.sumEquivProd (𝕜 := ℝ) t).1 ⬝ᵥ
          S *ᵥ ofLp (EuclideanSpace.sumEquivProd (𝕜 := ℝ) t).1 +
        ofLp (EuclideanSpace.sumEquivProd (𝕜 := ℝ) t).2 ⬝ᵥ
          R *ᵥ ofLp (EuclideanSpace.sumEquivProd (𝕜 := ℝ) t).2 := by
    conv_lhs => rw [← Sum.elim_comp_inl_inr (ofLp t)]
    rw [fromBlocks_mulVec, zero_mulVec, zero_mulVec, add_zero, zero_add, Sum.elim_comp_inl,
      Sum.elim_comp_inr, sumElim_dotProduct_sumElim]
    rfl
  rw [h1, h2]
  push_cast
  ring

/-- Independent Gaussian random vectors concatenate to a Gaussian vector with block-diagonal
covariance. -/
theorem map_sumEquivProd_symm_of_indepFun {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {x : Ω → EuclideanSpace ℝ ι} {v : Ω → EuclideanSpace ℝ κ}
    (hx : Measurable x) (hv : Measurable v) (hind : IndepFun x v P) {m : EuclideanSpace ℝ ι}
    {m' : EuclideanSpace ℝ κ} {S : Matrix ι ι ℝ} {R : Matrix κ κ ℝ} (hS : S.PosSemidef)
    (hR : R.PosSemidef) (hxl : P.map x = multivariateGaussian m S)
    (hvl : P.map v = multivariateGaussian m' R) :
    P.map (fun ω => (EuclideanSpace.sumEquivProd (𝕜 := ℝ)).symm (x ω, v ω)) =
      multivariateGaussian ((EuclideanSpace.sumEquivProd (𝕜 := ℝ)).symm (m, m'))
        (fromBlocks S 0 0 R) := by
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hx.aemeasurable hv.aemeasurable).1 hind
  rw [← map_sumEquivProd_symm_prod_multivariateGaussian m m' hS hR, ← hxl, ← hvl, ← hprod,
    Measure.map_map (EuclideanSpace.sumEquivProd (𝕜 := ℝ)).symm.continuous.measurable
      (hx.prodMk hv)]
  rfl

end Blocks

section LinearModel

/-! ### Linear-Gaussian models: marginals and Bayes' theorem -/

open Matrix WithLp
open EuclideanSpace (sumEquivProd)
open scoped MatrixOrder

section Vectors

variable {n p : Type*} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]

theorem toEuclideanLin_blockRow_sumEquivProd_symm {ρ : Type*} (A : Matrix ρ n ℝ)
    (B : Matrix ρ p ℝ) (a : EuclideanSpace ℝ n) (b : EuclideanSpace ℝ p) :
    toEuclideanLin (blockRow A B) ((sumEquivProd (𝕜 := ℝ)).symm (a, b)) =
      toEuclideanLin A a + toEuclideanLin B b := by
  apply WithLp.ofLp_injective
  ext r
  simp [blockRow, mulVec, dotProduct, Fintype.sum_sum_type]

theorem toEuclideanLin_fromBlocks_sumEquivProd_symm (A : Matrix n n ℝ) (B : Matrix n p ℝ)
    (C : Matrix p n ℝ) (D : Matrix p p ℝ) (a : EuclideanSpace ℝ n) (b : EuclideanSpace ℝ p) :
    toEuclideanLin (fromBlocks A B C D) ((sumEquivProd (𝕜 := ℝ)).symm (a, b)) =
      (sumEquivProd (𝕜 := ℝ)).symm
        (toEuclideanLin A a + toEuclideanLin B b, toEuclideanLin C a + toEuclideanLin D b) := by
  apply WithLp.ofLp_injective
  ext r
  cases r <;> simp [fromBlocks, mulVec, dotProduct, Fintype.sum_sum_type]

theorem toEuclideanLin_one_apply (v : EuclideanSpace ℝ n) :
    toEuclideanLin (1 : Matrix n n ℝ) v = v := by
  apply WithLp.ofLp_injective
  exact one_mulVec _

end Vectors

section Covariances

variable {n p : Type*} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]

/-- The joint covariance `[[S, S Hᵀ], [H S, H S Hᵀ + R]]` of `(x, H x + v)` is
`[[1, 0], [H, 1]] diag(S, R) [[1, 0], [H, 1]]ᵀ`. -/
theorem fromBlocks_one_zero_mul_mul_transpose (S : Matrix n n ℝ) (R : Matrix p p ℝ)
    (H : Matrix p n ℝ) :
    fromBlocks 1 0 H 1 * fromBlocks S 0 0 R * (fromBlocks 1 0 H 1)ᵀ =
      fromBlocks S (S * Hᵀ) (H * S) (H * S * Hᵀ + R) := by
  simp [fromBlocks_multiply, fromBlocks_transpose, Matrix.mul_assoc]

omit [DecidableEq n] [Fintype p] [DecidableEq p] in
/-- The joint covariance of a linear-Gaussian observation is positive semidefinite. -/
theorem posSemidef_fromBlocks_linear [Finite p] {S : Matrix n n ℝ} {R : Matrix p p ℝ}
    (hS : S.PosSemidef) (hR : R.PosSemidef) (H : Matrix p n ℝ) :
    (fromBlocks S (S * Hᵀ) (H * S) (H * S * Hᵀ + R)).PosSemidef := by
  classical
  have := Fintype.ofFinite p
  rw [← fromBlocks_one_zero_mul_mul_transpose]
  simpa [conjTranspose_eq_transpose_of_trivial] using
    (posSemidef_fromBlocks_zero hS hR).mul_mul_conjTranspose_same (fromBlocks 1 0 H 1)

omit [DecidableEq n] in
/-- **The posterior covariance is positive semidefinite**: for positive semidefinite `S` and
positive definite `R`, `S - S Hᵀ (H S Hᵀ + R)⁻¹ H S` is positive semidefinite (it is the Schur
complement of the joint covariance). -/
theorem posSemidef_sub_mul_inv_mul {S : Matrix n n ℝ} {R : Matrix p p ℝ} (hS : S.PosSemidef)
    (hR : R.PosDef) (H : Matrix p n ℝ) :
    (S - S * Hᵀ * (H * S * Hᵀ + R)⁻¹ * (H * S)).PosSemidef := by
  classical
  have hHS : (H * S * Hᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hS.mul_mul_conjTranspose_same H
  have hD : (H * S * Hᵀ + R).PosDef := PosDef.posSemidef_add hHS hR
  have : Invertible (H * S * Hᵀ + R) := hD.isUnit.invertible
  have hSt : Sᵀ = S := by simpa [conjTranspose_eq_transpose_of_trivial] using hS.isHermitian.eq
  have hB : (S * Hᵀ)ᴴ = H * S := by
    rw [conjTranspose_eq_transpose_of_trivial, transpose_mul, transpose_transpose, hSt]
  have hjoint : (fromBlocks S (S * Hᵀ) (S * Hᵀ)ᴴ (H * S * Hᵀ + R)).PosSemidef := by
    rw [hB]
    exact posSemidef_fromBlocks_linear hS hR.posSemidef H
  have h := (PosDef.fromBlocks₂₂ S (S * Hᵀ) hD).1 hjoint
  rwa [hB] at h

end Covariances

section Model

variable {n p : Type*} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The marginal of a linear-Gaussian model**: if `x ~ N(m, S)` and `w ~ N(c, Q)` are
independent, then `F x + w ~ N(F m + c, F S Fᵀ + Q)`. -/
theorem map_linear_add_of_indepFun {x : Ω → EuclideanSpace ℝ n} {w : Ω → EuclideanSpace ℝ p}
    (hx : Measurable x) (hw : Measurable w) (hind : IndepFun x w P) {m : EuclideanSpace ℝ n}
    {c : EuclideanSpace ℝ p} {S : Matrix n n ℝ} {Q : Matrix p p ℝ} (hS : S.PosSemidef)
    (hQ : Q.PosSemidef) (hxl : P.map x = multivariateGaussian m S)
    (hwl : P.map w = multivariateGaussian c Q) (F : Matrix p n ℝ) :
    P.map (fun ω => toEuclideanLin F (x ω) + w ω) =
      multivariateGaussian (toEuclideanLin F m + c) (F * S * Fᵀ + Q) := by
  have hcat := map_sumEquivProd_symm_of_indepFun hx hw hind hS hQ hxl hwl
  have heq : (fun ω => toEuclideanLin F (x ω) + w ω) =
      toEuclideanLin (blockRow F 1) ∘ fun ω => (sumEquivProd (𝕜 := ℝ)).symm (x ω, w ω) := by
    funext ω
    rw [Function.comp_apply, toEuclideanLin_blockRow_sumEquivProd_symm, toEuclideanLin_one_apply]
  have hcm : Measurable fun ω => (sumEquivProd (𝕜 := ℝ)).symm (x ω, w ω) :=
    (sumEquivProd (𝕜 := ℝ)).symm.continuous.measurable.comp (hx.prodMk hw)
  rw [heq, ← Measure.map_map (continuous_toEuclideanLin _).measurable hcm, hcat,
    map_toEuclideanLin_multivariateGaussian _ _ (posSemidef_fromBlocks_zero hS hQ),
    toEuclideanLin_blockRow_sumEquivProd_symm, toEuclideanLin_one_apply,
    blockRow_mul_mul_transpose]
  simp

/-- **Bayes' theorem for a linear-Gaussian observation**: if `x ~ N(m, S)` and the noise
`v ~ N(0, R)` are independent and `H S Hᵀ + R` is invertible, then given the observation
`y = H x + v` the state is Gaussian with mean `m + S Hᵀ (H S Hᵀ + R)⁻¹ (y - H m)` and covariance
`S - S Hᵀ (H S Hᵀ + R)⁻¹ H S` (for almost every `y`). -/
theorem condDistrib_linear_add_of_indepFun {x : Ω → EuclideanSpace ℝ n}
    {v : Ω → EuclideanSpace ℝ p} (hx : Measurable x) (hv : Measurable v) (hind : IndepFun x v P)
    {m : EuclideanSpace ℝ n} {S : Matrix n n ℝ} {R : Matrix p p ℝ} (hS : S.PosSemidef)
    (hR : R.PosSemidef) (hxl : P.map x = multivariateGaussian m S)
    (hvl : P.map v = multivariateGaussian 0 R) (H : Matrix p n ℝ)
    (hinv : IsUnit (H * S * Hᵀ + R).det) :
    ∀ᵐ y ∂P.map (fun ω => toEuclideanLin H (x ω) + v ω),
      condDistrib x (fun ω => toEuclideanLin H (x ω) + v ω) P y =
        multivariateGaussian
          (m + toEuclideanLin (S * Hᵀ * (H * S * Hᵀ + R)⁻¹) (y - toEuclideanLin H m))
          (S - S * Hᵀ * (H * S * Hᵀ + R)⁻¹ * (H * S)) := by
  set e := (sumEquivProd (𝕜 := ℝ) (ι := n) (κ := p)).symm with he
  set M : Matrix (n ⊕ p) (n ⊕ p) ℝ := fromBlocks 1 0 H 1 with hM
  set V : Ω → EuclideanSpace ℝ (n ⊕ p) := fun ω => toEuclideanLin M (e (x ω, v ω)) with hVdef
  have hcm : Measurable fun ω => e (x ω, v ω) := e.continuous.measurable.comp (hx.prodMk hv)
  have hVm : Measurable V := (continuous_toEuclideanLin M).measurable.comp hcm
  have hMe : ∀ a b, toEuclideanLin M (e (a, b)) = e (a, toEuclideanLin H a + b) := fun a b => by
    rw [hM, he, toEuclideanLin_fromBlocks_sumEquivProd_symm, toEuclideanLin_one_apply,
      toEuclideanLin_one_apply, map_zero, LinearMap.zero_apply, add_zero]
  have hdiag := posSemidef_fromBlocks_zero hS hR
  have hcov : M * fromBlocks S 0 0 R * Mᵀ = fromBlocks S (S * Hᵀ) (H * S) (H * S * Hᵀ + R) :=
    fromBlocks_one_zero_mul_mul_transpose S R H
  have hjoint := posSemidef_fromBlocks_linear hS hR H
  have hlawV : P.map V = multivariateGaussian (e (m, toEuclideanLin H m))
      (fromBlocks S (S * Hᵀ) (H * S) (H * S * Hᵀ + R)) := by
    rw [show V = toEuclideanLin M ∘ fun ω => e (x ω, v ω) from rfl,
      ← Measure.map_map (continuous_toEuclideanLin _).measurable hcm,
      map_sumEquivProd_symm_of_indepFun hx hv hind hS hR hxl hvl,
      map_toEuclideanLin_multivariateGaussian _ _ hdiag, hcov, hMe, add_zero]
  have h := condDistrib_multivariateGaussian hVm hjoint hlawV (by simpa using hinv)
  have hblk1 : ∀ a b, toEuclideanLin (blockRow (1 : Matrix n n ℝ) 0) (e (a, b)) = a :=
    fun a b => by
      rw [he, toEuclideanLin_blockRow_sumEquivProd_symm, toEuclideanLin_one_apply, map_zero,
        LinearMap.zero_apply, add_zero]
  have hblk2 : ∀ a b, toEuclideanLin (blockRow (0 : Matrix p n ℝ) 1) (e (a, b)) = b :=
    fun a b => by
      rw [he, toEuclideanLin_blockRow_sumEquivProd_symm, toEuclideanLin_one_apply, map_zero,
        LinearMap.zero_apply, zero_add]
  have hX : (fun ω => toEuclideanLin (blockRow (1 : Matrix n n ℝ) 0) (V ω)) = x := by
    funext ω
    change toEuclideanLin (blockRow (1 : Matrix n n ℝ) 0) (toEuclideanLin M (e (x ω, v ω))) = x ω
    rw [hMe, hblk1]
  have hY : (fun ω => toEuclideanLin (blockRow (0 : Matrix p n ℝ) 1) (V ω)) =
      fun ω => toEuclideanLin H (x ω) + v ω := by
    funext ω
    change toEuclideanLin (blockRow (0 : Matrix p n ℝ) 1) (toEuclideanLin M (e (x ω, v ω))) = _
    rw [hMe, hblk2]
  rw [hX, hY, hblk1, hblk2] at h
  simpa using h

end Model

end LinearModel

end MetaMathlibExt
