/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.CramerWold
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# The multivariate central limit theorem

For an i.i.d. sequence `X : ℕ → Ω → E` of square-integrable random vectors in a
finite-dimensional real inner product space, with mean `μ := ∫ ω, X 0 ω ∂P`, the scaled centered
sums `(√n)⁻¹ • (∑ k ∈ range n, X k - n • μ)` converge in distribution to any random vector `Y`
whose every scalar projection `⟪Y, t⟫` is a centered real Gaussian of variance
`Var[⟪X 0, t⟫]`.

## Main statements

* `ProbabilityTheory.tendstoInDistribution_inv_sqrt_smul_sum_sub`: the multivariate CLT in
  interface form: the limit `Y` is given, and only the laws of its projections are assumed.
* `ProbabilityTheory.exists_hasLaw_inner_gaussianReal`: a continuous linear map `A : E →L[ℝ] E`
  whose projections `⟪A z, t⟫` under `stdGaussian E` have law `gaussianReal 0 Var[⟪X₀, t⟫]`.
* `ProbabilityTheory.exists_tendstoInDistribution_inv_sqrt_smul_sum_sub`: the multivariate CLT
  with that constructed Gaussian limit on `stdGaussian E`.

## Proof

Cramér–Wold (`TendstoInDistribution.of_inner`) reduces convergence to every scalar projection.
For fixed `t`, the projections `⟪X k, t⟫` are i.i.d. and square integrable, and
`⟪(√n)⁻¹ • (∑ X k - n • μ), t⟫ = (√n)⁻¹ * (∑ ⟪X k, t⟫ - n * P[⟪X 0, t⟫])` since
`P[⟪X 0, t⟫] = ⟪μ, t⟫`. The one-dimensional CLT `tendstoInDistribution_inv_sqrt_mul_sum_sub`
then applies to each projection.

The covariance may be singular: a projection of variance `0` converges to the Dirac mass at `0`,
which is `gaussianReal 0 0`, by the scalar CLT's own degenerate branch.

For the constructed limit, write the covariance of `X₀` as a positive semidefinite matrix `S` in
an orthonormal basis `b` of `E`, take `A := b.repr.symm ∘ CFC.sqrt S ∘ b.repr`, and read the
projection laws off `multivariateGaussian 0 S`, which is the image of `stdGaussian` under
`CFC.sqrt S`.
-/

public section

open MeasureTheory Filter Finset RealInnerProductSpace
open scoped Real

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

omit [MeasurableSpace E] [BorelSpace E] [IsProbabilityMeasure P] in
/-- The scalar projection of a centered scaled sum is the centered scaled sum of the scalar
projections. -/
private lemma inner_inv_sqrt_smul_sum_sub (X : ℕ → Ω → E) (hX : Integrable (X 0) P) (t : E)
    (n : ℕ) (ω : Ω) :
    ⟪(√n)⁻¹ • (∑ k ∈ range n, X k ω - n • ∫ ω, X 0 ω ∂P), t⟫ =
      (√n)⁻¹ * (∑ k ∈ range n, ⟪X k ω, t⟫ - n * ∫ ω, ⟪X 0 ω, t⟫ ∂P) := by
  have hμ : ∫ ω, ⟪X 0 ω, t⟫ ∂P = ⟪∫ ω, X 0 ω ∂P, t⟫ := by
    simp_rw [real_inner_comm t]
    exact integral_inner hX t
  rw [real_inner_smul_left, inner_sub_left, sum_inner, ← Nat.cast_smul_eq_nsmul ℝ,
    real_inner_smul_left, hμ]

/-- **Multivariate central limit theorem** (interface form). Let `X : ℕ → Ω → E` be i.i.d.
square-integrable random vectors in a finite-dimensional real inner product space with mean
`μ := ∫ ω, X 0 ω ∂P`. If `Y : Ω' → E` is a random vector all of whose scalar projections `⟪Y, t⟫`
are centered real Gaussians with variance `Var[⟪X 0, t⟫]`, then
`(√n)⁻¹ • (∑ k ∈ range n, X k - n • μ)` converges in distribution to `Y`.

The covariance of `X 0` may be singular: a projection with variance `0` has the Dirac mass at `0`
as its limit law, which is `gaussianReal 0 0`. -/
theorem tendstoInDistribution_inv_sqrt_smul_sum_sub {X : ℕ → Ω → E} {Y : Ω' → E}
    (hY : AEMeasurable Y P')
    (hYlaw : ∀ t : E,
      HasLaw (fun ω ↦ ⟪Y ω, t⟫) (gaussianReal 0 (Var[fun ω ↦ ⟪X 0 ω, t⟫; P]).toNNReal) P')
    (hX : MemLp (X 0) 2 P) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (√n)⁻¹ • (∑ k ∈ range n, X k ω - n • ∫ ω, X 0 ω ∂P))
      atTop Y (fun _ ↦ P) P' := by
  have hmeas : ∀ i, AEMeasurable (X i) P := fun i ↦ (hident i).aemeasurable_fst
  refine TendstoInDistribution.of_inner hY
    (fun n ↦ ((Finset.aemeasurable_fun_sum _ fun k _ ↦ hmeas k).sub aemeasurable_const).const_smul
      _) fun t ↦ ?_
  have hinner : Measurable fun x : E ↦ ⟪x, t⟫ := (continuous_id.inner continuous_const).measurable
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub (X := fun k ω ↦ ⟪X k ω, t⟫)
    (hYlaw t) (hX.inner_const t) (hindep.comp (fun _ x ↦ ⟪x, t⟫) fun _ ↦ hinner)
    (fun i ↦ (hident i).comp hinner)
  have hfun : (fun (n : ℕ) ω ↦ ⟪(√n)⁻¹ • (∑ k ∈ range n, X k ω - n • ∫ ω, X 0 ω ∂P), t⟫) =
      fun (n : ℕ) ω ↦ (√n)⁻¹ * (∑ k ∈ range n, ⟪X k ω, t⟫ - n * ∫ ω, ⟪X 0 ω, t⟫ ∂P) := by
    ext n ω
    exact inner_inv_sqrt_smul_sum_sub X (hX.integrable one_le_two) t n ω
  rw [hfun]
  exact hclt

/-! ### Existence of the Gaussian limit -/

section Existence

open Matrix
open scoped MatrixOrder

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The matrix of a bilinear form in a basis, as a quadratic form in coordinates. -/
private lemma dotProduct_mulVec_bilin {ι : Type*} [Fintype ι] (C : E →L[ℝ] E →L[ℝ] ℝ)
    (b : ι → E) (x : ι → ℝ) :
    x ⬝ᵥ (Matrix.of fun i j ↦ C (b i) (b j)) *ᵥ x = C (∑ i, x i • b i) (∑ i, x i • b i) := by
  simp only [dotProduct, mulVec, of_apply, map_sum, map_smul, _root_.sum_apply,
    _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

omit [FiniteDimensional ℝ E] in
/-- The covariance matrix of a measure in a family of vectors is positive semidefinite. -/
private lemma posSemidef_covarianceBilin_matrix {ι : Type*} [Finite ι] (ν : Measure E)
    (b : ι → E) : (Matrix.of fun i j ↦ covarianceBilin ν (b i) (b j)).PosSemidef := by
  have := Fintype.ofFinite ι
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x ↦ ?_
  · ext i j
    simp [covarianceBilin_comm]
  · rw [star_trivial, dotProduct_mulVec_bilin]
    exact covarianceBilin_self_nonneg _

/-- For any square-integrable random vector `X₀` in a finite-dimensional real inner product space
`E`, there is a continuous linear map `A : E →L[ℝ] E` such that, under the standard Gaussian
measure on `E`, every scalar projection `⟪A z, t⟫` is a centered real Gaussian with variance
`Var[⟪X₀, t⟫]`. Concretely `A` is the positive square root of the covariance of `X₀`, written in
an orthonormal basis. -/
theorem exists_hasLaw_inner_gaussianReal {X₀ : Ω → E} (hX : MemLp X₀ 2 P) :
    ∃ A : E →L[ℝ] E, ∀ t : E, HasLaw (fun z ↦ ⟪A z, t⟫)
      (gaussianReal 0 (Var[fun ω ↦ ⟪X₀ ω, t⟫; P]).toNNReal) (stdGaussian E) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let ν : Measure E := P.map X₀
  let S : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    Matrix.of fun i j ↦ covarianceBilin ν (b i) (b j)
  have hS : S.PosSemidef := posSemidef_covarianceBilin_matrix ν b
  let R := toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
  let e := b.repr.toContinuousLinearEquiv.toContinuousLinearMap
  let e' := b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨e' ∘L R ∘L e, fun t ↦ ⟨by fun_prop, ?_⟩⟩
  set s := b.repr t
  have hproj : (fun z ↦ ⟪(e' ∘L R ∘L e) z, t⟫) =
      (innerSL ℝ s) ∘ (fun w ↦ 0 + R w) ∘ b.repr := by
    ext z
    simp [e, e', LinearIsometryEquiv.inner_map_eq_flip, real_inner_comm, s]
  have hmv : (stdGaussian E).map ((fun w ↦ 0 + R w) ∘ b.repr) = multivariateGaussian 0 S := by
    rw [← Measure.map_map (by fun_prop) (by fun_prop), stdGaussian_map b.repr]
    rfl
  have hν : MemLp id 2 ν := (memLp_map_measure_iff aestronglyMeasurable_id hX.aemeasurable).2 hX
  have hinner : Measurable fun u : E ↦ ⟪t, u⟫ := (continuous_const.inner continuous_id).measurable
  rw [hproj, ← Measure.map_map (by fun_prop) (by fun_prop), hmv,
    IsGaussian.map_eq_gaussianReal,
    ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id,
    integral_id_multivariateGaussian, map_zero]
  congr 2
  have hvar : Var[⇑(innerSL ℝ s); multivariateGaussian 0 S] = s ⬝ᵥ S *ᵥ s := by
    rw [← covarianceBilin_multivariateGaussian hS, covarianceBilin_self IsGaussian.memLp_two_id]
    rfl
  rw [hvar, dotProduct_mulVec_bilin]
  simp only [s, b.sum_repr]
  rw [covarianceBilin_self hν, variance_map hinner.aemeasurable hX.aemeasurable]
  simp_rw [Function.comp_def, real_inner_comm t]

/-- **Multivariate central limit theorem** with a constructed limit. For i.i.d.
square-integrable random vectors `X : ℕ → Ω → E` in a finite-dimensional real inner product space
with mean `μ := ∫ ω, X 0 ω ∂P`, there is a continuous linear map `A : E →L[ℝ] E` such that, under
the standard Gaussian measure on `E`, `A` is a Gaussian random vector whose projections `⟪A, t⟫`
are centered with variance `Var[⟪X 0, t⟫]`, and `(√n)⁻¹ • (∑ k ∈ range n, X k - n • μ)` converges
in distribution to `A`. -/
theorem exists_tendstoInDistribution_inv_sqrt_smul_sum_sub {X : ℕ → Ω → E}
    (hX : MemLp (X 0) 2 P) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∃ A : E →L[ℝ] E, HasGaussianLaw A (stdGaussian E) ∧
      (∀ t : E, HasLaw (fun z ↦ ⟪A z, t⟫)
        (gaussianReal 0 (Var[fun ω ↦ ⟪X 0 ω, t⟫; P]).toNNReal) (stdGaussian E)) ∧
      TendstoInDistribution
        (fun (n : ℕ) ω ↦ (√n)⁻¹ • (∑ k ∈ range n, X k ω - n • ∫ ω, X 0 ω ∂P))
        atTop A (fun _ ↦ P) (stdGaussian E) := by
  obtain ⟨A, hA⟩ := exists_hasLaw_inner_gaussianReal hX
  exact ⟨A, IsGaussian.hasGaussianLaw_id.map A, hA,
    tendstoInDistribution_inv_sqrt_smul_sum_sub A.continuous.aemeasurable hA hX hindep hident⟩

end Existence

end ProbabilityTheory
