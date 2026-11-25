/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.VectorGaussianKL
public import MathlibExt.Probability.Distributions.GaussianConditioning
public import MathlibExt.Probability.Distributions.GaussianMLE
public import MathlibExt.Probability.Statistics.InformationInequalityIdentification
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.WithDensity

/-!
# KL divergence of a Gaussian channel kernel

Let `H` be a real matrix from a finite input space to an output space of dimension `d`, let
`R` and `T` be positive definite output covariances, and let `q` be an output vector. For an
input law `μ` with finite second moment (no density assumed), let `k` be the additive Gaussian
noise kernel `x ↦ N(H x, R)`, the canonical `MetaMathlibExt.noiseKernel` with noise law
`N(0, R)`. Then

`KL(μ ⊗ₘ k ‖ μ × N(q, T)) =
  ofReal ((log (det T / det R) - d + trace (T⁻¹ R) + ∫ (H x - q)ᵀ T⁻¹ (H x - q) dμ(x)) / 2)`

(`klDiv_compProd_noiseKernel`, closed form `gaussianKernelKLReal`). The proof writes both laws
as densities against `μ × volume`, through the canonical multivariate Gaussian density, and
supplies the three ingredients separately: absolute continuity
(`compProd_noiseKernel_absolutelyContinuous`), the explicit fixed-covariance log-likelihood
ratio (`llr_compProd_noiseKernel_ae`) and its integrability
(`integrable_llr_compProd_noiseKernel`). The inner Gaussian expectations use the trace
evaluation `integral_quadratic_multivariateGaussian` from
`MathlibExt.InformationTheory.VectorGaussianKL`.

Validation: a point-mass input evaluates the closed form at the point
(`gaussianKernelKLReal_dirac`, `klDiv_compProd_noiseKernel_dirac`), and a Gaussian input whose
covariance is only positive semidefinite gives the trace term `trace (T⁻¹ H S Hᵀ)` plus the
mean quadratic form (`gaussianKernelKLReal_gaussianInput`).

Only the explicit fixed-covariance case is treated: there is no general divergence chain rule
for measurable kernels and no capacity optimization.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal

namespace MathlibExt.InformationTheory.VectorGaussianKernelKL

open _root_.InformationTheory
open MathlibExt.Probability.Statistics.InformationInequalityIdentification
  (densityModel logDensity densityModel_absolutelyContinuous llr_densityModel_ae_eq_of_ae)

/-! ### Auxiliary lemmas -/

/-- A quadratic form of a square-integrable vector is integrable. -/
theorem integrable_quad {α ι : Type*} [MeasurableSpace α] [Fintype ι] {ρ : Measure α}
    {u : α → EuclideanSpace ℝ ι} (hu : MemLp u 2 ρ) (M : Matrix ι ι ℝ) :
    Integrable (fun a => ofLp (u a) ⬝ᵥ M *ᵥ ofLp (u a)) ρ := by
  have hc : ∀ i, MemLp (fun a => u a i) 2 ρ := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hu
  have : (fun a => ofLp (u a) ⬝ᵥ M *ᵥ ofLp (u a)) =
      fun a => ∑ i, ∑ j, M i j * (u a i * u a j) := by
    funext a
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this]
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  exact ((hc i).integrable_mul (hc j)).const_mul _

/-- Measurability of the multivariate Gaussian density in the point. -/
theorem measurable_multivariateGaussianPDFReal_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    Measurable fun x => MetaMathlibExt.multivariateGaussianPDFReal m S x := by
  unfold MetaMathlibExt.multivariateGaussianPDFReal
  fun_prop

/-- The joint law of input and noise-kernel output is the image of the product law. -/
theorem compProd_noiseKernel_eq_map {E F : Type*} [AddCommGroup E] [MeasurableSpace E]
    [MeasurableAdd₂ E] [MeasurableSpace F] (f : F → E) (hf : Measurable f) (ν : Measure E)
    [IsProbabilityMeasure ν] (μ : Measure F) [SFinite μ] :
    μ ⊗ₘ MetaMathlibExt.noiseKernel f hf ν = (μ.prod ν).map fun p => (p.1, f p.1 + p.2) := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply (by fun_prop) hs,
    Measure.prod_apply (hs.preimage (by fun_prop))]
  refine lintegral_congr fun x => ?_
  rw [MetaMathlibExt.noiseKernel_apply,
    Measure.map_apply (measurable_const_add _) (measurable_prodMk_left hs)]
  rfl

/-! ### The closed form and its ingredients -/

/-- The closed form for the Gaussian channel kernel divergence: the
log-determinant term, the trace term, and the expected output quadratic
form under the input law, all over `2`. -/
noncomputable def gaussianKernelKLReal {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ) (q : EuclideanSpace ℝ ι)
    (R T : Matrix ι ι ℝ) (μ : Measure (EuclideanSpace ℝ κ)) : ℝ :=
  (Real.log (T.det / R.det) - (Fintype.card ι : ℝ) + (T⁻¹ * R).trace +
    ∫ x, ofLp (toEuclideanLin H x - q) ⬝ᵥ T⁻¹ *ᵥ ofLp (toEuclideanLin H x - q) ∂μ) / 2

/-- The output quadratic form is integrable under a finite-second-
moment input law, for any matrix `T`. -/
theorem integrable_outputQuadratic {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ) (q : EuclideanSpace ℝ ι)
    (T : Matrix ι ι ℝ)
    (μ : Measure (EuclideanSpace ℝ κ)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ) :
    Integrable (fun x => ofLp (toEuclideanLin H x - q) ⬝ᵥ T⁻¹ *ᵥ
      ofLp (toEuclideanLin H x - q)) μ :=
  integrable_quad (u := fun x => toEuclideanLin H x - q)
    (((LinearMap.toContinuousLinearMap (toEuclideanLin H)).comp_memLp' hμ).sub
      (memLp_const q)) T⁻¹

/-- The Gaussian noise kernel at `x` is the Gaussian centered at `H x`. -/
theorem noiseKernel_apply_multivariateGaussian {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ) (R : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ κ) :
    MetaMathlibExt.noiseKernel (toEuclideanLin H)
        (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R) x =
      multivariateGaussian (toEuclideanLin H x) R := by
  rw [MetaMathlibExt.noiseKernel_apply, MetaMathlibExt.map_add_multivariateGaussian, add_zero]

/-- The joint law has the explicit Gaussian density with respect to the input law times
Lebesgue measure. -/
theorem compProd_noiseKernel_eq_withDensity {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ) (R : Matrix ι ι ℝ) (hR : R.PosDef)
    (μ : Measure (EuclideanSpace ℝ κ)) [IsProbabilityMeasure μ] :
    μ ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
        (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R) =
      (μ.prod volume).withDensity fun p =>
        ENNReal.ofReal
          (MetaMathlibExt.multivariateGaussianPDFReal (toEuclideanLin H p.1) R p.2) := by
  have hj : Measurable fun p : EuclideanSpace ℝ κ × EuclideanSpace ℝ ι =>
      MetaMathlibExt.multivariateGaussianPDFReal (toEuclideanLin H p.1) R p.2 := by
    have hH : Measurable (toEuclideanLin H) :=
      (MetaMathlibExt.continuous_toEuclideanLin H).measurable
    unfold MetaMathlibExt.multivariateGaussianPDFReal
    fun_prop
  have hg : Measurable (Function.uncurry fun (x : EuclideanSpace ℝ κ) (y : EuclideanSpace ℝ ι) =>
      ENNReal.ofReal (MetaMathlibExt.multivariateGaussianPDFReal (toEuclideanLin H x) R y)) :=
    hj.ennreal_ofReal
  have hk : MetaMathlibExt.noiseKernel (toEuclideanLin H)
      (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R) =
      Kernel.withDensity (Kernel.const _ volume) fun x y =>
        ENNReal.ofReal (MetaMathlibExt.multivariateGaussianPDFReal (toEuclideanLin H x) R y) := by
    ext1 x
    rw [Kernel.withDensity_apply _ hg, Kernel.const_apply, noiseKernel_apply_multivariateGaussian,
      MetaMathlibExt.multivariateGaussian_eq_withDensity _ hR]
  have hs : IsSFiniteKernel (Kernel.withDensity
      (Kernel.const (EuclideanSpace ℝ κ) (volume : Measure (EuclideanSpace ℝ ι))) fun x y =>
        ENNReal.ofReal (MetaMathlibExt.multivariateGaussianPDFReal (toEuclideanLin H x) R y)) :=
    Kernel.IsSFiniteKernel.withDensity _ fun _ _ => ENNReal.ofReal_ne_top
  rw [hk, Measure.compProd_withDensity hg, Measure.compProd_const]

/-- The product of the input law with a Gaussian has the explicit density. -/
theorem prod_multivariateGaussian_eq_withDensity {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (q : EuclideanSpace ℝ ι) (T : Matrix ι ι ℝ) (hT : T.PosDef)
    (μ : Measure (EuclideanSpace ℝ κ)) [IsProbabilityMeasure μ] :
    μ.prod (multivariateGaussian q T) =
      (μ.prod volume).withDensity fun p =>
        ENNReal.ofReal (MetaMathlibExt.multivariateGaussianPDFReal q T p.2) := by
  rw [MetaMathlibExt.multivariateGaussian_eq_withDensity q hT,
    prod_withDensity_right
      (g := fun x => ENNReal.ofReal (MetaMathlibExt.multivariateGaussianPDFReal q T x))
      (measurable_multivariateGaussianPDFReal_right q T).ennreal_ofReal]

/-- Under the joint law, the noise and the output deviation from `q` have finite second
moments. -/
theorem memLp_compProd_noiseKernel {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ) (q : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ)
    (μ : Measure (EuclideanSpace ℝ κ)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ) :
    MemLp (fun p : EuclideanSpace ℝ κ × EuclideanSpace ℝ ι => p.2 - toEuclideanLin H p.1) 2
        (μ ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
          (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R)) ∧
      MemLp (fun p : EuclideanSpace ℝ κ × EuclideanSpace ℝ ι => p.2 - q) 2
        (μ ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
          (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R)) := by
  have hHc := MetaMathlibExt.continuous_toEuclideanLin H
  have hφ : AEMeasurable (fun p : EuclideanSpace ℝ κ × EuclideanSpace ℝ ι =>
      (p.1, toEuclideanLin H p.1 + p.2)) (μ.prod (multivariateGaussian 0 R)) :=
    (measurable_fst.prodMk ((hHc.measurable.comp measurable_fst).add measurable_snd)).aemeasurable
  have hsnd : MemLp (fun p : EuclideanSpace ℝ κ × EuclideanSpace ℝ ι => p.2) 2
      (μ.prod (multivariateGaussian 0 R)) :=
    IsGaussian.memLp_two_id.comp_measurePreserving measurePreserving_snd
  have hfst : MemLp (fun p : EuclideanSpace ℝ κ × EuclideanSpace ℝ ι => toEuclideanLin H p.1) 2
      (μ.prod (multivariateGaussian 0 R)) :=
    ((LinearMap.toContinuousLinearMap (toEuclideanLin H)).comp_memLp' hμ).comp_measurePreserving
      measurePreserving_fst
  rw [compProd_noiseKernel_eq_map]
  constructor
  · rw [memLp_map_measure_iff (g := fun p : EuclideanSpace ℝ κ × EuclideanSpace ℝ ι =>
      p.2 - toEuclideanLin H p.1)
      (continuous_snd.sub (hHc.comp continuous_fst)).aestronglyMeasurable hφ]
    have : ((fun p : EuclideanSpace ℝ κ × EuclideanSpace ℝ ι => p.2 - toEuclideanLin H p.1) ∘
        fun p : EuclideanSpace ℝ κ × EuclideanSpace ℝ ι => (p.1, toEuclideanLin H p.1 + p.2)) =
        fun p => p.2 := by
      funext p; simp
    rw [this]; exact hsnd
  · rw [memLp_map_measure_iff (g := fun p : EuclideanSpace ℝ κ × EuclideanSpace ℝ ι => p.2 - q)
      (continuous_snd.sub continuous_const).aestronglyMeasurable hφ]
    have : ((fun p : EuclideanSpace ℝ κ × EuclideanSpace ℝ ι => p.2 - q) ∘
        fun p : EuclideanSpace ℝ κ × EuclideanSpace ℝ ι => (p.1, toEuclideanLin H p.1 + p.2)) =
        fun p => toEuclideanLin H p.1 + p.2 - q := rfl
    rw [this]; exact (hfst.add hsnd).sub (memLp_const q)

/-- Absolute continuity on the product: the joint law of input and
channel output is absolutely continuous with respect to the product
of the input law with the comparison Gaussian. -/
theorem compProd_noiseKernel_absolutelyContinuous {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ) (q : EuclideanSpace ℝ ι)
    (R T : Matrix ι ι ℝ) (hR : R.PosDef) (hT : T.PosDef)
    (μ : Measure (EuclideanSpace ℝ κ)) [IsProbabilityMeasure μ] :
    μ ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
        (MetaMathlibExt.continuous_toEuclideanLin H).measurable
        (multivariateGaussian 0 R) ≪
      μ.prod (multivariateGaussian q T) := by
  have hg : Measurable fun p : EuclideanSpace ℝ κ × EuclideanSpace ℝ ι =>
      MetaMathlibExt.multivariateGaussianPDFReal q T p.2 :=
    (measurable_multivariateGaussianPDFReal_right q T).comp measurable_snd
  rw [compProd_noiseKernel_eq_withDensity H R hR μ,
    prod_multivariateGaussian_eq_withDensity q T hT μ]
  exact densityModel_absolutelyContinuous (ν := μ.prod volume) (p := fun f => f)
    (θ₀ := fun p => MetaMathlibExt.multivariateGaussianPDFReal (toEuclideanLin H p.1) R p.2) hg
    (ae_of_all _ fun p => MetaMathlibExt.multivariateGaussianPDFReal_pos q hT p.2)

/-- The log-likelihood ratio on the product is the fixed-covariance
Gaussian ratio: the log-determinant term minus the noise quadratic form
plus the comparison quadratic form, all over `2`, almost everywhere
under the joint law. -/
theorem llr_compProd_noiseKernel_ae {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ) (q : EuclideanSpace ℝ ι)
    (R T : Matrix ι ι ℝ) (hR : R.PosDef) (hT : T.PosDef)
    (μ : Measure (EuclideanSpace ℝ κ)) [IsProbabilityMeasure μ] :
    llr (μ ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
        (MetaMathlibExt.continuous_toEuclideanLin H).measurable
        (multivariateGaussian 0 R)) (μ.prod (multivariateGaussian q T)) =ᵐ[
      μ ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
        (MetaMathlibExt.continuous_toEuclideanLin H).measurable
        (multivariateGaussian 0 R)]
      fun p => (Real.log (T.det / R.det) -
        ofLp (p.2 - toEuclideanLin H p.1) ⬝ᵥ R⁻¹ *ᵥ ofLp (p.2 - toEuclideanLin H p.1) +
        ofLp (p.2 - q) ⬝ᵥ T⁻¹ *ᵥ ofLp (p.2 - q)) / 2 := by
  have hf : Measurable fun p : EuclideanSpace ℝ κ × EuclideanSpace ℝ ι =>
      MetaMathlibExt.multivariateGaussianPDFReal (toEuclideanLin H p.1) R p.2 := by
    have hH : Measurable (toEuclideanLin H) :=
      (MetaMathlibExt.continuous_toEuclideanLin H).measurable
    unfold MetaMathlibExt.multivariateGaussianPDFReal
    fun_prop
  have hg : Measurable fun p : EuclideanSpace ℝ κ × EuclideanSpace ℝ ι =>
      MetaMathlibExt.multivariateGaussianPDFReal q T p.2 :=
    (measurable_multivariateGaussianPDFReal_right q T).comp measurable_snd
  rw [compProd_noiseKernel_eq_withDensity H R hR μ,
    prod_multivariateGaussian_eq_withDensity q T hT μ]
  have h := llr_densityModel_ae_eq_of_ae (ν := μ.prod volume) (p := fun f => f) hf hg
    (ae_of_all _ fun p => MetaMathlibExt.multivariateGaussianPDFReal_pos _ hR p.2)
    (ae_of_all _ fun p => MetaMathlibExt.multivariateGaussianPDFReal_pos q hT p.2)
  simp only [densityModel, logDensity] at h
  filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le h] with p hp
  rw [hp, ← Real.log_div (MetaMathlibExt.multivariateGaussianPDFReal_pos _ hR p.2).ne'
      (MetaMathlibExt.multivariateGaussianPDFReal_pos q hT p.2).ne',
    VectorGaussianKL.log_multivariateGaussianPDFReal_div _ _ _ _ hR hT]

/-- The log-likelihood ratio on the product is integrable under the
joint law. -/
theorem integrable_llr_compProd_noiseKernel {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ) (q : EuclideanSpace ℝ ι)
    (R T : Matrix ι ι ℝ) (hR : R.PosDef) (hT : T.PosDef)
    (μ : Measure (EuclideanSpace ℝ κ)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ) :
    Integrable (llr (μ ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
        (MetaMathlibExt.continuous_toEuclideanLin H).measurable
        (multivariateGaussian 0 R)) (μ.prod (multivariateGaussian q T)))
      (μ ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
        (MetaMathlibExt.continuous_toEuclideanLin H).measurable
        (multivariateGaussian 0 R)) := by
  obtain ⟨h1, h2⟩ := memLp_compProd_noiseKernel H q R μ hμ
  exact ((((integrable_const _).sub (integrable_quad h1 R⁻¹)).add
    (integrable_quad h2 T⁻¹)).div_const 2).congr
      (llr_compProd_noiseKernel_ae H q R T hR hT μ).symm

/-! ### The divergence -/

/-- **Gaussian channel kernel divergence.** For a finite-second-
moment input law `μ` and the noise kernel of `N(0, R)`, with `R, T`
positive definite, the divergence of the joint law from `μ` times
`N(q, T)` is the displayed closed form, with `d = card ι` the output
dimension. -/
theorem klDiv_compProd_noiseKernel {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ) (q : EuclideanSpace ℝ ι)
    (R T : Matrix ι ι ℝ) (hR : R.PosDef) (hT : T.PosDef)
    (μ : Measure (EuclideanSpace ℝ κ)) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ) :
    klDiv (μ ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
        (MetaMathlibExt.continuous_toEuclideanLin H).measurable
        (multivariateGaussian 0 R)) (μ.prod (multivariateGaussian q T)) =
      ENNReal.ofReal (gaussianKernelKLReal H q R T μ) := by
  obtain ⟨h1, h2⟩ := memLp_compProd_noiseKernel H q R μ hμ
  have hF : Integrable (fun p : EuclideanSpace ℝ κ × EuclideanSpace ℝ ι =>
      (Real.log (T.det / R.det) -
        ofLp (p.2 - toEuclideanLin H p.1) ⬝ᵥ R⁻¹ *ᵥ ofLp (p.2 - toEuclideanLin H p.1) +
        ofLp (p.2 - q) ⬝ᵥ T⁻¹ *ᵥ ofLp (p.2 - q)) / 2)
      (μ ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
        (MetaMathlibExt.continuous_toEuclideanLin H).measurable (multivariateGaussian 0 R)) :=
    (((integrable_const _).sub (integrable_quad h1 R⁻¹)).add (integrable_quad h2 T⁻¹)).div_const 2
  rw [klDiv_of_ac_of_integrable (compProd_noiseKernel_absolutelyContinuous H q R T hR hT μ)
      (integrable_llr_compProd_noiseKernel H q R T hR hT μ hμ),
    integral_congr_ae (llr_compProd_noiseKernel_ae H q R T hR hT μ), probReal_univ,
    probReal_univ, add_sub_cancel_right, Measure.integral_compProd hF]
  congr 1
  simp_rw [noiseKernel_apply_multivariateGaussian]
  have inner : ∀ x : EuclideanSpace ℝ κ,
      ∫ y, (Real.log (T.det / R.det) -
        ofLp (y - toEuclideanLin H x) ⬝ᵥ R⁻¹ *ᵥ ofLp (y - toEuclideanLin H x) +
        ofLp (y - q) ⬝ᵥ T⁻¹ *ᵥ ofLp (y - q)) / 2 ∂(multivariateGaussian (toEuclideanLin H x) R) =
      (Real.log (T.det / R.det) - (Fintype.card ι : ℝ) + (T⁻¹ * R).trace +
        ofLp (toEuclideanLin H x - q) ⬝ᵥ T⁻¹ *ᵥ ofLp (toEuclideanLin H x - q)) / 2 := by
    intro x
    have hQ : ∀ (c : EuclideanSpace ℝ ι) (M : Matrix ι ι ℝ),
        Integrable (fun y => ofLp (y - c) ⬝ᵥ M *ᵥ ofLp (y - c))
          (multivariateGaussian (toEuclideanLin H x) R) := fun c M =>
      VectorGaussianKL.integrable_quadratic_multivariateGaussian _ c R M hR.posSemidef
    have hI : Integrable (fun y => Real.log (T.det / R.det) -
        ofLp (y - toEuclideanLin H x) ⬝ᵥ R⁻¹ *ᵥ ofLp (y - toEuclideanLin H x))
        (multivariateGaussian (toEuclideanLin H x) R) :=
      (integrable_const _).sub (hQ _ R⁻¹)
    rw [integral_div, integral_add hI (hQ q T⁻¹), integral_sub (integrable_const _) (hQ _ R⁻¹),
      integral_const, probReal_univ,
      VectorGaussianKL.integral_quadratic_multivariateGaussian _ _ R R⁻¹ hR.posSemidef,
      VectorGaussianKL.integral_quadratic_multivariateGaussian _ q R T⁻¹ hR.posSemidef,
      nonsing_inv_mul R (isUnit_iff_ne_zero.2 hR.det_pos.ne')]
    simp
    ring
  simp_rw [inner]
  unfold gaussianKernelKLReal
  rw [integral_div, integral_add (integrable_const _) (integrable_outputQuadratic H q T μ hμ),
    integral_const, probReal_univ, one_smul]

/-! ### Validation -/

/-- Point-mass input: the expected quadratic form is the quadratic
form at the point, so a large input mean contributes through
`H a - q`; the closed form is evaluated at that point. -/
theorem gaussianKernelKLReal_dirac {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ) (q : EuclideanSpace ℝ ι)
    (R T : Matrix ι ι ℝ) (a : EuclideanSpace ℝ κ) :
    gaussianKernelKLReal H q R T (Measure.dirac a) =
      (Real.log (T.det / R.det) - (Fintype.card ι : ℝ) + (T⁻¹ * R).trace +
        ofLp (toEuclideanLin H a - q) ⬝ᵥ T⁻¹ *ᵥ ofLp (toEuclideanLin H a - q)) / 2 := by
  unfold gaussianKernelKLReal
  rw [integral_dirac]

/-- Point-mass input, measure level: the divergence for a Dirac
input law is the closed form evaluated at the point. -/
theorem klDiv_compProd_noiseKernel_dirac {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ) (q : EuclideanSpace ℝ ι)
    (R T : Matrix ι ι ℝ) (hR : R.PosDef) (hT : T.PosDef) (a : EuclideanSpace ℝ κ) :
    klDiv ((Measure.dirac a) ⊗ₘ MetaMathlibExt.noiseKernel (toEuclideanLin H)
        (MetaMathlibExt.continuous_toEuclideanLin H).measurable
        (multivariateGaussian 0 R)) ((Measure.dirac a).prod (multivariateGaussian q T)) =
      ENNReal.ofReal (gaussianKernelKLReal H q R T (Measure.dirac a)) := by
  have hμ : MemLp id 2 (Measure.dirac a) := (memLp_const a).ae_eq (ae_eq_dirac id).symm
  exact klDiv_compProd_noiseKernel H q R T hR hT (Measure.dirac a) hμ

/-- Singular Gaussian input: for a Gaussian input with only positive
semidefinite covariance `S`, the expected output quadratic form is
the trace term plus the mean quadratic form, so the closed form has
the displayed evaluation. -/
theorem gaussianKernelKLReal_gaussianInput {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (H : Matrix ι κ ℝ) (q : EuclideanSpace ℝ ι)
    (R T : Matrix ι ι ℝ) (m : EuclideanSpace ℝ κ) (S : Matrix κ κ ℝ) (hS : S.PosSemidef) :
    gaussianKernelKLReal H q R T (multivariateGaussian m S) =
      (Real.log (T.det / R.det) - (Fintype.card ι : ℝ) + (T⁻¹ * R).trace +
        ((T⁻¹ * (H * S * Hᵀ)).trace +
          ofLp (toEuclideanLin H m - q) ⬝ᵥ T⁻¹ *ᵥ ofLp (toEuclideanLin H m - q))) / 2 := by
  have hHS : (H * S * Hᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hS.mul_mul_conjTranspose_same H
  have hmap := integral_map (μ := multivariateGaussian m S)
    (MetaMathlibExt.continuous_toEuclideanLin H).aemeasurable
    (f := fun y => ofLp (y - q) ⬝ᵥ T⁻¹ *ᵥ ofLp (y - q)) (by fun_prop)
  rw [MetaMathlibExt.map_toEuclideanLin_multivariateGaussian H m hS,
    VectorGaussianKL.integral_quadratic_multivariateGaussian _ q _ T⁻¹ hHS] at hmap
  unfold gaussianKernelKLReal
  rw [← hmap]

end MathlibExt.InformationTheory.VectorGaussianKernelKL
