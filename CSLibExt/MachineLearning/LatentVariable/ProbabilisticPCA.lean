/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Probabilistic PCA and factor analysis: the marginal is Gaussian

The linear-Gaussian latent-variable model `x = W z + μ + ε`, with `z ~ N(0, I)` and independent
noise `ε ~ N(0, Ψ)` (Tipping and Bishop, *Probabilistic principal component analysis*, J. R.
Stat. Soc. B 61, 1999; Bishop, *Pattern Recognition and Machine Learning*, Sections 12.2 and
12.2.4). The Gaussians are Mathlib's `stdGaussian` and `multivariateGaussian`.

Main results:

* The map `z ↦ W z` is Mathlib's `Matrix.toEuclideanLin W`. `inner_toEuclideanLin`: its adjoint
  is `Wᵀ` (from `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`); `charFun_map_toEuclideanLin`:
  characteristic functions of linear images.
* `map_eq_multivariateGaussian`: **the marginal is Gaussian**: `x ~ N(μ, W Wᵀ + Ψ)` for any
  positive semidefinite `Ψ`.
* `ppca_map_eq` (`Ψ = σ² I`, probabilistic PCA) and `factorAnalysis_map_eq` (`Ψ` diagonal,
  factor analysis).

Not covered: the maximum-likelihood solution (Tipping and Bishop's principal-subspace theorem)
and the posterior of `z` given `x`. The reconstruction objective of deterministic PCA is in
`FormalizedTextbooks/UnderstandingMachineLearningFromTheoryToAlgorithms/Ch23.lean`; Gaussian
projections and covariances are in `FormalizedTextbooks/HighDimensionalProbability/Chapter03/`.

## Cost model

None: a statement about laws.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.LatentVariable.ProbabilisticPCA

open MeasureTheory ProbabilityTheory Complex Matrix WithLp
open scoped RealInnerProductSpace

variable {q d : ℕ}

theorem continuous_toEuclideanLin (W : Matrix (Fin d) (Fin q) ℝ) :
    Continuous (toEuclideanLin W) :=
  LinearMap.continuous_of_finiteDimensional _

/-- **The transpose of a real matrix is its adjoint.** For every real $d \times q$ matrix $W$ and
all $z \in \mathbb{R}^q$ and $t \in \mathbb{R}^d$, the Euclidean inner products satisfy
$\langle Wz, t\rangle = \langle z, W^\top t\rangle$. -/
theorem inner_toEuclideanLin (W : Matrix (Fin d) (Fin q) ℝ) (t : EuclideanSpace ℝ (Fin d))
    (z : EuclideanSpace ℝ (Fin q)) :
    ⟪toEuclideanLin W z, t⟫ = ⟪z, toEuclideanLin Wᵀ t⟫ := by
  rw [← conjTranspose_eq_transpose_of_trivial, toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_right]

/-- **Characteristic function of a linear image.** Let $\mu$ be a measure on $\mathbb{R}^q$
and $W$ a real $d \times q$ matrix, and write
$\varphi_\nu(t) = \int e^{i\langle x, t\rangle}\,d\nu(x)$ for the characteristic function of a
measure $\nu$. Then the pushforward $W_*\mu$ of $\mu$ under $z \mapsto Wz$ satisfies
$\varphi_{W_*\mu}(t) = \varphi_\mu(W^\top t)$ for every $t \in \mathbb{R}^d$. -/
theorem charFun_map_toEuclideanLin (μ : Measure (EuclideanSpace ℝ (Fin q)))
    (W : Matrix (Fin d) (Fin q) ℝ) (t : EuclideanSpace ℝ (Fin d)) :
    charFun (μ.map (toEuclideanLin W)) t = charFun μ (toEuclideanLin Wᵀ t) := by
  rw [charFun_apply, charFun_apply,
    integral_map (continuous_toEuclideanLin W).aemeasurable (by fun_prop)]
  simp_rw [inner_toEuclideanLin]

theorem norm_sq_toEuclideanLin_transpose (W : Matrix (Fin d) (Fin q) ℝ)
    (t : EuclideanSpace ℝ (Fin d)) :
    ‖toEuclideanLin Wᵀ t‖ ^ 2 = ofLp t ⬝ᵥ (W * Wᵀ) *ᵥ ofLp t := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
    show ofLp (toEuclideanLin Wᵀ t) = Wᵀ *ᵥ ofLp t from rfl, ← mulVec_mulVec, dotProduct_mulVec,
    ← mulVec_transpose, transpose_transpose,
    dotProduct_comm]

/-- **The marginal of probabilistic PCA and factor analysis is Gaussian.** Let $Z$ and $E$ be
independent random vectors on a probability space, with values in $\mathbb{R}^q$ and
$\mathbb{R}^d$, such that $Z$ has the standard Gaussian law $N(0, I_q)$ and $E$ has law
$N(0, \Psi)$ for a positive semidefinite real $d \times d$ matrix $\Psi$. Then for every real
$d \times q$ matrix $W$ and every $\mu \in \mathbb{R}^d$, the random vector $WZ + \mu + E$ has
law $N(\mu, WW^\top + \Psi)$.

This is the marginal of Tipping and Bishop's model: probabilistic PCA is the case
$\Psi = \sigma^2 I$, factor analysis the case of a diagonal $\Psi$. -/
theorem map_eq_multivariateGaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → EuclideanSpace ℝ (Fin q)} {E : Ω → EuclideanSpace ℝ (Fin d)}
    {Ψ : Matrix (Fin d) (Fin d) ℝ} (hZ : HasLaw Z (stdGaussian _) P)
    (hE : HasLaw E (multivariateGaussian 0 Ψ) P) (hΨ : Ψ.PosSemidef) (hind : IndepFun Z E P)
    (W : Matrix (Fin d) (Fin q) ℝ) (μ : EuclideanSpace ℝ (Fin d)) :
    P.map (fun ω => toEuclideanLin W (Z ω) + μ + E ω) = multivariateGaussian μ (W * Wᵀ + Ψ) := by
  have hWW : (W * Wᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose W
  have hS : (W * Wᵀ + Ψ).PosSemidef := hWW.add hΨ
  have hA : AEMeasurable (fun ω => toEuclideanLin W (Z ω) + μ) P := by
    have := hZ.aemeasurable
    fun_prop
  have hind' : IndepFun (fun ω => toEuclideanLin W (Z ω) + μ) E P :=
    hind.comp (φ := fun z => toEuclideanLin W z + μ) (ψ := id) (by fun_prop) measurable_id
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [hind'.charFun_map_fun_add_eq_mul hA hE.aemeasurable, Pi.mul_apply,
    charFun_multivariateGaussian hS, hE.map_eq, charFun_multivariateGaussian hΨ]
  have hmap : P.map (fun ω => toEuclideanLin W (Z ω) + μ) =
      ((P.map Z).map (toEuclideanLin W)).map (· + μ) := by
    rw [Measure.map_map (by fun_prop) (continuous_toEuclideanLin W).measurable,
      AEMeasurable.map_map_of_aemeasurable (by fun_prop) hZ.aemeasurable]
    rfl
  rw [hmap, charFun_map_add_const, charFun_map_toEuclideanLin, hZ.map_eq, charFun_stdGaussian,
    ← Complex.ofReal_pow, norm_sq_toEuclideanLin_transpose, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [inner_zero_right, add_mulVec, dotProduct_add, real_inner_comm μ t]
  push_cast
  ring

/-- **The probabilistic PCA marginal.** Let $Z$ and $E$ be independent random vectors on a
probability space, with values in $\mathbb{R}^q$ and $\mathbb{R}^d$, such that $Z$ has the
standard Gaussian law $N(0, I_q)$ and $E$ has the isotropic law $N(0, \sigma^2 I_d)$ for a real
$\sigma^2 \ge 0$. Then for every real $d \times q$ matrix $W$ and every $\mu \in \mathbb{R}^d$, the
random vector $WZ + \mu + E$ has law $N(\mu, WW^\top + \sigma^2 I_d)$. -/
theorem ppca_map_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : Ω → EuclideanSpace ℝ (Fin q)} {E : Ω → EuclideanSpace ℝ (Fin d)} {σ2 : ℝ} (hσ : 0 ≤ σ2)
    (hZ : HasLaw Z (stdGaussian _) P) (hE : HasLaw E (multivariateGaussian 0 (σ2 • 1)) P)
    (hind : IndepFun Z E P) (W : Matrix (Fin d) (Fin q) ℝ) (μ : EuclideanSpace ℝ (Fin d)) :
    P.map (fun ω => toEuclideanLin W (Z ω) + μ + E ω) = multivariateGaussian μ (W * Wᵀ + σ2 • 1) :=
  map_eq_multivariateGaussian hZ hE
    (by rw [smul_one_eq_diagonal]; exact posSemidef_diagonal_iff.2 fun _ => hσ) hind W μ

/-- **The factor-analysis marginal.** Let $Z$ and $E$ be independent random vectors on a
probability space, with values in $\mathbb{R}^q$ and $\mathbb{R}^d$, such that $Z$ has the
standard Gaussian law $N(0, I_q)$ and $E$ has law $N(0, \operatorname{diag}\psi)$ for a vector
$\psi \in \mathbb{R}^d$ with $\psi_i \ge 0$ for all $i$. Then for every real $d \times q$ matrix
$W$ and every $\mu \in \mathbb{R}^d$, the random vector $WZ + \mu + E$ has law
$N(\mu, WW^\top + \operatorname{diag}\psi)$. -/
theorem factorAnalysis_map_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → EuclideanSpace ℝ (Fin q)} {E : Ω → EuclideanSpace ℝ (Fin d)}
    {ψ : Fin d → ℝ} (hψ : ∀ i, 0 ≤ ψ i) (hZ : HasLaw Z (stdGaussian _) P)
    (hE : HasLaw E (multivariateGaussian 0 (diagonal ψ)) P) (hind : IndepFun Z E P)
    (W : Matrix (Fin d) (Fin q) ℝ) (μ : EuclideanSpace ℝ (Fin d)) :
    P.map (fun ω => toEuclideanLin W (Z ω) + μ + E ω) =
      multivariateGaussian μ (W * Wᵀ + diagonal ψ) :=
  map_eq_multivariateGaussian hZ hE (posSemidef_diagonal_iff.2 hψ) hind W μ

end Cslib.MachineLearning.LatentVariable.ProbabilisticPCA
