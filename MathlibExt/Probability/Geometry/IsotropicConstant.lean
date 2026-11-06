/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Geometry.ThinShell
public import Mathlib.Analysis.Convex.Body
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Entropy-based isotropic constants

Source: `constants/20b.md` and Klartag--Lehec, arXiv:2412.15044v1,
Introduction, equations (1.2)--(1.6). Entropy uses natural logarithms.
-/

@[expose] public section

namespace MathlibExt.Probability.IsotropicConstant

open MeasureTheory
open scoped ENNReal
open scoped BigOperators

/-- **Covariance matrix.** For a measure $\mu$ on $\mathbb{R}^n$, the covariance matrix of $\mu$ is
the $n \times n$ real matrix whose $(i, j)$ entry is
$\int (x_i - m_i)(x_j - m_j) \, d\mu(x)$, where $m_i = \int x_i \, d\mu(x)$ is the mean of the
$i$-th coordinate.

Source: `constants/20b.md`, covariance definition. -/
noncomputable def covarianceMatrix {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ProbabilityTheory.covariance (fun x => x i) (fun x => x j) μ

/-- **Differential entropy.** For a function $f \colon \mathbb{R}^n \to \mathbb{R}$, usually the
Lebesgue density of a probability law, the differential entropy of $f$ is
$-\int_{\mathbb{R}^n} f(x) \log f(x) \, dx$, with the natural logarithm and $0 \log 0 = 0$.

Source: `constants/20b.md`, Ent(μ)=-∫f log f. -/
noncomputable def differentialEntropy {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  -(∫ x, f x * Real.log (f x))

/-- **Full-dimensional convex body.** For a natural number $n$, a full-dimensional convex body in
dimension $n$ is a nonempty compact convex set $K$ in the Euclidean space $\mathbb{R}^n$ whose
interior is nonempty, where $n$ is required to be positive.

Source: `constants/20b.md`, convex-body domain. -/
structure FullDimensionalBody (n : ℕ) where
  body : ConvexBody (EuclideanSpace ℝ (Fin n))
  dimension_pos : 0 < n
  interior_nonempty : (interior (body : Set (EuclideanSpace ℝ (Fin n)))).Nonempty

/-- **Log-concave law.** For a positive integer $n$, a log-concave law on $\mathbb{R}^n$ is a
probability measure $\mu$ on $\mathbb{R}^n$ together with a Lebesgue density $f$ of $\mu$ that is
log-concave: $f$ is measurable and nonnegative, and $f((1-t)x + ty) \ge f(x)^{1-t} f(y)^t$ for all
$x, y \in \mathbb{R}^n$ and $0 < t < 1$. Moreover every coordinate $x_i$ and every product
$x_i x_j$ is $\mu$-integrable, and $f \log f$ is Lebesgue integrable.

Source: `constants/20b.md`; finite moments and entropy integrability ensure the
displayed real integrals do not use the non-integrable default value. -/
structure LogConcaveLaw (n : ℕ) where
  dimension_pos : 0 < n
  law : Measure (EuclideanSpace ℝ (Fin n))
  probability : IsProbabilityMeasure law
  density : EuclideanSpace ℝ (Fin n) → ℝ
  logConcave : ThinShell.IsLogConcaveDensity density
  law_eq : law = volume.withDensity (fun x => ENNReal.ofReal (density x))
  moment_one : ∀ i : Fin n, Integrable (fun x => x i) law
  moment_two : ∀ i j : Fin n, Integrable (fun x => x i * x j) law
  entropy_integrable : Integrable (fun x => density x * Real.log (density x)) volume

/-- **Covariance matrices of log-concave laws are positive semidefinite.** For every log-concave
law $\mu$ on $\mathbb{R}^n$, the covariance matrix of $\mu$ is positive semidefinite.

The proof writes the quadratic form of the covariance matrix as the integral of the square of a
centered linear form. -/
theorem covarianceMatrix_posSemidef {n : ℕ} (μ : LogConcaveLaw n) :
    (covarianceMatrix μ.law).PosSemidef := by
  let : IsProbabilityMeasure μ.law := μ.probability
  let m : Fin n → ℝ := fun i => ∫ x, x i ∂μ.law
  have hc : ∀ i j : Fin n, Integrable (fun x => (x i - m i) * (x j - m j)) μ.law := by
    intro i j
    convert (((μ.moment_two i j).sub ((μ.moment_one i).mul_const (m j))).sub
      ((μ.moment_one j).const_mul (m i))).add (integrable_const (m i * m j)) using 1
    ext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hHerm : (covarianceMatrix μ.law).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, covarianceMatrix, star_trivial,
      ProbabilityTheory.covariance_comm]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
  intro v
  have hcv : ∀ i j : Fin n,
      Integrable (fun x => v i * (((x i - m i) * (x j - m j)) * v j)) μ.law := by
    intro i j
    exact ((hc i j).mul_const (v j)).const_mul (v i)
  have hs : ∀ i : Fin n, Integrable
      (fun x => ∑ j : Fin n, v i * (((x i - m i) * (x j - m j)) * v j)) μ.law := by
    intro i
    exact integrable_finsetSum Finset.univ (fun j _ => hcv i j)
  have hinner (i : Fin n) :
      (∑ j : Fin n, ∫ x, v i * (((x i - m i) * (x j - m j)) * v j) ∂μ.law) =
        ∫ x, ∑ j : Fin n, v i * (((x i - m i) * (x j - m j)) * v j) ∂μ.law :=
    (integral_finsetSum Finset.univ (fun j _ => hcv i j)).symm
  have heq : star v ⬝ᵥ (covarianceMatrix μ.law).mulVec v =
      ∫ x, (∑ i : Fin n, v i * (x i - m i)) ^ 2 ∂μ.law := by
    simp only [Matrix.mulVec, dotProduct, Pi.star_apply, star_trivial, covarianceMatrix,
      ProbabilityTheory.covariance]
    simp_rw [Finset.mul_sum, ← integral_mul_const, ← integral_const_mul]
    change (∑ i : Fin n, ∑ j : Fin n,
      ∫ x, v i * (((x i - m i) * (x j - m j)) * v j) ∂μ.law) = _
    simp_rw [hinner]
    rw [← integral_finsetSum Finset.univ (fun i _ => hs i)]
    congr 1
    ext x
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    congr 1
    ext i
    congr 1
    ext j
    ring
  rw [heq]
  apply integral_nonneg
  intro x
  positivity

theorem covarianceMatrix_det_nonneg {n : ℕ} (μ : LogConcaveLaw n) :
    0 ≤ (covarianceMatrix μ.law).det :=
  (covarianceMatrix_posSemidef μ).det_nonneg

/-- **Isotropic log-concave laws have identity covariance.** If $\mu$ is an isotropic log-concave
probability measure on $\mathbb{R}^n$, then the covariance matrix of $\mu$ is the $n \times n$
identity matrix. -/
theorem covarianceMatrix_eq_one_of_isIsotropic {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hμ : ThinShell.IsIsotropicLogConcave μ) :
    covarianceMatrix μ = 1 := by
  ext i j
  simp only [covarianceMatrix, ProbabilityTheory.covariance, (hμ.2.2.1 i).2,
    (hμ.2.2.1 j).2, sub_zero, Matrix.one_apply]
  exact (hμ.2.2.2 i j).2

/-- **Uniform distribution on a convex body.** For a full-dimensional convex body $K$ in
$\mathbb{R}^n$, the uniform law on $K$ is the probability measure obtained by restricting
Lebesgue measure to $K$ and dividing by the volume of $K$; it gives a set $A$ the mass
$\operatorname{vol}(A \cap K) / \operatorname{vol}(K)$. -/
noncomputable def bodyLaw {n : ℕ} (K : FullDimensionalBody n) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  ProbabilityTheory.cond volume (K.body : Set (EuclideanSpace ℝ (Fin n)))

/-- **Isotropic constant of a convex body.** For a full-dimensional convex body $K$ in
$\mathbb{R}^n$, let $\operatorname{Cov}(K)$ be the covariance matrix of the uniform probability
law on $K$ and let $\operatorname{vol}(K)$ be the Lebesgue volume of $K$. The isotropic constant
of $K$ is the real number
$L_K = \left(\det \operatorname{Cov}(K) / \operatorname{vol}(K)^2\right)^{1/(2n)}$. -/
noncomputable def bodyIsotropicConstant {n : ℕ} (K : FullDimensionalBody n) : ℝ :=
  Real.rpow ((covarianceMatrix (bodyLaw K)).det /
    (volume (K.body : Set (EuclideanSpace ℝ (Fin n)))).toReal ^ 2)
    (1 / (2 * (n : ℝ)))

/-- **Isotropic constant of a log-concave law.** For a log-concave law $\mu$ on $\mathbb{R}^n$ with
Lebesgue density $f$, the isotropic constant of $\mu$ is
$L_\mu = e^{-h(f)/n} (\det \mathrm{Cov}(\mu))^{1/(2n)}$, where
$h(f) = -\int_{\mathbb{R}^n} f \log f$ is the differential entropy of $f$ and $\mathrm{Cov}(\mu)$
is the covariance matrix of the coordinates under $\mu$. -/
noncomputable def lawIsotropicConstant {n : ℕ} (μ : LogConcaveLaw n) : ℝ :=
  Real.exp (-differentialEntropy μ.density / (n : ℝ)) *
    Real.rpow (covarianceMatrix μ.law).det (1 / (2 * (n : ℝ)))

/-- **Supremum of isotropic constants in a fixed dimension.** For $n \in \mathbb{N}$, this is
$\sup_K L_K \in [0, \infty]$, the supremum of the isotropic constants $L_K$ over all
full-dimensional convex bodies $K$ in $\mathbb{R}^n$. Full-dimensional convex bodies are taken
only in dimension $n \ge 1$, so for $n = 0$ the supremum is over the empty family and is $0$. -/
noncomputable def dimensionBodySupremum (n : ℕ) : ℝ≥0∞ :=
  ⨆ K : FullDimensionalBody n, ENNReal.ofReal (bodyIsotropicConstant K)

/-- **Supremum of entropic isotropic constants in a fixed dimension.** For $n \in \mathbb{N}$, this
is $\sup_\mu L_\mu \in [0, \infty]$, the supremum of the isotropic constants
$L_\mu = e^{-\operatorname{Ent}(f)/n} (\det \operatorname{Cov}(\mu))^{1/(2n)}$ over all
log-concave laws $\mu$ on $\mathbb{R}^n$, where $f$ is the log-concave Lebesgue density of $\mu$,
$\operatorname{Ent}(f)$ its differential entropy and $\operatorname{Cov}(\mu)$ its covariance
matrix. Here a log-concave law is a probability measure on $\mathbb{R}^n$ with $n \ge 1$, with
finite second moments and with $f \log f$ integrable, so for $n = 0$ the supremum is over the
empty family and is $0$. -/
noncomputable def dimensionLawSupremum (n : ℕ) : ℝ≥0∞ :=
  ⨆ μ : LogConcaveLaw n, ENNReal.ofReal (lawIsotropicConstant μ)

/-- **Supremum of isotropic constants of convex bodies.** This is the value
$\sup_{n \ge 1} \sup_K L_K \in [0, \infty]$, where for each dimension $n \ge 1$ the inner
supremum runs over all full-dimensional convex bodies $K$ in $\mathbb{R}^n$ and $L_K$ is the
isotropic constant of $K$.

Source: `constants/20b.md`, the sharp-value body constant. -/
noncomputable def bodySupremum : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ (_ : 0 < n), dimensionBodySupremum n

/-- **Centrally symmetric convex body.** For a natural number $n$, a full-dimensional convex
body $K \subseteq \mathbb{R}^n$ is centrally symmetric when $K = -K$, that is, for every
$x \in \mathbb{R}^n$, $x \in K$ if and only if $-x \in K$.

Source: arXiv:2412.15044v1, Introduction after Theorem 1.2. -/
def IsCentrallySymmetric {n : ℕ} (K : FullDimensionalBody n) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n),
    x ∈ (K.body : Set (EuclideanSpace ℝ (Fin n))) ↔
      -x ∈ (K.body : Set (EuclideanSpace ℝ (Fin n)))

/-- **Supremum of isotropic constants of symmetric convex bodies.** This is the value
$\sup_{n \ge 1} \sup_K L_K \in [0, \infty]$, where for each dimension $n \ge 1$ the inner
supremum runs over the full-dimensional convex bodies $K$ in $\mathbb{R}^n$ that are centrally
symmetric, that is $K = -K$, and $L_K$ is the isotropic constant of $K$. -/
noncomputable def centrallySymmetricBodySupremum : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ (_ : 0 < n), ⨆ K : FullDimensionalBody n,
    ⨆ (_ : IsCentrallySymmetric K), ENNReal.ofReal (bodyIsotropicConstant K)

/-- **Squared-radius thin-shell width.** For a natural number $n$, the squared-radius thin-shell
width in dimension $n$ is the supremum, in $[0, \infty]$, of
$\left(\int (|x|^2 - n)^2 \, d\mu(x) / n\right)^{1/2}$ (with $0/0 = 0$) over all isotropic
log-concave probability measures $\mu$ on $\mathbb{R}^n$, that is, those with a log-concave
Lebesgue density, mean zero and identity covariance.

It measures the fluctuation of the squared radius $|x|^2$, not of the radius $|x|$. -/
noncomputable def squaredRadiusThinShellWidth (n : ℕ) : ℝ≥0∞ :=
  ⨆ μ : Measure (EuclideanSpace ℝ (Fin n)), ⨆ (_ : ThinShell.IsIsotropicLogConcave μ),
    ENNReal.rpow (ThinShell.normalizedRadiusVariance μ) (1 / 2)

/-- **Supremum of the isotropic constant over full-dimensional log-concave laws.** This is the
supremum, in $[0, \infty]$, of the isotropic constant
$L_\mu = e^{-h(f)/n} (\det \mathrm{Cov}(\mu))^{1/(2n)}$ over all positive integers $n$ and all
log-concave laws $\mu$ on $\mathbb{R}^n$ with Lebesgue density $f$, where
$h(f) = -\int_{\mathbb{R}^n} f \log f$ is the differential entropy of $f$ and $\mathrm{Cov}(\mu)$
is the covariance matrix of the coordinates under $\mu$.

Each such law has a density on all of $\mathbb{R}^n$, so laws supported on a proper affine
subspace are not included here. -/
noncomputable def fullDimensionalLawSupremum : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ (_ : 0 < n), dimensionLawSupremum n

theorem bodyIsotropicConstant_le_dimensionSupremum {n : ℕ} (K : FullDimensionalBody n) :
    ENNReal.ofReal (bodyIsotropicConstant K) ≤ dimensionBodySupremum n :=
  le_iSup (fun K : FullDimensionalBody n => ENNReal.ofReal (bodyIsotropicConstant K)) K

theorem lawIsotropicConstant_le_dimensionSupremum {n : ℕ} (μ : LogConcaveLaw n) :
    ENNReal.ofReal (lawIsotropicConstant μ) ≤ dimensionLawSupremum n :=
  le_iSup (fun μ : LogConcaveLaw n => ENNReal.ofReal (lawIsotropicConstant μ)) μ

theorem dimensionBodySupremum_le_bodySupremum {n : ℕ} (hn : 0 < n) :
    dimensionBodySupremum n ≤ bodySupremum :=
  le_iSup_of_le n (le_iSup (fun _ : 0 < n => dimensionBodySupremum n) hn)

theorem symmetricBodyIsotropicConstant_le_supremum {n : ℕ}
    (K : FullDimensionalBody n) (hK : IsCentrallySymmetric K) :
    ENNReal.ofReal (bodyIsotropicConstant K) ≤ centrallySymmetricBodySupremum :=
  le_iSup_of_le n (le_iSup_of_le K.dimension_pos (le_iSup_of_le K
    (le_iSup (fun _ : IsCentrallySymmetric K =>
      ENNReal.ofReal (bodyIsotropicConstant K)) hK)))

theorem squaredRadiusThinShellWidth_le_varianceConstant (n : ℕ) (hn : 0 < n) :
    squaredRadiusThinShellWidth n ≤ ENNReal.rpow ThinShell.thinShellVarianceConstant (1 / 2) := by
  apply iSup_le
  intro μ
  apply iSup_le
  intro hμ
  exact ENNReal.rpow_le_rpow (ThinShell.normalizedRadiusVariance_le_constant hn hμ)
    (by norm_num)

theorem dimensionLawSupremum_le_fullSupremum {n : ℕ} (hn : 0 < n) :
    dimensionLawSupremum n ≤ fullDimensionalLawSupremum :=
  le_iSup_of_le n (le_iSup (fun _ : 0 < n => dimensionLawSupremum n) hn)

end MathlibExt.Probability.IsotropicConstant
