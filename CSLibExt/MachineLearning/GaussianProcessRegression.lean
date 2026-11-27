/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.GaussianConditioning

/-!
# Gaussian-process regression: the posterior on finitely many points

Gaussian-process regression with Gaussian noise (Rasmussen and Williams, *Gaussian Processes for
Machine Learning*, Section 2.2): a zero-mean prior `f ~ GP(0, k)` and targets `y = f(x) + ε` with
`ε ~ N(0, σ² I)`. On finitely many test inputs `x*` and training inputs `x`, the test values and the
targets are jointly Gaussian with covariance `[[K(x*, x*), K(x*, x)], [K(x, x*), K(x, x) + σ² I]]`
(`jointCov`), and the posterior is Gaussian with the predictive mean and covariance

  `K(x*, x) (K(x, x) + σ² I)⁻¹ y` and `K(x*, x*) - K(x*, x) (K(x, x) + σ² I)⁻¹ K(x, x*)`.

Main results:

* `condDistrib_test_given_targets`: **the GP posterior**, as Mathlib's `condDistrib`, a corollary of
  the Schur-complement formula `MetaMathlibExt.condDistrib_multivariateGaussian`, for a covariance
  kernel (positive semidefinite kernel matrix on all the inputs) and noise variance `σ² > 0`.
* `jointCov_eq_add`, `jointCov_posSemidef`, `kernelMatrix_posSemidef_train`: the joint covariance
  is the kernel matrix plus noise on the training block, hence positive semidefinite.
* `isUnit_det_kernelMatrix_add`: `K + σ² I` is invertible for a positive semidefinite kernel
  matrix and `σ² > 0`.

The joint prior is the hypothesis: the joint vector `V = (f(x*), y)` on `τ ⊕ ν` has law
`N(0, jointCov k σ² x* x)`. The test values and targets are its blocks `testPart`, `targetPart`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.GaussianProcessRegression

open MeasureTheory ProbabilityTheory Matrix WithLp MetaMathlibExt
open scoped MatrixOrder

variable {X : Type*} {τ ν : Type*} [Fintype τ] [DecidableEq τ] [Fintype ν] [DecidableEq ν]

/-- **Kernel matrix.** For a kernel $k : X \times X \to \mathbb{R}$ and two families of inputs
$a = (a_i)_{i \in \alpha}$ and $b = (b_j)_{j \in \beta}$ in $X$, the kernel (Gram) matrix
$K(a, b)$ is the $\alpha \times \beta$ real matrix with entries $K(a, b)_{ij} = k(a_i, b_j)$. -/
def kernelMatrix (k : X → X → ℝ) {α β : Type*} (a : α → X) (b : β → X) : Matrix α β ℝ :=
  Matrix.of fun i j => k (a i) (b j)

/-- The joint prior covariance of the test values `f(x*)` and the noisy training targets
`y = f(x) + ε`, `ε ~ N(0, σ² I)`: `[[K(x*, x*), K(x*, x)], [K(x, x*), K(x, x) + σ² I]]`. -/
def jointCov (k : X → X → ℝ) (σ2 : ℝ) (xt : τ → X) (xs : ν → X) :
    Matrix (τ ⊕ ν) (τ ⊕ ν) ℝ :=
  fromBlocks (kernelMatrix k xt xt) (kernelMatrix k xt xs) (kernelMatrix k xs xt)
    (kernelMatrix k xs xs + σ2 • 1)

/-- **Test-value projection.** For finite index sets $\tau$ (test inputs) and $\nu$ (training
inputs), the test-value projection is the $\tau \times (\tau \sqcup \nu)$ real matrix with the
identity matrix on the columns indexed by $\tau$ and a zero block on the columns indexed by $\nu$.
It sends a joint vector $(u, y)$ with $u \in \mathbb{R}^{\tau}$ and $y \in \mathbb{R}^{\nu}$ to its
block of test values $u$. -/
noncomputable def testPart : Matrix τ (τ ⊕ ν) ℝ := blockRow 1 0

/-- **Training-target projection.** For finite index sets $\tau$ (test inputs) and $\nu$
(training inputs), the training-target projection is the $\nu \times (\tau \sqcup \nu)$ real
matrix with a zero block on the columns indexed by $\tau$ and the identity matrix on the columns
indexed by $\nu$. It sends a joint vector $(u, y)$ with $u \in \mathbb{R}^{\tau}$ and
$y \in \mathbb{R}^{\nu}$ to its block of training targets $y$. -/
noncomputable def targetPart : Matrix ν (τ ⊕ ν) ℝ := blockRow 0 1

/-- **Regularized kernel matrices are invertible.** Let $k : X \times X \to \mathbb{R}$ be a kernel
and $x = (x_j)_{j \in \nu}$ a finite family of inputs whose kernel matrix
$K = (k(x_i, x_j))_{i, j \in \nu}$ is positive semidefinite. Then for every $\sigma^2 > 0$ the
matrix $K + \sigma^2 I$ has nonzero determinant, so it is invertible. -/
theorem isUnit_det_kernelMatrix_add (k : X → X → ℝ) (xs : ν → X)
    (hK : (kernelMatrix k xs xs).PosSemidef)
    {σ2 : ℝ} (hσ : 0 < σ2) : IsUnit (kernelMatrix k xs xs + σ2 • 1).det :=
  (PosDef.posSemidef_add hK (PosDef.one.smul hσ)).det_pos.ne'.isUnit

omit [Fintype τ] [Fintype ν] in
/-- **The joint covariance as a kernel matrix plus noise.** For a kernel
$k : X \times X \to \mathbb{R}$, a real number $\sigma^2$, test inputs $x^* = (x^*_i)_{i \in \tau}$
and training inputs $x = (x_j)_{j \in \nu}$, the joint covariance of $k$, $\sigma^2$, $x^*$ and $x$
equals $K + D$, where $K$ is the kernel matrix of the combined family $(x^*, x)$ indexed by
$\tau \sqcup \nu$ and $D$ is the diagonal matrix with entry $0$ at each test index and $\sigma^2$
at each training index. -/
theorem jointCov_eq_add (k : X → X → ℝ) (σ2 : ℝ) (xt : τ → X) (xs : ν → X) :
    jointCov k σ2 xt xs = kernelMatrix k (Sum.elim xt xs) (Sum.elim xt xs) +
      diagonal (Sum.elim 0 fun _ => σ2) := by
  ext a b
  cases a <;> cases b <;> simp [jointCov, kernelMatrix, diagonal, Matrix.one_apply]

omit [Fintype τ] [Fintype ν] [DecidableEq τ] in
/-- **The joint covariance is positive semidefinite.** Let $k : X \times X \to \mathbb{R}$ be a
kernel, let $x^* = (x^*_i)_{i \in \tau}$ and $x = (x_j)_{j \in \nu}$ be families of test and
training inputs, and let $\sigma^2 \ge 0$. If the kernel matrix of the combined family $(x^*, x)$,
indexed by $\tau \sqcup \nu$, is positive semidefinite, then the joint covariance of $k$,
$\sigma^2$, $x^*$ and $x$ is positive semidefinite. -/
theorem jointCov_posSemidef (k : X → X → ℝ) {σ2 : ℝ} (hσ : 0 ≤ σ2) (xt : τ → X) (xs : ν → X)
    (hk : (kernelMatrix k (Sum.elim xt xs) (Sum.elim xt xs)).PosSemidef) :
    (jointCov k σ2 xt xs).PosSemidef := by
  classical
  rw [jointCov_eq_add]
  refine hk.add (posSemidef_diagonal_iff.2 fun a => ?_)
  cases a <;> simp [hσ]

omit [Fintype τ] [DecidableEq τ] [Fintype ν] [DecidableEq ν] in
/-- **Training blocks of positive semidefinite kernel matrices.** Let
$k : X \times X \to \mathbb{R}$ be a kernel and let $x^* = (x^*_i)_{i \in \tau}$ and
$x = (x_j)_{j \in \nu}$ be families of inputs. If the kernel matrix of the combined family
$(x^*, x)$, indexed by $\tau \sqcup \nu$, is positive semidefinite, then so is the kernel matrix
$(k(x_i, x_j))_{i, j \in \nu}$ of $x$. -/
theorem kernelMatrix_posSemidef_train (k : X → X → ℝ) (xt : τ → X) (xs : ν → X)
    (hk : (kernelMatrix k (Sum.elim xt xs) (Sum.elim xt xs)).PosSemidef) :
    (kernelMatrix k xs xs).PosSemidef :=
  hk.submatrix Sum.inr

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The Gaussian-process posterior.** Let $k : X \times X \to \mathbb{R}$ be a kernel, let
$x^* = (x^*_i)_{i \in \tau}$ (test inputs) and $x = (x_j)_{j \in \nu}$ (training inputs) be
finite families in $X$, and write $K(a, b)$ for the kernel matrix $(k(a_i, b_j))_{i, j}$. Assume
that the kernel matrix of the combined family $(x^*, x)$, indexed by $\tau \sqcup \nu$, is
positive semidefinite, and let $\sigma^2 > 0$. Let $V$ be a measurable random vector in
$\mathbb{R}^{\tau \sqcup \nu}$ on a probability space whose law is the Gaussian $N(0, \Sigma)$,
where $\Sigma$ is the joint covariance of $k$, $\sigma^2$, $x^*$ and $x$, and let $F$ (the test
values) and $Y$ (the training targets), random vectors in $\mathbb{R}^{\tau}$ and
$\mathbb{R}^{\nu}$, be the test and training blocks of $V$. Then for almost every $y$ with respect
to the law of $Y$, the conditional distribution of $F$ given $Y = y$ is the Gaussian with mean
$K(x^*, x) (K(x, x) + \sigma^2 I)^{-1} y$ and covariance
$K(x^*, x^*) - K(x^*, x) (K(x, x) + \sigma^2 I)^{-1} K(x, x^*)$. -/
theorem condDistrib_test_given_targets (k : X → X → ℝ) {σ2 : ℝ} (hσ : 0 < σ2) (xt : τ → X)
    (xs : ν → X) (hk : (kernelMatrix k (Sum.elim xt xs) (Sum.elim xt xs)).PosSemidef)
    {V : Ω → EuclideanSpace ℝ (τ ⊕ ν)} (hV : Measurable V)
    (hlaw : P.map V = multivariateGaussian 0 (jointCov k σ2 xt xs)) :
    ∀ᵐ y ∂P.map (fun ω => toEuclideanLin (targetPart (τ := τ)) (V ω)),
      condDistrib (fun ω => toEuclideanLin (testPart (ν := ν)) (V ω))
          (fun ω => toEuclideanLin (targetPart (τ := τ)) (V ω)) P y =
        multivariateGaussian
          (toEuclideanLin (kernelMatrix k xt xs * (kernelMatrix k xs xs + σ2 • 1)⁻¹) y)
          (kernelMatrix k xt xt -
            kernelMatrix k xt xs * (kernelMatrix k xs xs + σ2 • 1)⁻¹ * kernelMatrix k xs xt) := by
  have hK := isUnit_det_kernelMatrix_add k xs (kernelMatrix_posSemidef_train k xt xs hk) hσ
  have h := condDistrib_multivariateGaussian (ι := τ) (κ := ν) hV
    (jointCov_posSemidef k hσ.le xt xs hk) hlaw (by simpa [jointCov] using hK)
  simp only [jointCov, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, map_zero, sub_zero, zero_add] at h
  exact h

end Cslib.MachineLearning.GaussianProcessRegression
