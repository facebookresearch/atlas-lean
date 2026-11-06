/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.DiscreteSpectrum
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.LinearAlgebra.Dimension.Finrank

@[expose] public section

open TopologicalSpace MeasureTheory

namespace DirichletLaplacian

/-- **Smooth test functions.** For an open set $\Omega \subseteq \mathbb{R}^n$, the space of smooth
test functions on $\Omega$ is the real vector space of infinitely differentiable functions
$f : \mathbb{R}^n \to \mathbb{R}$ whose support is compact and contained in $\Omega$.

These functions form the core of the Dirichlet form. -/
abbrev SmoothTestSpace {n : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin n))) :=
  TestFunction Ω ℝ ⊤

/-- **Rayleigh quotient.** For a smooth test function $f$ on an open set
$\Omega \subseteq \mathbb{R}^n$, the Rayleigh quotient of $f$ is
$$R(f) = \frac{\int_{\mathbb{R}^n} \|Df(x)\|^2 \, dx}{\int_{\mathbb{R}^n} |f(x)|^2 \, dx},$$
where $\|Df(x)\|$ is the operator norm of the derivative of $f$ at $x$ (equal to
$|\nabla f(x)|$) and both integrals are against Lebesgue measure. For $f = 0$ the quotient
$0/0$ is read as $0$. -/
noncomputable def rayleighQuotient {n : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin n))}
    (f : SmoothTestSpace Ω) : ℝ :=
  (∫ x, ‖fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ ^ 2 ∂volume) /
    (∫ x, |f x| ^ 2 ∂volume)

/-- **Variational eigenvalue.** For an open set $\Omega \subseteq \mathbb{R}^n$ and an index
$j \ge 0$, the variational eigenvalue of $\Omega$ at index $j$ is the Courant–Fischer min–max
value
$$\lambda_j(\Omega) = \inf_V \, \sup_{f \in V,\ f \ne 0} R(f),$$
where $V$ ranges over the $(j+1)$-dimensional subspaces of the space of smooth test functions
on $\Omega$ and $R(f)$ is the Rayleigh quotient of $f$. Infima and suprema are taken in
$\mathbb{R}$, where an empty set, or a set unbounded in the relevant direction, has value $0$.

This is a definition only: it does not claim that the values are attained, nonnegative,
monotone in $j$, divergent, or eigenvalues of an operator. -/
noncomputable def variationalEigenvalue {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) (j : ℕ) : ℝ :=
  sInf {a : ℝ | ∃ V : Submodule ℝ (SmoothTestSpace Ω),
    Module.finrank ℝ ↥V = j + 1 ∧
      a = sSup {q : ℝ | ∃ f : ↥V,
        (f : SmoothTestSpace Ω) ≠ 0 ∧
          rayleighQuotient (f : SmoothTestSpace Ω) = q}}

end DirichletLaplacian

/-- **Dirichlet spectrum of an open set.** A nonnegative discrete spectrum $S = (S_j)_{j \ge 0}$
is the Dirichlet spectrum of an open set $\Omega \subseteq \mathbb{R}^n$ when
$S_j = \lambda_j(\Omega)$ for every $j \ge 0$, where $\lambda_j(\Omega)$ is the variational
eigenvalue of $\Omega$ at index $j$. -/
def NonnegativeDiscreteSpectrum.IsDirichletSpectrum {n : ℕ}
    (S : NonnegativeDiscreteSpectrum)
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ j, S j = DirichletLaplacian.variationalEigenvalue Ω j

namespace EuclideanLaplacian

/-- **Volume of the unit ball.** For $n \ge 0$, $\omega_n$ is the Lebesgue measure of the open
unit ball $\{x \in \mathbb{R}^n : |x| < 1\}$ of Euclidean space $\mathbb{R}^n$, as a real
number. -/
noncomputable def unitBallVolume (n : ℕ) : ℝ :=
  (volume : Measure (EuclideanSpace ℝ (Fin n))).real
    (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)

/-- **Volume of a domain.** For an open set $\Omega \subseteq \mathbb{R}^n$, the volume $|\Omega|$
is the Lebesgue measure of $\Omega$ taken as a real number, with $|\Omega| = 0$ when the
Lebesgue measure of $\Omega$ is infinite. -/
noncomputable def domainVolume {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) : ℝ :=
  (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Ω : Set _)

/-- **Semiclassical counting coefficient.** For an open set $\Omega \subseteq \mathbb{R}^n$, the
semiclassical counting coefficient is $\omega_n |\Omega| / (2\pi)^n$, where $\omega_n$ is the
volume of the unit ball in $\mathbb{R}^n$ and $|\Omega|$ is the Lebesgue measure of $\Omega$
taken as a real number, with $|\Omega| = 0$ when that measure is infinite. -/
noncomputable def semiclassicalCountingCoefficient {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) : ℝ :=
  unitBallVolume n * domainVolume Ω / (2 * Real.pi) ^ n

/-- **Pólya eigenvalue benchmark.** For an open set $\Omega \subseteq \mathbb{R}^n$ and an index
$j \ge 0$, the Pólya benchmark at index $j$ is
$$(2\pi)^2 \left(\frac{j+1}{\omega_n |\Omega|}\right)^{2/n},$$
where $\omega_n$ is the volume of the unit ball in $\mathbb{R}^n$ and $|\Omega|$ is the volume of
$\Omega$. Indices start at $0$, so index $j$ belongs to the $(j+1)$-st eigenvalue.

Division by zero is read as $0$: the exponent is $0$ when $n = 0$, and the base is $0$ when
$\omega_n |\Omega| = 0$. -/
noncomputable def polyaEigenvalueBenchmark {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) (j : ℕ) : ℝ :=
  (2 * Real.pi) ^ 2 *
    ((((j + 1 : ℕ) : ℝ) /
      (unitBallVolume n * domainVolume Ω)) ^ (2 / (n : ℝ)))

theorem unitBallVolume_nonneg (n : ℕ) : 0 ≤ unitBallVolume n :=
  measureReal_nonneg

theorem domainVolume_nonneg {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) : 0 ≤ domainVolume Ω :=
  measureReal_nonneg

theorem semiclassicalCountingCoefficient_nonneg {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    0 ≤ semiclassicalCountingCoefficient Ω := by
  unfold semiclassicalCountingCoefficient
  exact div_nonneg
    (mul_nonneg (unitBallVolume_nonneg n) (domainVolume_nonneg Ω))
    (pow_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg) n)

theorem polyaEigenvalueBenchmark_nonneg {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) (j : ℕ) :
    0 ≤ polyaEigenvalueBenchmark Ω j := by
  unfold polyaEigenvalueBenchmark
  exact mul_nonneg
    (pow_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg) 2)
    (Real.rpow_nonneg
      (div_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (unitBallVolume_nonneg n) (domainVolume_nonneg Ω))) _)

end EuclideanLaplacian
