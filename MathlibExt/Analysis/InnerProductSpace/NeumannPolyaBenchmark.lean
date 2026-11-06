/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.DirichletSpectrum

@[expose] public section

open TopologicalSpace

namespace EuclideanLaplacian

/-- **Neumann Pólya benchmark.** For an open set $\Omega \subseteq \mathbb{R}^n$ and a natural
number $j$, the Neumann Pólya benchmark of $\Omega$ at index $j$ is the real number
$(2\pi)^2 \left(j / (\omega_n |\Omega|)\right)^{2/n}$, where $\omega_n$ is the volume of the unit
ball of $\mathbb{R}^n$, $|\Omega|$ is the volume of $\Omega$, the power is the real power with
exponent $2/n$, and a quotient by $0$ is read as $0$.

The index is zero-based: $j$ is the source's one-based eigenvalue number minus one, so index
zero records the constant Neumann mode in positive dimension. -/
noncomputable def neumannPolyaEigenvalueBenchmark {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) (j : ℕ) : ℝ :=
  (2 * Real.pi) ^ 2 *
    ((((j : ℕ) : ℝ) /
      (unitBallVolume n * domainVolume Ω)) ^ (2 / (n : ℝ)))

theorem neumannPolyaEigenvalueBenchmark_nonneg {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) (j : ℕ) :
    0 ≤ neumannPolyaEigenvalueBenchmark Ω j := by
  unfold neumannPolyaEigenvalueBenchmark
  exact mul_nonneg
    (pow_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg) 2)
    (Real.rpow_nonneg
      (div_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (unitBallVolume_nonneg n) (domainVolume_nonneg Ω))) _)

/-- **Neumann and Dirichlet Pólya benchmarks agree after an index shift.** For every open set
$\Omega \subseteq \mathbb{R}^n$ and every natural number $j$, the Neumann Pólya benchmark of
$\Omega$ at index $j + 1$ equals the Pólya eigenvalue benchmark of $\Omega$ at index $j$.

In the source's one-based numbering, the Neumann index $j + 2$ has the same Weyl benchmark as
the Dirichlet index $j + 1$. -/
@[simp] theorem neumannPolyaEigenvalueBenchmark_succ {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) (j : ℕ) :
    neumannPolyaEigenvalueBenchmark Ω (j + 1) =
      polyaEigenvalueBenchmark Ω j :=
  rfl

end EuclideanLaplacian
