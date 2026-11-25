/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KLS source bounds and comparison requests
-/
module

import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Geometry.KLS
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section

open MeasureTheory
open scoped ENNReal
open MathlibExt.Probability.ThinShell

namespace MathlibExt.Probability.KLS

/-- **Kannan–Lovász–Simonovits bound on the KLS constant.** There are a real $C > 0$ and an
integer $N \ge 3$ such that for every $n \ge N$ the dimensional KLS constant
$\psi_n \in [0, \infty]$ satisfies $\psi_n \le C \sqrt{n}$.

Source: Kannan, Lovasz and Simonovits, DCG 13 (1995), 541--560;
optimizationproblems `constants/20c.md`, KLS1995 row. -/
public theorem_wanted kannanLovaszSimonovits1995_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      dimensionalKlsConstant n ≤ ENNReal.ofReal (C * Real.sqrt n)

/-- **Lee–Vempala bound on the KLS constant.** There are a real $C > 0$ and an integer $N \ge 3$
such that for every $n \ge N$ the dimensional KLS constant $\psi_n \in [0, \infty]$ satisfies
$\psi_n \le C n^{1/4}$.

Source: Lee and Vempala, Ann. of Math. 199 (2024), 1--104;
optimizationproblems `constants/20c.md`, LV2024 row. -/
public theorem_wanted leeVempala2024_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      dimensionalKlsConstant n ≤ ENNReal.ofReal (C * Real.rpow (n : ℝ) (1 / 4))

/-- **Chen's subpolynomial bound on the KLS constant, weaker form.** There are a real $C > 0$ and
an integer $N \ge 3$ such that for every $n \ge N$ the dimensional KLS constant
$\psi_n \in [0, \infty]$ satisfies $\psi_n \le \exp\bigl(C \sqrt{\log n} \, \log \log n\bigr)$.

Source: Chen, GAFA 31 (2021), 34--61; optimizationproblems `constants/20c.md`.
Jambulapati--Lee--Vempala v1 quotes the stronger exponent `sqrt(log n * log(log n))`. -/
public theorem_wanted chen2021_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      dimensionalKlsConstant n ≤
        ENNReal.ofReal (Real.exp (C * Real.sqrt (Real.log n) * Real.log (Real.log n)))

/-- **Klartag–Lehec polylogarithmic bound on the KLS constant.** There are a real $C > 0$ and an
integer $N \ge 3$ such that for every $n \ge N$ the dimensional KLS constant
$\psi_n \in [0, \infty]$ satisfies $\psi_n \le C (\log n)^5$.

Source: Klartag and Lehec, GAFA 32 (2022), 1134--1159;
optimizationproblems `constants/20c.md`, KL2022 row. -/
public theorem_wanted klartagLehec2022_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      dimensionalKlsConstant n ≤ ENNReal.ofReal (C * Real.rpow (Real.log n) 5)

/-- **Jambulapati–Lee–Vempala polylogarithmic bound on the KLS constant.** Let
$\alpha = 1 + \bigl(1 + 7\sqrt{2} + \sqrt{53 - 4\sqrt{2}}\bigr)/8$. There are a real $C > 0$ and an
integer $N \ge 3$ such that for every $n \ge N$ the dimensional KLS constant
$\psi_n \in [0, \infty]$ satisfies $\psi_n \le C (\log n)^{\alpha}$.

The exponent is kept in exact algebraic form rather than as a rounded decimal.

Source: arXiv:2208.11644v1, Theorem 22 and the preceding KLS/thin-shell comparison. -/
public theorem_wanted jambulapatiLeeVempala2022_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      dimensionalKlsConstant n ≤ ENNReal.ofReal
        (C * Real.rpow (Real.log n)
          (1 + (1 + 7 * Real.sqrt 2 + Real.sqrt (53 - 4 * Real.sqrt 2)) / 8))

/-- **Lehec's reported polylogarithmic bound on the KLS constant, weakened.** There are a real
$C > 0$ and an integer $N \ge 3$ such that for every $n \ge N$ the dimensional KLS constant
$\psi_n \in [0, \infty]$ satisfies $\psi_n \le C (\log n)^{3.083}$.

The exponent $3.083$ lies just above Lehec's reported exponent $3.082\ldots$, which the primary
gives only to this decimal precision; $3.083$ is not claimed to be the exact exponent.

Source: Klartag, arXiv:2303.14938v1, Introduction, personal-communication paragraph. -/
public theorem_wanted lehec_reported_bound_weaker_specialization :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      dimensionalKlsConstant n ≤ ENNReal.ofReal (C * Real.rpow (Real.log n) (3083 / 1000))

/-- **Klartag's square-root-logarithmic bound on the KLS constant.** There is a real $C > 0$ such
that for every integer $n \ge 2$ the dimensional KLS constant $\psi_n \in [0, \infty]$ satisfies
$\psi_n \le C \sqrt{\log n}$.

Source: Klartag, arXiv:2303.14938v1, Theorem 1.2. -/
public theorem_wanted klartag2023_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      dimensionalKlsConstant n ≤ ENNReal.ofReal (C * Real.sqrt (Real.log n))

/-- **Inverse Cheeger constant of the standard Gaussian.** For every $n \ge 1$, the standard
Gaussian measure on $\mathbb{R}^n$ has inverse Cheeger constant exactly $\sqrt{\pi/2}$.

Source: optimizationproblems `constants/20c.md`, classical Gaussian row;
the Gaussian isoperimetric theorem supplies the minimizing half-space claim. -/
public theorem_wanted stdGaussian_inverseCheeger (n : ℕ) (hn : 0 < n) :
    inverseCheegerConstant
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))) =
        ENNReal.ofReal (Real.sqrt (Real.pi / 2))

/-- **A lower bound for the KLS constant.** The KLS constant is at least $\sqrt{\pi/2}$.

The bound comes from the standard Gaussian measure in any dimension $n \ge 1$, whose inverse Cheeger
constant is $\sqrt{\pi/2}$.

Source: optimizationproblems `constants/20c.md`, classical Gaussian lower-bound row. -/
public theorem_wanted sqrtPiDivTwo_le_klsConstant :
    ENNReal.ofReal (Real.sqrt (Real.pi / 2)) ≤ klsConstant

/-- **Lower Poincaré–Cheeger comparison with coefficient 1/π.** Let $n \ge 1$ and let $\mu$ be an
isotropic log-concave probability measure on $\mathbb{R}^n$, with inverse Cheeger constant
$\psi(\mu) \in [0, \infty]$ and smooth Poincaré constant $C_P(\mu) \in [0, \infty]$. Then
$\frac{1}{\pi} \psi(\mu)^2 \le C_P(\mu)$.

Source: optimizationproblems `constants/20c.md`, Poincare comparison display.
Klartag arXiv:2303.14938v1 states the weaker lower coefficient `1/9`, not `1/pi`. -/
public theorem_wanted catalogue_poincare_lower_bound {n : ℕ} (hn : 0 < n)
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hμ : IsIsotropicLogConcave μ) :
    ENNReal.ofReal (1 / Real.pi) * inverseCheegerConstant μ ^ 2 ≤
      smoothPoincareConstant μ

/-- **Lower Poincaré–Cheeger comparison with coefficient 1/9.** Let $n \ge 1$ and let $\mu$ be an
isotropic log-concave probability measure on $\mathbb{R}^n$, with inverse Cheeger constant
$\psi(\mu) \in [0, \infty]$ and smooth Poincaré constant $C_P(\mu) \in [0, \infty]$. Then
$\frac{1}{9} \psi(\mu)^2 \le C_P(\mu)$.

Source: Klartag, arXiv:2303.14938v1, equation comparing `psi` and `C_P`.
The locally Lipschitz-to-smooth approximation remains part of the requested proof. -/
public theorem_wanted klartag2023_poincare_lower_bound {n : ℕ} (hn : 0 < n)
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hμ : IsIsotropicLogConcave μ) :
    ENNReal.ofReal (1 / 9) * inverseCheegerConstant μ ^ 2 ≤
      smoothPoincareConstant μ

/-- **Cheeger's inequality for isotropic log-concave measures.** Let $n \ge 1$, let $\mu$ be an
isotropic log-concave probability measure on $\mathbb{R}^n$, and let $\psi_\mu \in [0, \infty]$ be
the inverse Cheeger constant of $\mu$. Then the smooth Poincaré constant of $\mu$ is at most
$4 \psi_\mu^2$.

Source: optimizationproblems `constants/20c.md`, comparison display, and
Klartag, arXiv:2303.14938v1, Introduction. -/
public theorem_wanted poincare_cheeger_upper_bound {n : ℕ} (hn : 0 < n)
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hμ : IsIsotropicLogConcave μ) :
    smoothPoincareConstant μ ≤ 4 * inverseCheegerConstant μ ^ 2

/-- **Dimensional KLS constant versus thin-shell variance, up to a squared logarithm.** Let
$\Sigma \in [0, \infty]$ be the thin-shell variance constant: the supremum, over all dimensions
$m \ge 1$ and all isotropic log-concave probability measures $\mu$ on $\mathbb{R}^m$, of
$\frac{1}{m} \int (\lVert x \rVert^2 - m)^2 \, d\mu(x)$. There is a real $C > 0$ such that for
every integer $n \ge 3$ the dimensional KLS constant $\psi_n \in [0, \infty]$ satisfies
$\psi_n^2 \le C (\log n)^2 \, \Sigma$.

Source: Jambulapati--Lee--Vempala, arXiv:2208.11644v1, KLS/thin-shell comparison. -/
public theorem_wanted kls_le_thinShell_variance_log_squared :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
      dimensionalKlsConstant n ^ 2 ≤
        ENNReal.ofReal (C * Real.log n ^ 2) * thinShellVarianceConstant

end MathlibExt.Probability.KLS
