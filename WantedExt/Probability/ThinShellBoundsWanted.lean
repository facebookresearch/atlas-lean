/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Established thin-shell bounds
-/
module

import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Geometry.ThinShell
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Uniform

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MathlibExt.Probability.ThinShell

/-- **Klartag's first thin-shell bound.** There are a real $C > 0$ and a natural number
$N \ge 3$ such that for every natural number $n \ge N$ the thin-shell width
$\sigma_n \in [0, \infty]$ of dimension $n$ satisfies $\sigma_n \le C \sqrt{n / \log n}$.

This is Klartag's first bound in the weaker form tabulated by the optimization catalogue.

Source: Klartag, Invent. Math. 168 (2007), 91--131; catalogue `constants/20a.md`. -/
public theorem_wanted klartag2007a_width_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      thinShellWidth n ≤ ENNReal.ofReal (C * Real.sqrt ((n : ℝ) / Real.log n))

/-- **Klartag's power-law thin-shell bound.** For every $\varepsilon > 0$ there are a constant
$C > 0$ and an integer $N \ge 3$ such that for every dimension $n \ge N$ the thin-shell width
$\sigma_n \in [0, \infty]$ satisfies $\sigma_n \le C n^{2/5 + \varepsilon}$. Here $\sigma_n$ is
the square root of the supremum of $\mathbb{E}\,(|X| - \sqrt{n})^2$ over isotropic log-concave
random vectors $X$ in $\mathbb{R}^n$.

Source: Klartag, J. Funct. Anal. 245 (2007), 284--310; catalogue `constants/20a.md`. -/
public theorem_wanted klartag2007b_width_bound :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      thinShellWidth n ≤ ENNReal.ofReal (C * Real.rpow (n : ℝ) (2 / 5 + ε))

/-- **Fleury's thin-shell bound.** There are a real $C > 0$ and a natural number $N \ge 3$ such
that for every natural number $n \ge N$ the thin-shell width $\sigma_n \in [0, \infty]$ of
dimension $n$ satisfies $\sigma_n \le C n^{3/8}$.

Source: Fleury, J. Funct. Anal. 259 (2010), 832--841; catalogue `constants/20a.md`. -/
public theorem_wanted fleury2010_width_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      thinShellWidth n ≤ ENNReal.ofReal (C * Real.rpow (n : ℝ) (3 / 8))

/-- **Guédon–Milman thin-shell bound.** There are a real $C > 0$ and a natural number $N \ge 3$
such that for every natural number $n \ge N$ the thin-shell width $\sigma_n \in [0, \infty]$ of
dimension $n$ satisfies $\sigma_n \le C n^{1/3}$.

Source: Guedon and Milman, GAFA 21 (2011), 1043--1068; catalogue `constants/20a.md`. -/
public theorem_wanted guedonMilman2011_width_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      thinShellWidth n ≤ ENNReal.ofReal (C * Real.rpow (n : ℝ) (1 / 3))

/-- **Lee–Vempala thin-shell bound.** There are a constant $C > 0$ and an integer $N \ge 3$
such that for every dimension $n \ge N$ the thin-shell width $\sigma_n \in [0, \infty]$ satisfies
$\sigma_n \le C n^{1/4}$. Here $\sigma_n$ is the square root of the supremum of
$\mathbb{E}\,(|X| - \sqrt{n})^2$ over isotropic log-concave random vectors $X$ in $\mathbb{R}^n$.

Source: Lee and Vempala, FOCS 2017, 998--1007; catalogue `constants/20a.md`. -/
public theorem_wanted leeVempala2017_width_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      thinShellWidth n ≤ ENNReal.ofReal (C * Real.rpow (n : ℝ) (1 / 4))

/-- **Chen's thin-shell bound.** For every real $\varepsilon > 0$ there is a natural number
$N \ge 3$ such that for every natural number $n \ge N$ the thin-shell width
$\sigma_n \in [0, \infty]$ of dimension $n$ satisfies
$\sigma_n \le \exp\big((\log n)^{1/2 + \varepsilon}\big)$.

There is no constant multiplier inside the exponential.

Source: Chen, GAFA 31 (2021), 34--61; catalogue `constants/20a.md`. -/
public theorem_wanted chen2021_width_bound :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      thinShellWidth n ≤
        ENNReal.ofReal (Real.exp (Real.rpow (Real.log n) (1 / 2 + ε)))

/-- **Klartag–Lehec polylogarithmic thin-shell bound.** There are a real $C > 0$ and a natural
number $N \ge 3$ such that for every natural number $n \ge N$ the thin-shell width
$\sigma_n \in [0, \infty]$ of dimension $n$ satisfies $\sigma_n \le C (\log n)^4$.

Source: Klartag and Lehec, GAFA 32 (2022), 1134--1159; catalogue `constants/20a.md`. -/
public theorem_wanted klartagLehec2022_width_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      thinShellWidth n ≤ ENNReal.ofReal (C * Real.rpow (Real.log n) 4)

/-- **Jambulapati–Lee–Vempala thin-shell bound.** Let
$\alpha = \big(1 + 7\sqrt{2} + \sqrt{53 - 4\sqrt{2}}\big)/8$. There are a real $C > 0$ and a
natural number $N \ge 3$ such that for every natural number $n \ge N$ the thin-shell width
$\sigma_n \in [0, \infty]$ of dimension $n$ satisfies $\sigma_n \le C (\log n)^{\alpha}$.

The exponent $\alpha$ is algebraic, not rational; the paper bounds it by $2.2226$. The paper
proves this bound for the square root of the normalized variance of the squared radius, which
bounds the thin-shell width from above.

Source: Jambulapati, Lee and Vempala, arXiv:2208.11644v1, Theorem 22. -/
public theorem_wanted jambulapatiLeeVempala2022_width_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      thinShellWidth n ≤ ENNReal.ofReal
        (C * Real.rpow (Real.log n)
          ((1 + 7 * Real.sqrt 2 + Real.sqrt (53 - 4 * Real.sqrt 2)) / 8))

/-- **Klartag's square-root-logarithmic thin-shell bound.** There are a constant $C > 0$ and an
integer $N \ge 3$ such that for every dimension $n \ge N$ the thin-shell width
$\sigma_n \in [0, \infty]$ satisfies $\sigma_n \le C \sqrt{\log n}$. Here $\sigma_n$ is the square
root of the supremum of $\mathbb{E}\,(|X| - \sqrt{n})^2$ over isotropic log-concave random
vectors $X$ in $\mathbb{R}^n$, and $\log$ is the natural logarithm.

Source: Klartag, Ars Inveniendi Analytica (2023), Paper 4; catalogue `constants/20a.md`. -/
public theorem_wanted klartag2023_width_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      thinShellWidth n ≤ ENNReal.ofReal (C * Real.sqrt (Real.log n))

/-- **Guan's thin-shell bound.** There are a real $C > 0$ and a natural number $N \ge 3$ such
that for every natural number $n \ge N$ the thin-shell width $\sigma_n \in [0, \infty]$ of
dimension $n$ satisfies $\sigma_n \le C \log \log n$.

Source: Guan, arXiv:2412.09075; catalogue `constants/20a.md`. -/
public theorem_wanted guan2024_width_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      thinShellWidth n ≤ ENNReal.ofReal (C * Real.log (Real.log n))

/-- **Klartag–Lehec thin-shell variance bound.** There is a real $C > 0$ such that for every
natural number $n \ge 1$ and every isotropic log-concave measure $\mu$ on $\mathbb{R}^n$, the
normalized radius variance $\frac{1}{n} \int (|x|^2 - n)^2 \, d\mu(x)$ is at most $C$.

Source: arXiv:2507.15495v1, Theorem 1.1. The constant is not optimized or made explicit. -/
public theorem_wanted klartagLehec2025_variance_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      ∀ μ : Measure (EuclideanSpace ℝ (Fin n)), IsIsotropicLogConcave μ →
        normalizedRadiusVariance μ ≤ ENNReal.ofReal C

/-- **Klartag–Lehec bounded thin-shell width.** There is a real $C > 0$ such that for every
natural number $n \ge 1$ the thin-shell width $\sigma_n \in [0, \infty]$ of dimension $n$
satisfies $\sigma_n \le C$.

Source: Klartag and Lehec, arXiv:2507.15495v1, Introduction and Theorem 1.1. -/
public theorem_wanted klartagLehec2025_width_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → thinShellWidth n ≤ ENNReal.ofReal C

/-- **The thin-shell variance constant is finite.** The thin-shell variance constant, the
supremum in $[0, \infty]$ of the normalized radius variances
$\frac{1}{n} \int (|x|^2 - n)^2 \, d\mu(x)$ over all dimensions $n \ge 1$ and all isotropic
log-concave probability measures $\mu$ on $\mathbb{R}^n$, is finite.

Source: Klartag and Lehec, arXiv:2507.15495v1, Theorem 1.1. -/
public theorem_wanted thinShellVarianceConstant_lt_top :
    thinShellVarianceConstant < ⊤

/-- **The standard Gaussian has normalized radius variance 2.** For every dimension $n \ge 1$,
the standard Gaussian measure $\gamma_n$ on $\mathbb{R}^n$ is isotropic log-concave (a probability
measure with a log-concave Lebesgue density, mean $0$ and identity covariance), and its normalized
radius variance $\frac{1}{n} \int (|x|^2 - n)^2 \, d\gamma_n(x)$ equals $2$.

Source: Klartag--Lehec, arXiv:2507.15495v1, Introduction. -/
public theorem_wanted stdGaussian_isotropic_variance (n : ℕ) (hn : 0 < n) :
    IsIsotropicLogConcave (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
      normalizedRadiusVariance
        (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))) = 2

/-- **The isotropic cube has normalized radius variance 4/5.** For every dimension $n \ge 1$, let
$\mu$ be the uniform probability measure on the cube $[-\sqrt{3}, \sqrt{3}]^n \subset \mathbb{R}^n$
(Lebesgue measure restricted to the cube and divided by its volume). Then $\mu$ is isotropic
log-concave (a probability measure with a log-concave Lebesgue density, mean $0$ and identity
covariance), and its normalized radius variance $\frac{1}{n} \int (|x|^2 - n)^2 \, d\mu(x)$
equals $4/5$.

The cube is scaled to covariance identity, so this is the unit-variance convention.
Source: Klartag--Lehec, arXiv:2507.15495v1, Introduction. -/
public theorem_wanted uniformCube_isotropic_variance (n : ℕ) (hn : 0 < n) :
    let μ := ProbabilityTheory.cond
      (volume : Measure (EuclideanSpace ℝ (Fin n)))
      {x | ∀ i : Fin n, |x i| ≤ Real.sqrt 3}
    IsIsotropicLogConcave μ ∧ normalizedRadiusVariance μ = ENNReal.ofReal (4 / 5)

/-- **Cube lower bound for the thin-shell variance constant.** The thin-shell variance constant,
an element of $[0, \infty]$, is at least $4/5$.

The value $4/5$ is the exact normalized radius variance of the uniform law on a cube scaled to
identity covariance.

Source: Klartag and Lehec, arXiv:2507.15495v1, Introduction. -/
public theorem_wanted fourFifths_le_thinShellVarianceConstant :
    ENNReal.ofReal (4 / 5) ≤ thinShellVarianceConstant

/-- **The thin-shell variance constant is at least 2.** The thin-shell variance constant, the
supremum in $[0, \infty]$ of the normalized radius variances
$\frac{1}{n} \int (|x|^2 - n)^2 \, d\mu(x)$ over all dimensions $n \ge 1$ and all isotropic
log-concave probability measures $\mu$ on $\mathbb{R}^n$, is at least $2$.

The lower bound comes from the standard Gaussian, whose normalized radius variance is $2$ in
every dimension.

Source: Klartag and Lehec, arXiv:2507.15495v1, Introduction. -/
public theorem_wanted two_le_thinShellVarianceConstant :
    2 ≤ thinShellVarianceConstant

end MathlibExt.Probability.ThinShell
