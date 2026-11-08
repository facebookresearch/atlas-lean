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

/-- The first polynomial bound, with one multiplier for every sufficiently large dimension.

Source: Kannan, Lovasz and Simonovits, DCG 13 (1995), 541--560;
optimizationproblems `constants/20c.md`, KLS1995 row. -/
public theorem_wanted kannanLovaszSimonovits1995_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      dimensionalKlsConstant n ≤ ENNReal.ofReal (C * Real.sqrt n)

/-- Lee--Vempala's exponent `1/4`, first published in FOCS 2017.

Source: Lee and Vempala, Ann. of Math. 199 (2024), 1--104;
optimizationproblems `constants/20c.md`, LV2024 row. -/
public theorem_wanted leeVempala2024_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      dimensionalKlsConstant n ≤ ENNReal.ofReal (C * Real.rpow (n : ℝ) (1 / 4))

/-- The catalogue's weaker form of Chen's subpolynomial estimate.

Source: Chen, GAFA 31 (2021), 34--61; optimizationproblems `constants/20c.md`.
Jambulapati--Lee--Vempala v1 quotes the stronger exponent `sqrt(log n * log(log n))`. -/
public theorem_wanted chen2021_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      dimensionalKlsConstant n ≤
        ENNReal.ofReal (Real.exp (C * Real.sqrt (Real.log n) * Real.log (Real.log n)))

/-- The first polylogarithmic KLS bound.

Source: Klartag and Lehec, GAFA 32 (2022), 1134--1159;
optimizationproblems `constants/20c.md`, KL2022 row. -/
public theorem_wanted klartagLehec2022_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      dimensionalKlsConstant n ≤ ENNReal.ofReal (C * Real.rpow (Real.log n) 5)

/-- The exact algebraic Jambulapati--Lee--Vempala exponent, not a rounded decimal.

Source: arXiv:2208.11644v1, Theorem 22 and the preceding KLS/thin-shell comparison. -/
public theorem_wanted jambulapatiLeeVempala2022_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      dimensionalKlsConstant n ≤ ENNReal.ofReal
        (C * Real.rpow (Real.log n)
          (1 + (1 + 7 * Real.sqrt 2 + Real.sqrt (53 - 4 * Real.sqrt 2)) / 8))

/-- An explicitly weaker specialization of Lehec's reported `3.082...` estimate.

The primary gives only decimal-prefix precision; `3.083` is not claimed to be
its exact exponent, and this request does not exhaust that historical row.
Source: Klartag, arXiv:2303.14938v1, Introduction, personal-communication paragraph. -/
public theorem_wanted lehec_reported_bound_weaker_specialization :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      dimensionalKlsConstant n ≤ ENNReal.ofReal (C * Real.rpow (Real.log n) (3083 / 1000))

/-- The square-root-logarithmic estimate in every dimension at least two.

Source: Klartag, arXiv:2303.14938v1, Theorem 1.2. -/
public theorem_wanted klartag2023_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      dimensionalKlsConstant n ≤ ENNReal.ofReal (C * Real.sqrt (Real.log n))

/-- The standard Gaussian has the exact inverse Cheeger coefficient `sqrt(pi/2)`.

Source: optimizationproblems `constants/20c.md`, classical Gaussian row;
the Gaussian isoperimetric theorem supplies the minimizing half-space claim. -/
public theorem_wanted stdGaussian_inverseCheeger (n : ℕ) (hn : 0 < n) :
    inverseCheegerConstant
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))) =
        ENNReal.ofReal (Real.sqrt (Real.pi / 2))

/-- The actual Gaussian law gives the exact lower bound for the global constant.

Source: optimizationproblems `constants/20c.md`, classical Gaussian lower-bound row. -/
public theorem_wanted sqrtPiDivTwo_le_klsConstant :
    ENNReal.ofReal (Real.sqrt (Real.pi / 2)) ≤ klsConstant

/-- The catalogue's precise Poincare/Cheeger comparison, whose lower coefficient
requires a separate source check rather than replacement by a convenient number.

Source: optimizationproblems `constants/20c.md`, Poincare comparison display.
Klartag arXiv:2303.14938v1 states the weaker lower coefficient `1/9`, not `1/pi`. -/
public theorem_wanted catalogue_poincare_lower_bound {n : ℕ} (hn : 0 < n)
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hμ : IsIsotropicLogConcave μ) :
    ENNReal.ofReal (1 / Real.pi) * inverseCheegerConstant μ ^ 2 ≤
      smoothPoincareConstant μ

/-- The lower comparison coefficient explicitly present in the retained primary.

Source: Klartag, arXiv:2303.14938v1, equation comparing `psi` and `C_P`.
The locally Lipschitz-to-smooth approximation remains part of the requested proof. -/
public theorem_wanted klartag2023_poincare_lower_bound {n : ℕ} (hn : 0 < n)
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hμ : IsIsotropicLogConcave μ) :
    ENNReal.ofReal (1 / 9) * inverseCheegerConstant μ ^ 2 ≤
      smoothPoincareConstant μ

/-- The upper Poincare comparison shared by the catalogue and retained primary.

Source: optimizationproblems `constants/20c.md`, comparison display, and
Klartag, arXiv:2303.14938v1, Introduction. -/
public theorem_wanted poincare_cheeger_upper_bound {n : ℕ} (hn : 0 < n)
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hμ : IsIsotropicLogConcave μ) :
    smoothPoincareConstant μ ≤ 4 * inverseCheegerConstant μ ^ 2

/-- A specified model-to-model logarithmic comparison with the actual thin-shell
variance constant. No numerical thin-shell parameter is supplied by the caller.

Source: Jambulapati--Lee--Vempala, arXiv:2208.11644v1, KLS/thin-shell comparison. -/
public theorem_wanted kls_le_thinShell_variance_log_squared :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
      dimensionalKlsConstant n ^ 2 ≤
        ENNReal.ofReal (C * Real.log n ^ 2) * thinShellVarianceConstant

end MathlibExt.Probability.KLS
