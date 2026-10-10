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

/-- Klartag's first bound, in the weaker form tabulated by the optimization catalogue.

Source: Klartag, Invent. Math. 168 (2007), 91--131; catalogue `constants/20a.md`. -/
public theorem_wanted klartag2007a_width_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      thinShellWidth n ≤ ENNReal.ofReal (C * Real.sqrt ((n : ℝ) / Real.log n))

/-- The power-law bound with its vanishing exponent expressed by every positive epsilon.

Source: Klartag, J. Funct. Anal. 245 (2007), 284--310; catalogue `constants/20a.md`. -/
public theorem_wanted klartag2007b_width_bound :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      thinShellWidth n ≤ ENNReal.ofReal (C * Real.rpow (n : ℝ) (2 / 5 + ε))

/-- Fleury's thin-shell exponent `3/8`.

Source: Fleury, J. Funct. Anal. 259 (2010), 832--841; catalogue `constants/20a.md`. -/
public theorem_wanted fleury2010_width_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      thinShellWidth n ≤ ENNReal.ofReal (C * Real.rpow (n : ℝ) (3 / 8))

/-- Guedon--Milman's thin-shell exponent `1/3`.

Source: Guedon and Milman, GAFA 21 (2011), 1043--1068; catalogue `constants/20a.md`. -/
public theorem_wanted guedonMilman2011_width_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      thinShellWidth n ≤ ENNReal.ofReal (C * Real.rpow (n : ℝ) (1 / 3))

/-- Lee--Vempala's thin-shell exponent `1/4`.

Source: Lee and Vempala, FOCS 2017, 998--1007; catalogue `constants/20a.md`. -/
public theorem_wanted leeVempala2017_width_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      thinShellWidth n ≤ ENNReal.ofReal (C * Real.rpow (n : ℝ) (1 / 4))

/-- Chen's subpolynomial bound, with no hidden multiplier inside the exponential.

Source: Chen, GAFA 31 (2021), 34--61; catalogue `constants/20a.md`. -/
public theorem_wanted chen2021_width_bound :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      thinShellWidth n ≤
        ENNReal.ofReal (Real.exp (Real.rpow (Real.log n) (1 / 2 + ε)))

/-- Klartag--Lehec's polylogarithmic exponent `4`.

Source: Klartag and Lehec, GAFA 32 (2022), 1134--1159; catalogue `constants/20a.md`. -/
public theorem_wanted klartagLehec2022_width_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      thinShellWidth n ≤ ENNReal.ofReal (C * Real.rpow (Real.log n) 4)

/-- The exact Jambulapati--Lee--Vempala exponent from arXiv:2208.11644v1, Theorem 22.

The catalogue's `2.23...` is not an exact rational. The primary paper gives the
algebraic exponent below and bounds it by `2.2226`. Its normalized squared-radius
width bounds this radius width by the proved radius-to-variance inequality.
Source: Jambulapati, Lee and Vempala, arXiv:2208.11644v1, Theorem 22. -/
public theorem_wanted jambulapatiLeeVempala2022_width_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      thinShellWidth n ≤ ENNReal.ofReal
        (C * Real.rpow (Real.log n)
          ((1 + 7 * Real.sqrt 2 + Real.sqrt (53 - 4 * Real.sqrt 2)) / 8))

/-- Klartag's square-root-logarithmic thin-shell bound.

Source: Klartag, Ars Inveniendi Analytica (2023), Paper 4; catalogue `constants/20a.md`. -/
public theorem_wanted klartag2023_width_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      thinShellWidth n ≤ ENNReal.ofReal (C * Real.sqrt (Real.log n))

/-- Guan's double-logarithmic thin-shell bound.

Source: Guan, arXiv:2412.09075; catalogue `constants/20a.md`. -/
public theorem_wanted guan2024_width_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      thinShellWidth n ≤ ENNReal.ofReal (C * Real.log (Real.log n))

/-- Klartag--Lehec's affirmative resolution: a finite universal variance bound.

Source: arXiv:2507.15495v1, Theorem 1.1. The constant is not optimized or made explicit. -/
public theorem_wanted klartagLehec2025_variance_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      ∀ μ : Measure (EuclideanSpace ℝ (Fin n)), IsIsotropicLogConcave μ →
        normalizedRadiusVariance μ ≤ ENNReal.ofReal C

/-- The dimension-independent constant-width consequence of the 2025 variance bound.

Source: Klartag and Lehec, arXiv:2507.15495v1, Introduction and Theorem 1.1. -/
public theorem_wanted klartagLehec2025_width_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → thinShellWidth n ≤ ENNReal.ofReal C

/-- The variance constant is finite, rather than an unresolved boundedness conjecture.

Source: Klartag and Lehec, arXiv:2507.15495v1, Theorem 1.1. -/
public theorem_wanted thinShellVarianceConstant_lt_top :
    thinShellVarianceConstant < ⊤

/-- The actual standard Gaussian witnesses normalized squared-radius variance `2`.

Source: Klartag--Lehec, arXiv:2507.15495v1, Introduction. -/
public theorem_wanted stdGaussian_isotropic_variance (n : ℕ) (hn : 0 < n) :
    IsIsotropicLogConcave (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
      normalizedRadiusVariance
        (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin n))) = 2

/-- The actual normalized Lebesgue law on `[-sqrt(3),sqrt(3)]^n` witnesses variance `4/5`.

The cube is scaled to covariance identity, so this is the unit-variance convention.
Source: Klartag--Lehec, arXiv:2507.15495v1, Introduction. -/
public theorem_wanted uniformCube_isotropic_variance (n : ℕ) (hn : 0 < n) :
    let μ := ProbabilityTheory.cond
      (volume : Measure (EuclideanSpace ℝ (Fin n)))
      {x | ∀ i : Fin n, |x i| ≤ Real.sqrt 3}
    IsIsotropicLogConcave μ ∧ normalizedRadiusVariance μ = ENNReal.ofReal (4 / 5)

/-- The cube's exact lower bound for the universal variance constant.

Source: Klartag and Lehec, arXiv:2507.15495v1, Introduction. -/
public theorem_wanted fourFifths_le_thinShellVarianceConstant :
    ENNReal.ofReal (4 / 5) ≤ thinShellVarianceConstant

/-- The Gaussian's exact lower bound for the universal variance constant.

Source: Klartag and Lehec, arXiv:2507.15495v1, Introduction. -/
public theorem_wanted two_le_thinShellVarianceConstant :
    2 ≤ thinShellVarianceConstant

end MathlibExt.Probability.ThinShell
